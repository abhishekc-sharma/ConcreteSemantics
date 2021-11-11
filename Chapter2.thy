theory Chapter2
  imports Main
begin

(* Exercise 2.1 *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* Exercise 2.2 *)

datatype mynat = Z | S mynat

fun add :: "mynat \<Rightarrow> mynat \<Rightarrow> mynat" where
"add Z m = m" |
"add (S n) m = S (add n m)"

theorem add_assoc [simp]: "add (add x y) z = add x (add y z)"
  apply(induction x)
  apply(auto)
done

lemma add_Zright [simp]: "add x Z = x"
  apply(induction x)
  apply(auto)
done

lemma add_Sright [simp]: "add x (S y) = S (add x y)"
  apply(induction x)
  apply(auto)
done

theorem add_comm [simp]: "add x y = add y x"
  apply(induction x)
  apply(auto)
done

fun double :: "mynat \<Rightarrow> mynat" where
"double Z = Z" |
"double (S n) = S ( S ( double n))"

theorem double_m_eq_add_m_m: "double m = add m m"
  apply(induction m)
  apply(auto)
done

(* Exercise 2.3 *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count n [] = 0" |
"count n (x#xs) = (if n = x then 1 else 0) + (count n xs)"

theorem count_lte_length: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
done

(* Exercise 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] e = [e]" |
"snoc (x#xs) e = x#(snoc xs e)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x#xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]: "reverse (snoc xs x) = x#(reverse xs)"
  apply(induction xs)
  apply(auto)
done

theorem reverse_reverse [simp]: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
done

(* Exercise 2.5 *)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = (Suc n) + (sum_upto n)"

theorem sum_upto_n [simp]: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
  apply(auto)
done

(* Exercise 2.6 *)

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l a r) = (contents l)@[a]@(contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l a r) = (sum_tree l) + a + (sum_tree r)"

theorem sum_tree_eq_sum_list_contents : "sum_tree t = sum_list (contents t)"
  apply(induction t)
  apply(auto)
done

(* Exercise 2.7 *)

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l a r) = a#(pre_order l)@(pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l a r) = (post_order l)@(post_order r)@[a]"

theorem pre_order_mirror_eq_rev_post_order : "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
done

(* Exercise 2.8 *)

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse _ [] = []" |
"intersperse _ [x] = [x]" |
"intersperse a (x#xs) = a#x#xs"

theorem map_f_intersperse_eq_intersperse_map_f : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
done

(* Exercise 2.9 *)

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem itadd_eq_add : "itadd m n = m + n"
  apply(induction m arbitrary: n)
  apply(auto)
done

end