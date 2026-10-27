module

public import CFSG.Literature.GL52BFS
public import CFSG.Literature.GL52Pass
public import CFSG.Literature.GL52Elements
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public meta import CFSG.Literature.GL52BFS
public meta import CFSG.Literature.GL52Pass
public meta import CFSG.Literature.GL52Elements
public meta import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Literature.GL52

open Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

@[expose] def glActFun (M : GL (Fin 3) (ZMod 2)) :
    MulAut (Multiplicative (Fin 3 → ZMod 2)) where
  toFun v := Multiplicative.ofAdd ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.toAdd)
  invFun v := Multiplicative.ofAdd
    (((M⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v.toAdd)
  left_inv v := by
    simp only [toAdd_ofAdd, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec, ofAdd_toAdd]
  right_inv v := by
    simp only [toAdd_ofAdd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec, ofAdd_toAdd]
  map_mul' v w := by
    simp only [toAdd_mul, mulVec_add, ofAdd_add]

@[expose] def glAct : GL (Fin 3) (ZMod 2) →* MulAut (Multiplicative (Fin 3 → ZMod 2)) where
  toFun := glActFun
  map_one' := by
    ext v
    simp [glActFun]
  map_mul' M N := by
    ext v
    simp [glActFun, mulVec_mulVec]

@[expose] def keyPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : List ℕ :=
  (List.finRange n).map fun i => (σ i : ℕ)

@[expose] def keyA5 (σ : alternatingGroup (Fin 5)) : List ℕ := keyPerm (σ : Equiv.Perm (Fin 5))

@[expose] def keyGL3 (M : GL (Fin 3) (ZMod 2)) : List ℕ :=
  (List.finRange 3).flatMap fun i => (List.finRange 3).map fun j =>
    ((M : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j).val

@[expose] def keyD8 : DihedralGroup 4 → List ℕ
  | .r i => [0, i.val]
  | .sr i => [1, i.val]

@[expose] def keyVec {n p : ℕ} (v : Multiplicative (Fin n → ZMod p)) : List ℕ :=
  (List.finRange n).map fun i => (v.toAdd i).val

@[expose] def decLetter (d : ℕ) : ℤ :=
  if d = 1 then 1 else if d = 2 then 2 else if d = 3 then -1 else -2

@[expose] def decKey : ℕ → ℕ → List ℕ × ℕ
  | 0, n => ([], n)
  | k + 1, n => (n % 8 :: (decKey k (n / 8)).1, (decKey k (n / 8)).2)

@[expose] def decWord : ℕ → ℕ → List ℤ
  | 0, _ => []
  | f + 1, n => if n % 8 = 0 then [] else decLetter (n % 8) :: decWord f (n / 8)

@[expose] def decEntry (k n : ℕ) : List ℕ × List ℤ := ((decKey k n).1, decWord 64 (decKey k n).2)

@[expose] def tblA5 : List (List ℕ × List ℤ) := List.map (decEntry 5) [
    18056, 1680419016, 4853380360, 305281104, 2357543632, 562960, 4467344472, 69802136, 170959640,
    403040, 75838112, 150882260192, 47233, 606684353, 13443311361, 2442184209, 67793, 1631990033,
    3188761, 38158489, 18860279065, 1367684129, 558401185, 21373153, 1379026498, 4465924290,
    2667266, 11032115210, 344266, 558237450, 203997722, 19537397850, 594202, 18811852322, 25505890,
    4752098, 2351474755, 36848259, 36738307, 1098763, 172361867, 35727417611, 69769235,
    285910024275, 2687763, 1188387, 26248291, 156299235491, 144452, 210048644, 38827074244,
    293938700, 294695052, 4588748, 35738759700, 8717908, 21532884, 3281948, 9478236, 1250393883292]

@[expose] def tblS3 : List (List ℕ × List ℤ) :=
  [([0, 1, 2], []), ([0, 2, 1], [2]), ([1, 0, 2], [1]), ([1, 2, 0], [1, 2]),
    ([2, 0, 1], [2, 1]), ([2, 1, 0], [1, 2, 1])]

@[expose] def tblGL3 : List (List ℕ × List ℤ) := List.map (decEntry 9) [
    1464036103509250112, 59475971887337536, 183073782408417344, 22875566262980672,
    5424117688078400, 43462193974644800, 920518062805056, 7433396957777984, 404750912, 10890510912,
    357565961863744, 14518350774848, 608727998693952, 9511626637888, 471305258071786048,
    5423980267995712, 2552238656, 148329468480, 4861165587141184, 84887092859456, 45778045276736,
    715533619776, 471234906236949056, 920380638532160, 134512648, 76090999865352, 2284093448,
    5722257784840, 678014677717000, 347697551946059784, 115064726392840, 59467175796445192,
    311114598918914568, 23447174870204936, 38958594347237896, 4861167753495048, 58904361132130824,
    929312024855048, 28320236040, 1797580423688, 22884222767206920, 311677551021920776,
    357568124031496, 2929797330375176, 183004530101752328, 357430686945800, 10593671352840,
    165761290760, 1342472264, 9511356366920, 18524438600, 715265441864, 183004512905334856,
    7434496467275848, 475807757919064136, 2859445766066248, 43392941653230152, 84751786443336,
    608745461908040, 38959693575750216, 5432774211174984, 22884360191509064, 698335134280,
    44678550684232, 7364144634270280, 14383042269768, 2930896554693192, 45795510587976,
    929174583808584, 475737406354526792, 14520496198216, 9494430257736, 2488916791353442305,
    43392941923794945, 5432776344240129, 58904363281973249, 16781313, 678014427860993, 28068548609,
    1324211245057, 11156885505, 22875564098490369, 698083479553, 366362054922241, 4869824243073537,
    76093149184513, 187577382035816961, 677997516718593, 2860527827030529, 38959693860704769,
    44695996862977, 23438378777448961, 116146804134401, 38889342011216385, 1815043412481,
    75955693720065, 471234889058910273, 43462193708040257, 679097011568705, 7363045393465409,
    366226777837633, 183074881668124737, 38958594062028865, 2860545260916801, 1188917448769,
    7434496183930945, 608745176731713, 75953563013185, 3491758657, 87260398145, 44695713743425,
    1814777037377, 58913157225124417, 1797848568385, 23447172704113217, 115047294833217,
    43391842141639233, 44678818861633, 84749637161537, 1326341984833, 183073782139748361,
    7364144904830985, 929176714772489, 471305257818030089, 285216777, 115064474439689,
    224697520137, 165509599241, 148595838985, 59475969724944393, 4869961680195593, 9494178598921,
    38889324845990409, 2930896841736713, 187577381782028809, 607645952377353, 679096757551625,
    2860544992248329, 5586947441161, 10611138527753, 366224615707145, 5724405010953,
    187507030200979977, 115047561204233, 183004530355503177, 7433396689076297, 116147056050249,
    43391842410332233, 45778328358985, 475737406639706185, 38889342277783625, 2929797045162057,
    89405821001, 2859445480624201, 5584816738377, 45795225407561, 347143533376832073,
    10593941586505, 677997246153289, 311677548857918025, 7363045122671177, 116163986096713,
    226828255817, 14380895076937, 20671631945, 1186772030025, 607645665071689, 10610867966537]

@[expose] def tblD8 : List (List ℕ × List ℤ) :=
  [([0, 0], []), ([0, 1], [1]), ([0, 2], [1, 1]), ([0, 3], [1, 1, 1]), ([1, 0], [2]),
    ([1, 1], [2, 1]), ([1, 2], [2, 1, 1]), ([1, 3], [2, 1, 1, 1])]

@[expose] def tblE16 : List (List ℕ × List ℤ) :=
  [([0, 0, 0, 0], []), ([0, 0, 0, 1], [4]), ([0, 0, 1, 0], [3]), ([0, 0, 1, 1], [3, 4]),
    ([0, 1, 0, 0], [2]), ([0, 1, 0, 1], [2, 4]), ([0, 1, 1, 0], [2, 3]),
    ([0, 1, 1, 1], [2, 3, 4]), ([1, 0, 0, 0], [1]), ([1, 0, 0, 1], [1, 4]),
    ([1, 0, 1, 0], [1, 3]), ([1, 0, 1, 1], [1, 3, 4]), ([1, 1, 0, 0], [1, 2]),
    ([1, 1, 0, 1], [1, 2, 4]), ([1, 1, 1, 0], [1, 2, 3]), ([1, 1, 1, 1], [1, 2, 3, 4])]

@[expose] def tblR9 : List (List ℕ × List ℤ) :=
  [([0, 0], []), ([0, 1], [2]), ([0, 2], [2, 2]), ([1, 0], [1]), ([1, 1], [1, 2]),
    ([1, 2], [1, 2, 2]), ([2, 0], [1, 1]), ([2, 1], [1, 1, 2]), ([2, 2], [1, 1, 2, 2])]

@[expose] def tblE8 : List (List ℕ × List ℤ) :=
  [([0, 0, 0], []), ([0, 0, 1], [3]), ([0, 1, 0], [2]), ([0, 1, 1], [2, 3]), ([1, 0, 0], [1]),
    ([1, 0, 1], [1, 3]), ([1, 1, 0], [1, 2]), ([1, 1, 1], [1, 2, 3])]

@[expose] def matOfKey (k : List ℕ) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun i j => ((k.getD (3 * i.val + j.val) 0 : ℕ) : ZMod 2)

@[expose] def matEq3 (A B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j => decide (A i j = B i j)

theorem eq_of_matEq3 {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : matEq3 A B = true) : A = B := by
  ext i j
  simp only [matEq3, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies] at h
  exact h i j

@[expose] def mkUnit3 (k k' : List ℕ) : Option (GL (Fin 3) (ZMod 2)) :=
  if h : matEq3 (matOfKey k * matOfKey k') 1 = true ∧
      matEq3 (matOfKey k' * matOfKey k) 1 = true then
    some (Units.mk (matOfKey k) (matOfKey k') (eq_of_matEq3 h.1) (eq_of_matEq3 h.2))
  else none

@[expose] def gl3Elems : List (GL (Fin 3) (ZMod 2)) :=
  tblGL3.filterMap fun e => tblGL3.findSome? fun e' => mkUnit3 e.1 e'.1

theorem mem_gl3Elems_of (h : (gl3Elems.map keyGL3).Nodup ∧ gl3Elems.length = 168)
    (M : GL (Fin 3) (ZMod 2)) : M ∈ gl3Elems := by
  classical
  have hnd : gl3Elems.Nodup := h.1.of_map _
  have h1 : gl3Elems.toFinset.card = 168 := by
    rw [List.toFinset_card_of_nodup hnd, h.2]
  have h2 : gl3Elems.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [h1, ← Nat.card_eq_fintype_card,
      CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two])
  have := Finset.mem_univ M
  rw [← h2] at this
  exact List.mem_toFinset.1 this

@[expose] def gensK1 : List G := [glK1b, glK1c]

@[expose] def gensK2 : List G := [glK2a, glK2b]

@[expose] def gensX : List G := [glX1, glX2]

@[expose] def gensD : List G := [glDx, glDy]

@[expose] def gensE : List G := [glE1, glE2, glE3, glT0]

@[expose] def gensT1 : List G := [glF1a, glF1b, glF1c]

@[expose] def gensT2 : List G := [glF2a, glF2b]

@[expose] def lkTableT {Q : Type*} {K : Type} [DecidableEq K] (tb tbi : List Table) (key : Q → K)
    (L : List (K × List ℤ)) (q : Q) : Table :=
  wordT 31 (letterT tb tbi) (lkWord key L q)

@[expose] def tbK1 : List Table := genTables gensK1

@[expose] def tbiK1 : List Table := genInvTables gensK1

@[expose] def tbK2 : List Table := genTables gensK2

@[expose] def tbiK2 : List Table := genInvTables gensK2

@[expose] def tbT2 : List Table := genTables gensT2

@[expose] def tbiT2 : List Table := genInvTables gensT2

@[expose] def t1Table (c : Multiplicative (Fin 3 → ZMod 2)) : Table :=
  lkTable gensT1 keyVec tblE8 c

@[expose] def t2Table (M : GL (Fin 3) (ZMod 2)) : Table := lkTableT tbT2 tbiT2 keyGL3 tblGL3 M

end CFSG.Literature.GL52
