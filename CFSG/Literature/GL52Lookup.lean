module

public import CFSG.Literature.GL52Chain
public import CFSG.Sporadic.Schreier.ClassSpec
public meta import CFSG.Literature.GL52Chain
public meta import CFSG.Sporadic.Schreier.ClassSpec

public section

namespace CFSG.Literature.GL52

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

@[expose] def tbl (g : G) : Table := toTable (glPerm g)

theorem rep_tbl (g : G) : Rep 31 (tbl g) g := rep_toTable (by norm_num) (glPerm g)

theorem eq_of_rep_tblEq {T T' : Table} {g h : G} (hg : Rep 31 T g) (hh : Rep 31 T' h)
    (he : tblEq 31 T T' = true) : g = h := by
  apply glPerm_injective
  refine Equiv.ext fun i => Fin.ext ?_
  have h1 := hg i.val i.isLt
  have h2 := hh i.val i.isLt
  have h3 := (tblEq_iff.1 he) i.val i.isLt
  rw [idx_of_lt _ i.isLt] at h1 h2
  rw [h1, h2] at h3
  exact h3

@[expose] def letterG (gs : List G) (l : ℤ) : G :=
  if 0 < l then gs.getD (l.toNat - 1) 1 else (gs.getD ((-l).toNat - 1) 1)⁻¹

@[expose] def genTables (gs : List G) : List Table := gs.map tbl

@[expose] def genInvTables (gs : List G) : List Table := gs.map fun g => tbl g⁻¹

@[expose] def letterT (tb tbi : List Table) (l : ℤ) : Table :=
  if 0 < l then tb.getD (l.toNat - 1) (idT 31) else tbi.getD ((-l).toNat - 1) (idT 31)

theorem getD_genTables (gs : List G) (k : ℕ) :
    Rep 31 ((genTables gs).getD k (idT 31)) (gs.getD k 1) := by
  by_cases hk : k < gs.length
  · rw [genTables, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
    exact rep_tbl _
  · rw [List.getD_eq_default _ _ (by simp [genTables]; omega),
      List.getD_eq_default _ _ (by omega)]
    exact Rep.idT (by norm_num)

theorem getD_genInvTables (gs : List G) (k : ℕ) :
    Rep 31 ((genInvTables gs).getD k (idT 31)) (gs.getD k 1)⁻¹ := by
  by_cases hk : k < gs.length
  · rw [genInvTables, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
      List.getD_eq_getElem _ _ hk]
    exact rep_tbl _
  · rw [List.getD_eq_default _ _ (by simp [genInvTables]; omega),
      List.getD_eq_default _ _ (by omega), inv_one]
    exact Rep.idT (by norm_num)

theorem rep_letterT (gs : List G) (l : ℤ) :
    Rep 31 (letterT (genTables gs) (genInvTables gs) l) (letterG gs l) := by
  unfold letterT letterG
  split_ifs
  · exact getD_genTables gs _
  · exact getD_genInvTables gs _

theorem rep_wordTable (gs : List G) (w : List ℤ) :
    Rep 31 (wordT 31 (letterT (genTables gs) (genInvTables gs)) w) (wordG (letterG gs) w) :=
  Rep.wordT (by norm_num) w fun l _ => rep_letterT gs l

theorem wordG_mem {gs : List G} {H : Subgroup G} (hgs : ∀ g ∈ gs, g ∈ H) (w : List ℤ) :
    wordG (letterG gs) w ∈ H := by
  have hl : ∀ l : ℤ, letterG gs l ∈ H := by
    intro l
    have hget : ∀ k, gs.getD k 1 ∈ H := by
      intro k
      by_cases hk : k < gs.length
      · rw [List.getD_eq_getElem _ _ hk]
        exact hgs _ (List.getElem_mem hk)
      · rw [List.getD_eq_default _ _ (by omega)]
        exact H.one_mem
    unfold letterG
    split_ifs
    · exact hget _
    · exact H.inv_mem (hget _)
  unfold wordG
  induction w with
  | nil => exact H.one_mem
  | cons l w ih => rw [List.map_cons, List.prod_cons]; exact H.mul_mem (hl l) ih

section Lookup

variable {Q : Type*} {K : Type} [DecidableEq K]

@[expose] def lkWord (key : Q → K) (L : List (K × List ℤ)) (q : Q) : List ℤ :=
  (L.lookup (key q)).getD []

@[expose] def lkFun (gs : List G) (key : Q → K) (L : List (K × List ℤ)) (q : Q) : G :=
  wordG (letterG gs) (lkWord key L q)

@[expose] def lkTable (gs : List G) (key : Q → K) (L : List (K × List ℤ)) (q : Q) : Table :=
  wordT 31 (letterT (genTables gs) (genInvTables gs)) (lkWord key L q)

theorem rep_lkTable (gs : List G) (key : Q → K) (L : List (K × List ℤ)) (q : Q) :
    Rep 31 (lkTable gs key L q) (lkFun gs key L q) :=
  rep_wordTable gs _

variable [Group Q]

abbrev lkMulOK (gs : List G) (key : Q → K) (L : List (K × List ℤ)) : Prop :=
  ∀ q r : Q, tblEq 31 (lkTable gs key L (q * r))
    (compT 31 (lkTable gs key L q) (lkTable gs key L r)) = true

abbrev lkInjOK (gs : List G) (key : Q → K) (L : List (K × List ℤ)) : Prop :=
  ∀ q : Q, tblEq 31 (lkTable gs key L q) (idT 31) = true → q = 1

@[expose] def lkHom (gs : List G) (key : Q → K) (L : List (K × List ℤ))
    (h : lkMulOK gs key L) : Q →* G :=
  MonoidHom.mk' (lkFun gs key L) fun q r =>
    eq_of_rep_tblEq (rep_lkTable gs key L (q * r))
      (Rep.compT (rep_lkTable gs key L q) (rep_lkTable gs key L r)) (h q r)

theorem lkHom_apply (gs : List G) (key : Q → K) (L : List (K × List ℤ))
    (h : lkMulOK gs key L) (q : Q) : lkHom gs key L h q = lkFun gs key L q :=
  congrFun (MonoidHom.mk'_apply _ _) q

theorem lkHom_injective (gs : List G) (key : Q → K) (L : List (K × List ℤ))
    (h : lkMulOK gs key L) (hi : lkInjOK gs key L) : Function.Injective (lkHom gs key L h) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  apply hi q
  have hrep := rep_lkTable gs key L q
  rw [← lkHom_apply gs key L h, hq] at hrep
  rw [tblEq_iff]
  intro i hi'
  rw [hrep i hi', (Rep.idT (G := G) (by norm_num) : Rep 31 (idT 31) (1 : G)) i hi']

theorem lkHom_range_le (gs : List G) (key : Q → K) (L : List (K × List ℤ))
    (h : lkMulOK gs key L) {H : Subgroup G} (hgs : ∀ g ∈ gs, g ∈ H) :
    (lkHom gs key L h).range ≤ H := by
  rintro _ ⟨q, rfl⟩
  rw [lkHom_apply]
  exact wordG_mem hgs _

end Lookup

end CFSG.Literature.GL52
