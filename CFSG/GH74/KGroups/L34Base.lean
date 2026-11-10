
module

public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.FieldGF
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.L34Inputs
public meta import CFSG.GH74.KGroups.L34Inputs

@[expose] public section

namespace CFSG.GH74.KGroups.L34

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Blueprint Matrix

theorem QP21_closure : QP21.originalSubgroup = Subgroup.closure {pa, pb} := by
  rw [QP21, certificate_originalSubgroup]
  congr 1
  ext g
  simp

theorem QP_closure : QP.originalSubgroup = Subgroup.closure {PA, PB} := by
  rw [QP, certificate_originalSubgroup]
  congr 1
  ext g
  simp

def vecTab : List (List ℕ) :=
  [[0, 0, 1], [0, 1, 0], [0, 1, 1], [0, 1, 2], [0, 1, 3], [1, 0, 0], [1, 0, 1], [1, 0, 2], [1, 0, 3], [1, 1, 0], [1, 1, 1], [1, 1, 2], [1, 1, 3], [1, 2, 0], [1, 2, 1], [1, 2, 2], [1, 2, 3], [1, 3, 0], [1, 3, 1], [1, 3, 2], [1, 3, 3]]

def vec (i : Fin 21) : Fin 3 → GF4 :=
  fun j => GF4.ofNat' ((vecTab.getD i.val [0, 0, 0]).getD j.val 0)

theorem vec_ne : ∀ i, vec i ≠ 0 := by decide +kernel

theorem vec_inj : ∀ i j (c : GF4), c • vec j = vec i → i = j := by decide +kernel

theorem vec_surj : ∀ v : Fin 3 → GF4, v ≠ 0 → ∃ i, ∃ c : GF4, c • v = vec i := by
  decide +kernel

def mA : Matrix.SpecialLinearGroup (Fin 3) GF4 :=
  ⟨!![(GF4.ofNat' 3), (GF4.ofNat' 0), (GF4.ofNat' 2); (GF4.ofNat' 0), (GF4.ofNat' 1), (GF4.ofNat' 0); (GF4.ofNat' 2), (GF4.ofNat' 0), (GF4.ofNat' 3)], by
    rw [Matrix.det_fin_three]; decide⟩

def mB : Matrix.SpecialLinearGroup (Fin 3) GF4 :=
  ⟨!![(GF4.ofNat' 1), (GF4.ofNat' 2), (GF4.ofNat' 3); (GF4.ofNat' 1), (GF4.ofNat' 3), (GF4.ofNat' 0); (GF4.ofNat' 3), (GF4.ofNat' 0), (GF4.ofNat' 0)], by
    rw [Matrix.det_fin_three]; decide⟩

theorem actA : ∀ i : Fin 21, ∃ c : GF4, c • ((mA : Matrix (Fin 3) (Fin 3) GF4) *ᵥ vec i) =
    vec (pa i) := by
  decide +kernel

theorem actB : ∀ i : Fin 21, ∃ c : GF4, c • ((mB : Matrix (Fin 3) (Fin 3) GF4) *ᵥ vec i) =
    vec (pb i) := by
  decide +kernel

theorem card_F : Nat.card GF4 = 2 ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_center : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) GF4)) = 3 := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := GF4) 0
  rw [Nat.card_congr e.toEquiv, Fintype.card_fin]
  have : Nat.card (rootsOfUnity 3 GF4) = Nat.card {u : GF4ˣ // u ^ 3 = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun u => mem_rootsOfUnity 3 u))
  rw [this, Nat.card_eq_fintype_card]
  decide

theorem card_psl : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) GF4) = 20160 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) GF4))
  rw [card_center, Matrix.card_SL_field 3] at h1
  have h2 : Fintype.card GF4 = 4 := by decide
  simp [Fin.prod_univ_three, h2] at h1
  show Nat.card (Matrix.SpecialLinearGroup (Fin 3) GF4 ⧸
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) GF4)) = 20160
  rw [Nat.card_eq_fintype_card]
  omega

end CFSG.GH74.KGroups.L34
