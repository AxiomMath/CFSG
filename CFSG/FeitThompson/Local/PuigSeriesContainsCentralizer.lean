module

public import CFSG.FeitThompson.Local.PuigTermsContainAbelianNormal
public import CFSG.FeitThompson.Local.MaximalNormalAbelianSelfCentralizing
import Mathlib.Data.SetLike.Fintype

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {p : ℕ} {P : Type*} [Group P]

theorem exists_maximal_normal_isMulCommutative (P : Type*) [Group P] [Finite P] :
    ∃ A : Subgroup P, Maximal (fun B : Subgroup P => B.Normal ∧ IsMulCommutative B) A := by
  obtain ⟨A, -, hA⟩ :=
    Finite.exists_le_maximal (p := fun B : Subgroup P => B.Normal ∧ IsMulCommutative B)
      (a := (⊥ : Subgroup P)) ⟨inferInstance, inferInstance⟩
  exact ⟨A, hA⟩

theorem exists_normal_isMulCommutative_centralizer_eq [Finite P] (hp : p.Prime)
    (hP : IsPGroup p P) :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative A ∧ centralizer (A : Set P) = A := by
  obtain ⟨A, hA⟩ := exists_maximal_normal_isMulCommutative P
  exact ⟨A, hA.1.1, hA.1.2,
    centralizer_eq_of_maximal_normal_isMulCommutative_of_isPGroup hp hP hA⟩

theorem centralizer_le_of_forall_normal_isMulCommutative_le [Finite P] (hp : p.Prime)
    (hP : IsPGroup p P) {H : Subgroup P}
    (hH : ∀ A : Subgroup P, A.Normal → IsMulCommutative A → A ≤ H) :
    centralizer (H : Set P) ≤ H := by
  obtain ⟨A, hAn, hAc, hAcent⟩ := exists_normal_isMulCommutative_centralizer_eq hp hP
  calc centralizer (H : Set P) ≤ centralizer (A : Set P) :=
        centralizer_le (by exact_mod_cast hH A hAn hAc)
    _ = A := hAcent
    _ ≤ H := hH A hAn hAc

theorem centralizer_puigSeries_le [Finite P] (hp : p.Prime) (hP : IsPGroup p P) {n : ℕ}
    (hn : 1 ≤ n) : centralizer (puigSeries P n : Set P) ≤ puigSeries P n :=
  centralizer_le_of_forall_normal_isMulCommutative_le hp hP fun _ hAn hAc =>
    have := hAn; le_puigSeries_of_normal hAc hn

theorem centralizer_puigLower_le [Finite P] (hp : p.Prime) (hP : IsPGroup p P) :
    centralizer (puigLower P : Set P) ≤ puigLower P :=
  centralizer_le_of_forall_normal_isMulCommutative_le hp hP fun _ hAn hAc =>
    have := hAn; le_puigLower_of_normal hAc

theorem centralizer_puigSubgroup_le [Finite P] (hp : p.Prime) (hP : IsPGroup p P) :
    centralizer (puigSubgroup P : Set P) ≤ puigSubgroup P :=
  centralizer_le_of_forall_normal_isMulCommutative_le hp hP fun _ hAn hAc =>
    have := hAn; le_puigSubgroup_of_normal hAc

theorem centralizer_puigUpper_le [Finite P] (hp : p.Prime) (hP : IsPGroup p P) :
    centralizer (puigUpper P : Set P) ≤ puigUpper P :=
  centralizer_le_of_forall_normal_isMulCommutative_le hp hP fun _ hAn hAc =>
    have := hAn; le_puigUpper_of_normal hAc

theorem centralizer_puigSubgroup_eq_puigCenter [Finite P] (hp : p.Prime) (hP : IsPGroup p P) :
    centralizer (puigSubgroup P : Set P) = puigCenter P := by
  rw [puigCenter_eq_inf_centralizer]
  exact (inf_eq_right.2 (centralizer_puigSubgroup_le hp hP)).symm

end CFSG.FeitThompson

end
