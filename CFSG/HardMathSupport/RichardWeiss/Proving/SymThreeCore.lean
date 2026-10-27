module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv

theorem sym3_involution_not_comm_finRotate :
    ∀ τ : Perm (Fin 3), τ ≠ 1 → τ ^ 2 = 1 → τ * finRotate 3 ≠ finRotate 3 * τ := by
  decide

theorem not_pPrimeCore_le_centralizer_of_sym3 {Γ : Type} [Group Γ] (e : Γ ≃* Equiv.Perm (Fin 3))
    {R : Subgroup Γ} {r : Γ} (hr : r ∈ R) (hr1 : r ≠ 1) (hr2 : r ^ 2 = 1) :
    ¬ CFSG.pPrimeCore 2 Γ ≤ Subgroup.centralizer (R : Set Γ) := by
  intro hle
  have hAnormal : ((alternatingGroup (Fin 3)).map e.symm.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.symm.toMonoidHom e.symm.surjective
  have hcard : Nat.card ((alternatingGroup (Fin 3)).map e.symm.toMonoidHom) = 3 := by
    rw [Nat.card_congr
        (Subgroup.equivMapOfInjective (alternatingGroup (Fin 3)) e.symm.toMonoidHom
          e.symm.injective).symm.toEquiv,
      nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hcop : Nat.Coprime 2 (Nat.card ((alternatingGroup (Fin 3)).map e.symm.toMonoidHom)) := by
    rw [hcard]
    norm_num
  have hAle : (alternatingGroup (Fin 3)).map e.symm.toMonoidHom ≤ CFSG.pPrimeCore 2 Γ := by
    unfold CFSG.pPrimeCore
    exact le_sSup ⟨hAnormal, hcop⟩
  have hrot : finRotate 3 ∈ alternatingGroup (Fin 3) := by
    rw [Equiv.Perm.mem_alternatingGroup, sign_finRotate]
    decide
  have ha' : e.symm (finRotate 3) ∈ (alternatingGroup (Fin 3)).map e.symm.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨finRotate 3, hrot, rfl⟩
  have hcomm : r * e.symm (finRotate 3) = e.symm (finRotate 3) * r :=
    (Subgroup.mem_centralizer_iff.mp (hle (hAle ha'))) r hr
  have hcomm' : e r * finRotate 3 = finRotate 3 * e r := by
    have h := congrArg e hcomm
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  have hne : e r ≠ 1 := by
    intro h
    exact hr1 (e.injective (by rw [h, map_one]))
  have hsq : (e r) ^ 2 = 1 := by
    rw [← map_pow, hr2, map_one]
  exact sym3_involution_not_comm_finRotate (e r) hne hsq hcomm'

end CFSG.HardMathSupport.RichardWeiss.Proving

end
