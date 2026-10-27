module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddForm
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddSL

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo.OppCl
open scoped Matrix

section SU

variable {F : Type} [Field F] [Finite F] {q f : ℕ} [Fact q.Prime] [CharP F q]
  (hK : Nat.card F = (q ^ f) ^ 2) (n : ℕ)

include hK in
theorem ea1_SU : EA1ε (unitaryForm q f hK n) (fun v => (unitaryForm q f hK n).β v v = 0)
    (natRep (StatedSU n (q ^ f) F)) (-1) := by
  intro x y hx hxy
  have hy : unitaryInvolution F q f ((unitaryForm q f hK n).β y y) =
      (unitaryForm q f hK n).β y y := (unitaryForm_symm hK y y).symm
  have hy' : unitaryInvolution F q f (-(unitaryForm q f hK n).β y y) =
      -(unitaryForm q f hK n).β y y := by rw [map_neg, hy]
  obtain ⟨c, hc⟩ := exists_add_unitaryInvolution_eq hK hy'
  obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_eichler hK hx hxy hc
  refine ⟨c, ⟨A, hA⟩, fun v => ?_⟩
  rw [natRep_apply]
  show (A : Matrix (Fin n) (Fin n) F) *ᵥ v = _
  rw [hAv v]
  module

include hK in
theorem ea2_SU : EA2ε (unitaryForm q f hK n) (fun v => (unitaryForm q f hK n).β v v = 0)
    (natRep (StatedSU n (q ^ f) F)) := by
  intro x hx
  obtain ⟨c₀, hc₀, hσc₀⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨A, hA, hAv⟩ := exists_mem_statedSU_transvection hK hx hσc₀
  refine ⟨c₀, ⟨A, hA⟩, hc₀, fun v => ?_⟩
  rw [natRep_apply]
  exact hAv v

include hK in
theorem radRigidInner_PSU (hn : 3 ≤ n) :
    RadRigidInner q (StatedProj (StatedSU n (q ^ f) F)) := by
  have hdim : 3 ≤ Module.finrank F (Fin n → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hn
  refine radRigidInner_of_rigid (H := StatedSU n (q ^ f) F)
    ((StatedScalars (Fin n) F).subgroupOf (StatedSU n (q ^ f) F)) (statedProj_kernel_central _)
    (statedProj_kernel_coprime q _) (natRep (StatedSU n (q ^ f) F)) (natRep_injective _)
    (fun Q => isoFlag (unitaryForm q f hK n) (natRep (StatedSU n (q ^ f) F)) Q)
    (fun Q _ => isoFlag_zero _ _ Q) (fun Q _ => ⟨_, isoFlag_top _ _ Q⟩)
    (fun Q _ => normalizer_le_flagStab_isoFlag _ _ (isIsometric_natRep_statedSU hK n) Q)
    (fun Q hQ => le_flagKernel_isoFlag _ _ q (isIsometric_natRep_statedSU hK n) Q hQ)
    (fun x hx => mem_statedScalars_of_natRep _ x hx) ?_
  exact rigidInner_form (unitaryForm q f hK n) (fun v => (unitaryForm q f hK n).β v v = 0)
    (unitaryForm q f hK n).IsTotallyIsotropic (natRep (StatedSU n (q ^ f) F))
    (fun Q => isoFlag (unitaryForm q f hK n) (natRep (StatedSU n (q ^ f) F)) Q) (Or.inr rfl)
    (fun c => unitaryInvolution_involutive hK c) hdim (fun U hU => hU)
    (fun U hU v hv => hU hv v hv) (natRep_injective _) (ea1_SU hK n) (Or.inl (ea2_SU hK n))
    (fun Q _ => ⟨isoSeq (unitaryForm q f hK n) (natRep (StatedSU n (q ^ f) F)) Q,
      Module.finrank F (Fin n → F), isoSeq_zero _ _ Q, isoSeq_mono _ _ Q,
      isoSeq_isTotallyIsotropic _ _ Q, rfl⟩)
    (isIsometric_natRep_statedSU hK n)

end SU

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
