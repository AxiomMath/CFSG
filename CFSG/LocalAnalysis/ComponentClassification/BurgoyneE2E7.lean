module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Split
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Field
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Twisted
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LieType.AlgebraicGroups (signMaskTuple)


theorem burgRow_E7 (hT : BurgoyneE2TwistedE7Input) {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (α : MulAut (adjointGroup .E7 K))
    (hα : orderOf α = 2) : BurgCoreFor α ∨ BurgTorusFor α := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (one_le_and_three_le_of_card hp hp2 hK).1 hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  rcases LieType.AlgebraicGroups.odd_E7_involution_inner_or_quadratic hodd hα2 with
    ⟨g, a, hga⟩ | ⟨p', e, hp', he, hK', δ, hδ, g, a, hga⟩
  · have hαeq : α = MulAut.conj g * rootDiagAut .E7 K a := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hga x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    by_cases hsplit : ∃ m : ℕ, (m = 1 ∨ m = 2 ∨ m = 3) ∧ ∃ ψ : MulAut (adjointGroup .E7 K),
        ψ * α * ψ⁻¹ = rootDiagAut .E7 K (signMaskTuple .E7 K m)
    · obtain ⟨m, hm, ψ, hψ⟩ := hsplit
      have hback : ψ⁻¹ * rootDiagAut .E7 K (signMaskTuple .E7 K m) * ψ⁻¹⁻¹ = α := by
        rw [← hψ]
        group
      rcases burgRow_E7_split hp hp2 hK hm with h | h
      · left
        rw [← hback]
        exact h.conj ψ⁻¹
      · right
        rw [← hback]
        exact h.conj ψ⁻¹
    · push Not at hsplit
      subst hαeq
      exact hT K hK2 g a hα hsplit
  · exact Or.inl (burgCoreFor_E7_field hp' he hK2 hK' hδ hga hα2)

theorem burgoynePropA_E7_of_twisted (hT : BurgoyneE2TwistedE7Input) {X : Type} [Group X]
    [Finite X] (hX : IsM4 X) {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .E7 n p f) {t : X} (ht : orderOf t = 2)
    {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -⟩ := hX
  rcases hL with ⟨hcl, -⟩ | ⟨-, -, hmod⟩ | ⟨-, hree, -⟩ | ⟨-, h, -⟩
  · exfalso
    simp [classicalTags] at hcl
  · obtain ⟨⟨hp, -, -⟩, hU⟩ := hmod
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 hU
    exact propAConclusion_of_rows hsimple hnab center_adjointGroup_eq_bot e
      (burgRow_E7 hT hp hp2 hK) ht hY hYO
  · exfalso
    simp [reeTitsTags] at hree
  · exact absurd h (by decide)

end CFSG.ComponentClassification.Burgoyne.E2
