module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinLift

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  full_central_kernel_involution_fixed_component_correspondence)
open CFSG.ComponentClassification.CatLeafProof.X10Lin (ModelIn)

theorem modelIn_of_centralLift {P S : Type} [Group P] [Group S] [Finite P]
    {π : P →* S} (hπ : Function.Surjective π) (hK : π.ker ≤ center P) {a : MulAut P}
    {α : MulAut S} (ha : ∀ x, a (a x) = x) (hα : ∀ s, α (α s) = s)
    (hcomm : ∀ x, π (a x) = α (π x)) {ℓ : ℕ} {T : Set (StatedLieTag × ℕ × ℕ)}
    (h : ∀ Q : Subgroup (fixedSubgroup a), IsComponent Q → ModelIn ℓ T Q)
    {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L) : ModelIn ℓ T L := by
  obtain ⟨-, -, -, hlift, -⟩ :=
    full_central_kernel_involution_fixed_component_correspondence hπ hK ha hα hcomm
  set R := L.map (fixedSubgroup α).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup α) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup α) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, -, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  exact (((h _ hQ').of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm).of_centerQuotient_equiv
    eQR.symm).of_mulEquiv
      (L.equivMapOfInjective (fixedSubgroup α).subtype (subtype_injective _))

end CFSG.OddStandard.HigherRank.LinUnit
