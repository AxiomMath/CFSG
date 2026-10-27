module

public import CFSG.LocalAnalysis.LargeEvenClassification.NormalElementary

public section

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse targetUniverse

theorem conjNormal_ker_eq_centralizer {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) [Normal.Normal] :
    (MulAut.conjNormal (H := Normal)).ker = Subgroup.centralizer (Normal : Set Ambient) := by
  ext element
  constructor
  · intro helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro normalElement hnormalElement
    have hfixed := congrArg (fun automorphism : MulAut Normal =>
      (automorphism ⟨normalElement, hnormalElement⟩ : Ambient)) helement
    change element * normalElement * element⁻¹ = normalElement at hfixed
    exact (mul_inv_eq_iff_eq_mul.mp hfixed).symm
  · intro helement
    apply MulEquiv.ext
    intro normalElement
    apply Subtype.ext
    change element * (normalElement : Ambient) * element⁻¹ = normalElement
    rw [← Subgroup.mem_centralizer_iff.mp helement normalElement normalElement.property,
      mul_assoc, mul_inv_cancel, mul_one]

theorem centralizer_normal_subgroup {Ambient : Type groupUniverse} [Group Ambient]
    (Normal : Subgroup Ambient) [Normal.Normal] :
    (Subgroup.centralizer (Normal : Set Ambient)).Normal := by
  rw [← conjNormal_ker_eq_centralizer Normal]
  infer_instance

theorem cyclic_quotient_central_commutative {Ambient : Type groupUniverse} [Group Ambient]
    (Central : Subgroup Ambient) [Central.Normal] (hcentral : Central ≤ Subgroup.center Ambient)
    [IsCyclic (Ambient ⧸ Central)] : IsMulCommutative Ambient := by
  let projection := QuotientGroup.map Central (Subgroup.center Ambient) (MonoidHom.id Ambient)
    (by simpa only [Subgroup.comap_id] using hcentral)
  have hsurjective : Function.Surjective projection := by
    intro coset
    obtain ⟨element, helement⟩ := QuotientGroup.mk'_surjective (Subgroup.center Ambient) coset
    refine ⟨QuotientGroup.mk' Central element, ?_⟩
    change QuotientGroup.map Central (Subgroup.center Ambient) (MonoidHom.id Ambient) _
      (QuotientGroup.mk' Central element) = coset
    rw [QuotientGroup.map_mk']
    exact helement
  let : IsCyclic (Ambient ⧸ Subgroup.center Ambient) :=
    isCyclic_of_surjective projection hsurjective
  exact isMulCommutative_of_isCyclic_quotient_center_self Ambient

theorem central_kernel_cyclic_image_commutative {Source : Type groupUniverse} [Group Source]
    {Target : Type targetUniverse} [Group Target] [IsCyclic Target]
    (quotient : Source →* Target) (hsurjective : Function.Surjective quotient)
    (hcentral : quotient.ker ≤ Subgroup.center Source) : IsMulCommutative Source := by
  let equivalence := QuotientGroup.quotientKerEquivOfSurjective quotient hsurjective
  let : IsCyclic (Source ⧸ quotient.ker) :=
    isCyclic_of_surjective equivalence.symm.toMonoidHom equivalence.symm.surjective
  exact cyclic_quotient_central_commutative quotient.ker hcentral

theorem maximal_abelian_normal_selfCentralizing {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime : ℕ} (hprime : prime.Prime) (hpgroup : IsPGroup prime Ambient)
    (Normal : Subgroup Ambient) [Normal.Normal] (hcommutative : IsMulCommutative Normal)
    (hmaximal : ∀ Larger : Subgroup Ambient,
      Larger.Normal → IsMulCommutative Larger → Normal ≤ Larger → Larger ≤ Normal) :
    Subgroup.centralizer (Normal : Set Ambient) = Normal := by
  let Centralizer := Subgroup.centralizer (Normal : Set Ambient)
  have hnormalLe : Normal ≤ Centralizer := by
    intro element helement
    apply Subgroup.mem_centralizer_iff.mpr
    intro normalElement hnormalElement
    exact congrArg (fun entry : Normal => (entry : Ambient))
      (@mul_comm' Normal _ hcommutative ⟨normalElement, hnormalElement⟩ ⟨element, helement⟩)
  apply le_antisymm _ hnormalLe
  by_contra hnotLe
  let : Centralizer.Normal := centralizer_normal_subgroup Normal
  let quotient := QuotientGroup.mk' Normal
  let image := Centralizer.map quotient
  let : image.Normal := Subgroup.Normal.map inferInstance quotient
    (QuotientGroup.mk'_surjective Normal)
  have himageNontrivial : image ≠ ⊥ := by
    intro htrivial
    apply hnotLe
    have hkernelLe := (Subgroup.map_eq_bot_iff Centralizer).mp htrivial
    change Centralizer ≤ (QuotientGroup.mk' Normal).ker at hkernelLe
    simpa only [QuotientGroup.ker_mk'] using hkernelLe
  obtain ⟨Central, hcentralNormal, hcentralLe, _, hcentralCard⟩ :=
    pGroup_normal_center_prime hprime (hpgroup.to_quotient Normal) image himageNontrivial
  let : Central.Normal := hcentralNormal
  let Larger := Central.comap quotient
  let : Larger.Normal := inferInstance
  have hpreimage : image.comap quotient = Centralizer := by
    apply Subgroup.comap_map_eq_self
    change (QuotientGroup.mk' Normal).ker ≤ Centralizer
    simpa only [QuotientGroup.ker_mk'] using hnormalLe
  have hlargerLe : Larger ≤ Centralizer := by
    rw [← hpreimage]
    exact Subgroup.comap_mono hcentralLe
  let restriction := quotient.subgroupComap Central
  have hrestriction : Function.Surjective restriction :=
    quotient.subgroupComap_surjective Central (QuotientGroup.mk'_surjective Normal)
  let : Fact prime.Prime := ⟨hprime⟩
  let : IsCyclic Central := isCyclic_of_prime_card hcentralCard
  have hkernelCentral : restriction.ker ≤ Subgroup.center Larger := by
    intro element helement
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    have helementNormal : (element : Ambient) ∈ Normal := by
      have hzero := congrArg (fun entry : Central => (entry : Ambient ⧸ Normal))
        (MonoidHom.mem_ker.mp helement)
      change (QuotientGroup.mk' Normal) (element : Ambient) = 1 at hzero
      have hmem : (element : Ambient) ∈ (QuotientGroup.mk' Normal).ker := hzero
      rwa [QuotientGroup.ker_mk'] at hmem
    exact (Subgroup.mem_centralizer_iff.mp (hlargerLe other.property)
      element helementNormal).symm
  have hlargerComm : IsMulCommutative Larger :=
    central_kernel_cyclic_image_commutative restriction hrestriction hkernelCentral
  have hnormalLarger : Normal ≤ Larger := by
    have hkernelLe := Subgroup.ker_le_comap quotient Central
    change (QuotientGroup.mk' Normal).ker ≤ Larger at hkernelLe
    simpa only [QuotientGroup.ker_mk'] using hkernelLe
  have hlargerNormal := hmaximal Larger inferInstance hlargerComm hnormalLarger
  have hlargerEq : Larger = Normal := le_antisymm hlargerNormal hnormalLarger
  have hcardLarger : Nat.card Larger = prime * Nat.card Normal := by
    rw [card_comap_of_surjective quotient (QuotientGroup.mk'_surjective Normal),
      hcentralCard, QuotientGroup.ker_mk']
  rw [hlargerEq] at hcardLarger
  have hpositive : 0 < Nat.card Normal := Nat.card_pos
  have hprimeOne : prime = 1 := by nlinarith
  exact hprime.ne_one hprimeOne

end CFSG.LargeEvenClassification.Helpers
