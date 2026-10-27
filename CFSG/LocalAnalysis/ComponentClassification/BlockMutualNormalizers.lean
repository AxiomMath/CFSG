module

public import CFSG.LocalAnalysis.ComponentClassification.BlockFactorContainment
public import CFSG.LocalAnalysis.ComponentClassification.SubgroupFixedInvolution

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockMutualNormalizers

theorem even {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (element : G) (helement : element ∈ BlockFusion.involutions component)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (himage : (MulAut.conj actor) element ∈ UniversalOrbitBlock.normalizer component)
    (first second : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component) :
    Even (Nat.card ↥(first ⊓ Subgroup.normalizer (UniversalOrbitBlock.conjugate second actor : Set G))) ∧
      Even (Nat.card ↥(UniversalOrbitBlock.conjugate second actor ⊓ Subgroup.normalizer (first : Set G))) := by
  let movedElement := (MulAut.conj actor) element
  let image := UniversalOrbitBlock.conjugate second actor
  let normalizer := UniversalOrbitBlock.normalizer component
  have hmovedOrder : orderOf movedElement = 2 :=
    (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective element).trans helement.1
  have hmovedNormalizes : movedElement ∈ Subgroup.normalizer (first : Set G) :=
    (CommutingComponentFamily.normalizer_iff_conjugate_eq first movedElement).mpr
      (hcontrol element helement actor hactor himage first hfirst)
  obtain ⟨firstInvolution, hfirstInvolution, hfirstOrder, hfirstFixed⟩ :=
    SubgroupFixedInvolution.involution_normalizing first
      (UniversalOrbitBlock.orbit_even component heven first hfirst.1) movedElement hmovedOrder hmovedNormalizes
  have hfirstFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard
    first hfirst firstInvolution hfirstInvolution hfirstOrder
  have hcentralizerImage : Subgroup.centralizer {movedElement} ≤ normalizer.map (MulAut.conj actor).toMonoidHom := by
    obtain ⟨horder, anchor, hanchor, hanchorCentral⟩ := helement
    have hle := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
      (UniversalOrbitBlock.involution_centralizer_le component heven huniversal hquasisimple anchor hanchor
        element horder hanchorCentral)
    rwa [UniversalComponentBlock.singleton_centralizer_map] at hle
  have hfirstNormalizesImage := BlockFactorContainment.reverse_normalizes component hcontrol actor hactor
    second hsecond firstInvolution hfirstFusion (hcentralizerImage hfirstFixed)
  have hfirstMutual : firstInvolution ∈ first ⊓ Subgroup.normalizer (image : Set G) :=
    ⟨hfirstInvolution, hfirstNormalizesImage⟩
  have hfirstEven : Even (Nat.card ↥(first ⊓ Subgroup.normalizer (image : Set G))) := by
    apply even_iff_two_dvd.mpr
    have hdivides := (first ⊓ Subgroup.normalizer (image : Set G)).orderOf_dvd_natCard hfirstMutual
    rwa [hfirstOrder] at hdivides
  have himageEven : Even (Nat.card image) := by
    change Even (Nat.card (second.map (MulAut.conj actor).toMonoidHom))
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective]
    exact UniversalOrbitBlock.orbit_even component heven second hsecond.1
  obtain ⟨secondInvolution, hsecondInvolution, hsecondOrder, hsecondFixed⟩ :=
    SubgroupFixedInvolution.involution_normalizing image himageEven firstInvolution hfirstOrder hfirstNormalizesImage
  have hfirstCentralizerLe : Subgroup.centralizer {firstInvolution} ≤ normalizer := by
    obtain ⟨horder, anchor, hanchor, hanchorCentral⟩ := hfirstFusion
    exact UniversalOrbitBlock.involution_centralizer_le component heven huniversal hquasisimple anchor hanchor
      firstInvolution horder hanchorCentral
  have hsecondNormalizer : secondInvolution ∈ normalizer := hfirstCentralizerLe hsecondFixed
  have hsecondNormalizes : secondInvolution ∈ Subgroup.normalizer (first : Set G) := by
    obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hsecondInvolution
    have horiginalOrder : orderOf original = 2 :=
      (orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective original).symm.trans
        ((congrArg orderOf heq).trans hsecondOrder)
    have horiginalFusion := BlockFactorInvolutions.mem_fusion_set component heven huniversal hcard second hsecond
      original horiginal horiginalOrder
    have heq' : (MulAut.conj actor) original = secondInvolution := heq
    have himageNormalizer : (MulAut.conj actor) original ∈ normalizer := by rwa [heq']
    have hfixed := hcontrol original horiginalFusion actor hactor himageNormalizer first hfirst
    rw [heq'] at hfixed
    exact (CommutingComponentFamily.normalizer_iff_conjugate_eq first secondInvolution).mpr hfixed
  have hsecondEven : Even (Nat.card ↥(image ⊓ Subgroup.normalizer (first : Set G))) := by
    apply even_iff_two_dvd.mpr
    have hdivides := (image ⊓ Subgroup.normalizer (first : Set G)).orderOf_dvd_natCard
      (show secondInvolution ∈ image ⊓ Subgroup.normalizer (first : Set G) from
        ⟨hsecondInvolution, hsecondNormalizes⟩)
    rwa [hsecondOrder] at hdivides
  exact ⟨hfirstEven, hsecondEven⟩

end CFSG.ComponentClassification.BlockMutualNormalizers
