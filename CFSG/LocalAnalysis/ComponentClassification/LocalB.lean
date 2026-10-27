module

public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents

public section

open CFSG.Open

namespace CFSG.ComponentClassification.LocalB

@[expose] def LocalBProperty (G : Type*) [Group G] : Prop :=
  ∀ twoSubgroup : Subgroup G, twoSubgroup ≠ ⊥ → IsPGroup 2 twoSubgroup →
    ∀ component : Subgroup (Subgroup.normalizer (twoSubgroup : Set G)),
      TwoComponents.IsTwoComponent component → IsComponentOf component ⊤

theorem of_corefree_and_inclusion {G : Type*} [Group G] [Finite G]
    (hcorefree : componentClassificationOddCore G = ⊥)
    (hinclusion : ∀ twoSubgroup : Subgroup G, twoSubgroup ≠ ⊥ → IsPGroup 2 twoSubgroup →
      (TwoComponents.badSubgroup (Subgroup.normalizer (twoSubgroup : Set G))).map
        (Subgroup.normalizer (twoSubgroup : Set G)).subtype ≤ TwoComponents.badSubgroup G) :
    LocalBProperty G := by
  intro twoSubgroup hnontrivial htwo component hcomponent
  have hbadMap := hinclusion twoSubgroup hnontrivial htwo
  rw [TwoComponents.badSubgroup_eq_bot_of_corefree hcorefree] at hbadMap
  have hmapBot := le_antisymm hbadMap bot_le
  have hbad := (Subgroup.map_eq_bot_iff_of_injective _
    (Subgroup.normalizer (twoSubgroup : Set G)).subtype_injective).mp hmapBot
  exact TwoComponents.ordinary_of_badSubgroup_eq_bot hbad hcomponent

theorem mem_zpowers_iff_of_involution {G : Type*} [Group G] [Finite G]
    (involution element : G) (hinvolution : orderOf involution = 2) :
    element ∈ Subgroup.zpowers involution ↔ element = 1 ∨ element = involution := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hinvolution]
  constructor
  · intro hmem
    obtain ⟨exponent, hexponent, rfl⟩ := Finset.mem_image.mp hmem
    have hlt : exponent < 2 := Finset.mem_range.mp hexponent
    have hcases : exponent = 0 ∨ exponent = 1 := by omega
    rcases hcases with rfl | rfl
    · exact Or.inl (pow_zero involution)
    · exact Or.inr (pow_one involution)
  · intro hcases
    rcases hcases with hone | heq
    · exact Finset.mem_image.mpr ⟨0, by decide, (pow_zero involution).trans hone.symm⟩
    · exact Finset.mem_image.mpr ⟨1, by decide, (pow_one involution).trans heq.symm⟩

theorem normalizer_zpowers_of_involution {G : Type*} [Group G] [Finite G]
    (involution : G) (hinvolution : orderOf involution = 2) :
    Subgroup.normalizer (Subgroup.zpowers involution : Set G) =
      Subgroup.centralizer ({involution} : Set G) := by
  have hne : involution ≠ 1 := by
    intro hone
    simp [hone] at hinvolution
  ext element
  constructor
  · intro hnormalizer
    have hconjugate := (Subgroup.mem_normalizer_iff.mp hnormalizer involution).mp
      (Subgroup.mem_zpowers involution)
    rcases (mem_zpowers_iff_of_involution involution _ hinvolution).mp hconjugate with
      hone | hfixed
    · have hinvolutionOne : involution = 1 := by
        have heq : (MulAut.conj element) involution = (MulAut.conj element) 1 := by
          simpa only [MulAut.conj_apply, map_one] using hone
        exact (MulAut.conj element).injective heq
      exact (hne hinvolutionOne).elim
    · apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      have heq : member = involution := Set.mem_singleton_iff.mp hmember
      subst member
      calc
        involution * element = (element * involution * element⁻¹) * element := by rw [hfixed]
        _ = element * involution := by group
  · intro hcentralizer
    have hcommutes := Subgroup.mem_centralizer_iff.mp hcentralizer involution (by simp)
    apply Subgroup.mem_normalizer_iff.mpr
    intro member
    rw [mem_zpowers_iff_of_involution involution member hinvolution,
      mem_zpowers_iff_of_involution involution (element * member * element⁻¹) hinvolution]
    have hfixed : element * involution * element⁻¹ = involution := by
      rw [← hcommutes]
      group
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl (by group)
      · exact Or.inr hfixed
    · rintro (hone | hinvolutionEq)
      · left
        have heq : (MulAut.conj element) member = (MulAut.conj element) 1 := by
          simpa only [MulAut.conj_apply, map_one] using hone
        exact (MulAut.conj element).injective heq
      · right
        have heq : (MulAut.conj element) member = (MulAut.conj element) involution := by
          change element * member * element⁻¹ = element * involution * element⁻¹
          rw [hfixed]
          exact hinvolutionEq
        exact (MulAut.conj element).injective heq

theorem ordinary_at_involution {G : Type*} [Group G] [Finite G]
    (hB : LocalBProperty G) (involution : G) (hinvolution : orderOf involution = 2)
    (component : Subgroup (Subgroup.centralizer ({involution} : Set G)))
    (hcomponent : TwoComponents.IsTwoComponent component) : IsComponentOf component ⊤ := by
  have hnontrivial : Subgroup.zpowers involution ≠ ⊥ := by
    intro hbot
    have hone : involution = 1 := Subgroup.zpowers_eq_bot.mp hbot
    simp [hone] at hinvolution
  have htwo : IsPGroup 2 (Subgroup.zpowers involution) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hinvolution)
  have hlocal := hB (Subgroup.zpowers involution) hnontrivial htwo
  have hnormalizer := normalizer_zpowers_of_involution involution hinvolution
  rw [hnormalizer] at hlocal
  exact hlocal component hcomponent

theorem hasInvolutionComponent_of_componentType {G : Type*} [Group G] [Finite G]
    (hB : LocalBProperty G) (hcomponentType : componentClassificationComponentType G) :
    HasInvolutionComponent G := by
  obtain ⟨involution, hinvolution, component, hcomponent⟩ := hcomponentType
  obtain ⟨lift, hlift, _⟩ := TwoComponents.exists_lift component hcomponent
  have hordinary := ordinary_at_involution hB involution hinvolution lift hlift
  have hne : involution ≠ 1 := by
    intro hone
    simp [hone] at hinvolution
  have hsquare : involution ^ 2 = 1 := by
    simpa only [hinvolution] using pow_orderOf_eq_one involution
  refine ⟨involution, lift.map (Subgroup.centralizer ({involution} : Set G)).subtype,
    hne, hsquare, ?_⟩
  refine ⟨Subgroup.map_subtype_le lift, ?_, Components.quasisimple_of_equiv
    (lift.equivMapOfInjective (Subgroup.centralizer ({involution} : Set G)).subtype
      (Subgroup.centralizer ({involution} : Set G)).subtype_injective).symm hordinary.2.2⟩
  have hrelative := Components.chain_map
    (Subgroup.centralizer ({involution} : Set G)).subtype hordinary.2.1
  have htopMap : (⊤ : Subgroup (Subgroup.centralizer ({involution} : Set G))).map
      (Subgroup.centralizer ({involution} : Set G)).subtype =
      Subgroup.centralizer ({involution} : Set G) := by
    ext element
    constructor
    · rintro ⟨member, _, rfl⟩
      exact member.property
    · intro hmem
      exact ⟨⟨element, hmem⟩, Subgroup.mem_top _, rfl⟩
  rwa [htopMap] at hrelative

end CFSG.ComponentClassification.LocalB
