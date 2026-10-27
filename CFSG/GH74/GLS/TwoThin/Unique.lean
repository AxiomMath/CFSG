module

public import CFSG.LocalAnalysis.ComponentClassification.TwoLayerTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingPrime
public import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup CFSG.ComponentClassification CFSG.Open

theorem le_of_map_le_of_residual {Z H : Type*} [Group Z] [Finite Z] [Group H] [Finite H]
    (q : Z →* H) (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (X S : Subgroup Z) (hX : TwoResidual.subgroup ↥X = ⊤) (hS : IsSubnormal S ⊤)
    (himages : X.map q ≤ S.map q) : X ≤ S := by
  let image := S.map q
  let preimage := image.comap q
  let restriction : preimage →* image :=
    (q.domRestrict preimage).codRestrict image fun element => element.property
  have hsurjectiveRestriction : Function.Surjective restriction := by
    intro element
    obtain ⟨lift, hvalue⟩ := hq element.val
    have hmem : lift ∈ preimage := by
      change q lift ∈ image
      rw [hvalue]
      exact element.property
    exact ⟨⟨lift, hmem⟩, Subtype.ext hvalue⟩
  have hkernel : restriction.ker = (q.domRestrict preimage).ker := by
    ext element
    change restriction element = 1 ↔ q element.val = 1
    exact ⟨fun hone => congrArg Subtype.val hone, fun hone => Subtype.ext hone⟩
  have hoddRestriction : Odd (Nat.card restriction.ker) := by
    rw [hkernel]
    exact OddKernel.odd_card_restriction_kernel q hodd preimage
  have hsubnormalLe : S ≤ preimage := Subgroup.le_comap_map q _
  have hcovering : Function.Surjective (restriction.domRestrict (S.subgroupOf preimage)) := by
    intro element
    obtain ⟨lift, hmem, hvalue⟩ := Subgroup.mem_map.mp element.property
    exact ⟨⟨⟨lift, hsubnormalLe hmem⟩, hmem⟩, Subtype.ext hvalue⟩
  have hoddIndex := TwoResidual.odd_index_of_covering restriction hsurjectiveRestriction
    hoddRestriction (S.subgroupOf preimage) hcovering
  have hlocalChain : IsSubnormal (S.subgroupOf preimage) ⊤ :=
    Components.chain_of_mathlib_subnormal
      ((Components.mathlib_subnormal_of_chain hS Subgroup.IsSubnormal.top).subgroupOf)
  have hresidual := TwoResidual.subnormal_contains_of_odd_index
    (S.subgroupOf preimage) hlocalChain hoddIndex
  have hXle : X ≤ preimage := Subgroup.map_le_iff_le_comap.mp himages
  have hgenerated : TwoResidual.subgroup ↥(X.subgroupOf preimage) = ⊤ :=
    TwoComponentTransport.residual_eq_top_of_equiv (Subgroup.subgroupOfEquivOfLe hXle).symm hX
  have hmap := TwoResidual.map_le (X.subgroupOf preimage).subtype
  rw [hgenerated] at hmap
  intro element hmem
  exact hresidual (hmap ⟨⟨⟨element, hXle hmem⟩, hmem⟩, Subgroup.mem_top _, rfl⟩)

theorem residual_eq_top_of_isPGroup {Z : Type*} [Group Z] {X : Subgroup Z} (hX : IsPGroup 2 ↥X) :
    TwoResidual.subgroup ↥X = ⊤ :=
  top_unique (TwoResidual.twoSubgroup_le _ (hX.of_equiv Subgroup.topEquiv.symm))

theorem le_of_isPGroup_of_map_le {Z H : Type*} [Group Z] [Finite Z] [Group H] [Finite H]
    (q : Z →* H) (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (X S : Subgroup Z) (hX : IsPGroup 2 ↥X) (hS : IsSubnormal S ⊤)
    (himages : X.map q ≤ S.map q) : X ≤ S :=
  le_of_map_le_of_residual q hq hodd X S (residual_eq_top_of_isPGroup hX) hS himages

theorem isPGroup_zpowers_of_pow_eq_one {Z : Type*} [Group Z] {z : Z} {n : ℕ}
    (hz : z ^ (2 ^ n) = 1) : IsPGroup 2 ↥(Subgroup.zpowers z) := by
  rintro ⟨_, m, rfl⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]

theorem exists_unique_isTwoComponent {Z : Type*} [Group Z] [Finite Z]
    (hq : CFSG.IsQuasisimple (Z ⧸ pPrimeCore 2 Z)) :
    ∃ Λ : Subgroup Z, TwoComponents.IsTwoComponent Λ ∧
      (∀ Λ' : Subgroup Z, TwoComponents.IsTwoComponent Λ' → Λ' = Λ) ∧
      Λ.map (QuotientGroup.mk' (pPrimeCore 2 Z)) = ⊤ ∧
      ∀ z : Z, (∃ n : ℕ, z ^ (2 ^ n) = 1) → z ∈ Λ := by
  set q := QuotientGroup.mk' (pPrimeCore 2 Z) with hqdef
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hodd : Odd (Nat.card q.ker) := by
    rw [hqdef, QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcore : componentClassificationOddCore (Z ⧸ pPrimeCore 2 Z) = ⊥ := by
    rw [← CatalogueBAlternating.primeCore_two_eq_oddCore]
    exact pPrimeCore_quotient_eq_bot Z
  have hqO : CFSG.Open.IsQuasisimple (Z ⧸ pPrimeCore 2 Z) :=
    ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have htopcomp : IsComponentOf (⊤ : Subgroup (Z ⧸ pPrimeCore 2 Z)) ⊤ :=
    ⟨le_top, IsSubnormal.refl _, Components.quasisimple_of_equiv Subgroup.topEquiv hqO⟩
  have htop2 : TwoComponents.IsTwoComponent (⊤ : Subgroup (Z ⧸ pPrimeCore 2 Z)) :=
    TwoLayerTransport.ordinary_isTwoComponent_of_corefree hcore ⊤ htopcomp
  obtain ⟨Λ, hΛ, hmap⟩ := OddKernelTwoComponents.exists_lift q hsurj hodd ⊤ htop2
  refine ⟨Λ, hΛ, ?_, hmap, ?_⟩
  · intro Λ' hΛ'
    have h1 := OddKernelTwoComponents.image q hsurj hodd Λ' hΛ'
    have h2 := TwoComponents.ordinary_of_corefree hcore h1
    have h3 : Λ'.map q = ⊤ := LocalComponents.eq_of_le _ _ h2 htopcomp le_top
    exact OddKernelTwoComponents.lift_unique q hsurj hodd Λ' Λ hΛ' hΛ (by rw [h3, hmap])
  · rintro z ⟨n, hz⟩
    exact (le_of_isPGroup_of_map_le q hsurj hodd (Subgroup.zpowers z) Λ
      (isPGroup_zpowers_of_pow_eq_one hz) hΛ.1 (by rw [hmap]; exact le_top))
      (Subgroup.mem_zpowers z)

end CFSG.GH74.GLS.TwoThin
