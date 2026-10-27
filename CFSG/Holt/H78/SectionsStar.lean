module

public import CFSG.Holt.H78.SectionsBlocks

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

section HoltTriple

theorem IsHoltTriple.isStarGroup [Finite G] [Finite Ω] {z : G} {α : Ω}
    (h : IsHoltTriple G Ω z α) (h3 : 3 ≤ Nat.card Ω) : IsStarGroup G Ω := by
  have hlong : ∃! ω : Ω, z • ω = ω :=
    ⟨α, (h.smul_eq_iff α).mpr rfl, fun ω hω => (h.smul_eq_iff ω).mp hω⟩
  have := h.isPretransitive
  refine ⟨CFSG.Holt.odd_card h.orderOf_eq_two hlong, h3, fun ω S hS hSω _ => ?_⟩
  obtain ⟨d, hd, hSd, hdω⟩ := exists_isConj_le_centralizer_of_le_stabilizer h.orderOf_eq_two
    hlong h.exists_sylow hS hSω
  refine ⟨d, ⟨⟨(orderOf_eq_of_isConj hd).symm.trans h.orderOf_eq_two, ω, (hdω ω).mpr rfl,
    fun ω' h' => (hdω ω').mp h'⟩, (hdω ω).mpr rfl⟩,
    Subgroup.mem_centralizer_iff.mpr fun s hs => Subgroup.mem_centralizer_singleton_iff.mp
      (hSd hs)⟩

end HoltTriple

section E4

variable [Finite G] [Finite Ω]

theorem IsStarGroup.isPretransitive_centralizer (hG : IsStarGroup G Ω) {S : Subgroup G}
    (hS : IsPGroup 2 S) : IsPretransitive (Subgroup.centralizer (S : Set G)) (fixSet Ω S) := by
  by_cases h3 : 3 ≤ Nat.card (fixSet Ω S)
  · have := (isStarGroup_centralizerImage hG hS h3).isPretransitive
    refine ⟨fun δ ε => ?_⟩
    obtain ⟨y, hy⟩ := exists_smul_eq (centralizerImage Ω S) δ ε
    obtain ⟨c, hc, hcy⟩ := mem_centralizerImage.mp y.2
    exact ⟨⟨c, hc⟩, Subtype.ext ((hcy δ).symm.trans (congrArg Subtype.val hy))⟩
  · have h1 : Nat.card (fixSet Ω S) ≤ 1 := by
      obtain ⟨k, hk⟩ := hG.odd_card_fixSet hS
      omega
    have := Finite.card_le_one_iff_subsingleton.mp h1
    exact ⟨fun δ ε => ⟨1, Subsingleton.elim _ _⟩⟩

theorem IsStarGroup.exists_centralizer_smul_eq_of_mem_fixSet (hG : IsStarGroup G Ω)
    {S : Subgroup G} (hS : IsPGroup 2 S) {β γ : Ω} (hβ : β ∈ fixSet Ω S) (hγ : γ ∈ fixSet Ω S) :
    ∃ c ∈ Subgroup.centralizer (S : Set G), c • β = γ := by
  have := hG.isPretransitive_centralizer hS
  obtain ⟨c, hc⟩ := exists_smul_eq (Subgroup.centralizer (S : Set G)) (⟨β, hβ⟩ : fixSet Ω S)
    ⟨γ, hγ⟩
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

end E4

section Kernel

theorem smul_eq_of_mem_normalCore {K : Subgroup G} {x : G} (hx : x ∈ K.normalCore)
    (c : G ⧸ K) : x • c = c := by
  rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker] at hx
  exact congrArg (fun π : Equiv.Perm (G ⧸ K) => π c) hx

variable [Finite G] [Finite Ω] {α : Ω} {K : Subgroup G}

theorem smul_eq_of_mem_normalCore_of_mem_fixingSubgroup (hG : IsStarGroup G Ω)
    (hK : stabilizer G α ≤ K) {x : G} (hx2 : orderOf x = 2) (hxN : x ∈ K.normalCore)
    (hxB : x ∈ fixingSubgroup G (orbit K α)) (ω : Ω) : x • ω = ω := by
  have := hG.isPretransitive
  have hS : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_zpowers_of_orderOf_eq_two hx2
  obtain ⟨β, hβ, hβω⟩ := exists_mem_fixSet_blockCoset_eq hG.odd_card hK hS
    (c := blockCoset α K ω) fun r hr =>
      Subgroup.zpowers_le.mpr (show x ∈ stabilizer G (blockCoset α K ω) from
        smul_eq_of_mem_normalCore hxN _) hr
  have hαS : α ∈ fixSet Ω (Subgroup.zpowers x) := by
    rw [fixSet_zpowers]
    exact (mem_fixingSubgroup_iff G).mp hxB α (mem_orbit_self α)
  obtain ⟨c, hcx, hc⟩ := hG.exists_centralizer_smul_eq_of_mem_fixSet hS hαS hβ
  have hmem : c⁻¹ • ω ∈ orbit K α := by
    rw [← blockCoset_eq_one_iff hK, blockCoset_smul hK, ← hβω, ← hc, blockCoset_smul hK,
      blockCoset_self hK, inv_smul_smul]
  have hfix : x • (c⁻¹ • ω) = c⁻¹ • ω := (mem_fixingSubgroup_iff G).mp hxB _ hmem
  have hcx' : x * c = c * x := Subgroup.mem_centralizer_iff.mp hcx x (Subgroup.mem_zpowers x)
  calc x • ω = x • (c • (c⁻¹ • ω)) := by rw [smul_inv_smul]
    _ = c • (x • (c⁻¹ • ω)) := by rw [← mul_smul, hcx', mul_smul]
    _ = ω := by rw [hfix, smul_inv_smul]

theorem odd_card_fixingSubgroup_inf_kernel [FaithfulSMul G Ω] (hG : IsStarGroup G Ω)
    (hK : stabilizer G α ≤ K) :
    Odd (Nat.card ↥(fixingSubgroup G (orbit K α) ⊓ K.normalCore)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  rw [Subgroup.orderOf_mk] at hx2
  obtain ⟨hxB, hxN⟩ := Subgroup.mem_inf.mp hx
  have hx1 : x = 1 := eq_of_smul_eq_smul fun ω => by
    rw [one_smul]
    exact smul_eq_of_mem_normalCore_of_mem_fixingSubgroup hG hK hx2 hxN hxB ω
  rw [hx1, orderOf_one] at hx2
  omega

theorem fixingSubgroup_inf_kernel_le_pPrimeCore [FaithfulSMul G Ω] (hG : IsStarGroup G Ω)
    (hK : stabilizer G α ≤ K) :
    fixingSubgroup G (orbit K α) ⊓ K.normalCore ≤ CFSG.pPrimeCore 2 G := by
  have := hG.isPretransitive
  set M := fixingSubgroup G (orbit K α) ⊓ K.normalCore
  set N := K.normalCore
  have hnorm : (M.subgroupOf N).Normal := by
    refine ⟨fun m hm n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨hmB, hmN⟩ := Subgroup.mem_inf.mp hm
    refine Subgroup.mem_inf.mpr ⟨(mem_fixingSubgroup_iff G).mpr fun b hb => ?_,
      N.mul_mem (N.mul_mem n.2 hmN) (N.inv_mem n.2)⟩
    have hnb : (n : G)⁻¹ • b ∈ orbit K α := by
      rw [← blockCoset_eq_one_iff hK, blockCoset_smul hK,
        smul_eq_of_mem_normalCore (N.inv_mem n.2), blockCoset_eq_one_iff hK]
      exact hb
    have h := (mem_fixingSubgroup_iff G).mp hmB _ hnb
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
    rw [h, smul_inv_smul]
  have hcop : Nat.Coprime 2 (Nat.card (M.subgroupOf N)) := by
    rw [← Subgroup.card_map_of_injective N.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left inf_le_right, Nat.coprime_two_left]
    exact odd_card_fixingSubgroup_inf_kernel hG hK
  have hle : M.subgroupOf N ≤ CFSG.pPrimeCore 2 N := le_sSup ⟨hnorm, hcop⟩
  have hMO : M ≤ oddCoreOf N := by
    have h := Subgroup.map_mono (f := N.subtype) hle
    rwa [Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right] at h
  refine hMO.trans (le_sSup ⟨ConjAct.normal_of_characteristic_of_normal, ?_⟩)
  rw [oddCoreOf, Subgroup.card_map_of_injective N.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

end Kernel

end CFSG.Holt.H78
