module

public import CFSG.Holt.General.Aschbacher73Basic
public import CFSG.Holt.General.Defs

public section

namespace CFSG.Holt.General

open MulAction CFSG.Open

variable {G : Type*} [Group G]

theorem normalClosure_le_fusionZStar {N : Subgroup G} (hN : N.Normal) (hNodd : Odd (Nat.card N))
    {z : G} (hzN : ∀ g : G, g * z * g⁻¹ * z⁻¹ ∈ N) :
    Subgroup.normalClosure {z} ≤ fusionZStar G := by
  have hNO : N ≤ fusionOddCore G := le_sSup ⟨hN, hNodd⟩
  apply Subgroup.normalClosure_le_normal
  rw [Set.singleton_subset_iff, SetLike.mem_coe]
  change QuotientGroup.mk' (fusionOddCore G) z ∈ Subgroup.center (G ⧸ fusionOddCore G)
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : ((g * z * g⁻¹ * z⁻¹ : G) : G ⧸ fusionOddCore G) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hNO (hzN g))
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv] at h1
  rw [QuotientGroup.mk'_apply]
  exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)

theorem conj_mul_inv_mem_oddCoreOf {L : Subgroup G} (hL : L.Normal) {z : G} (hzL : z ∈ L)
    {N : Subgroup G} (hN : N.Normal) (hNodd : Odd (Nat.card N))
    (hzN : ∀ g : G, g * z * g⁻¹ * z⁻¹ ∈ N) (g : G) : g * z * g⁻¹ * z⁻¹ ∈ oddCoreOf L := by
  have hwL : g * z * g⁻¹ * z⁻¹ ∈ L := L.mul_mem (hL.conj_mem z hzL g) (L.inv_mem hzL)
  have hcard : Odd (Nat.card (N.subgroupOf L)) := by
    refine hNodd.of_dvd_nat ?_
    rw [← Subgroup.card_map_of_injective (K := N.subgroupOf L) L.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : N.subgroupOf L ≤ CFSG.pPrimeCore 2 L :=
    le_sSup ⟨hN.subgroupOf L, Nat.coprime_two_left.mpr hcard⟩
  exact Subgroup.mem_map.mpr ⟨⟨_, hwL⟩, hle (Subgroup.mem_subgroupOf.mpr (hzN g)), rfl⟩

theorem isPretransitive_oddCoreOf_of_isolated {G : Type} [Group G] [Finite G] {Ω : Type*}
    [MulAction G Ω] [IsPretransitive G Ω] {z : G} {α : Ω} (hz : orderOf z = 2)
    (hα : ∀ ω : Ω, z • ω = ω ↔ ω = α)
    (hiso : ∀ g : G, Commute z (g * z * g⁻¹) → g * z * g⁻¹ = z) :
    Subgroup.normalClosure {z} ≤ fusionZStar G ∧
      IsPretransitive (oddCoreOf (Subgroup.normalClosure {z})) Ω := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by decide)
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hN, hNodd, hzN⟩ :=
    CFSG.ZStar.glauberman_zStar G z hz1 hzz fun g hg => hiso g hg.symm
  refine ⟨normalClosure_le_fusionZStar hN hNodd hzN, ?_⟩
  have hL : (Subgroup.normalClosure ({z} : Set G)).Normal := Subgroup.normalClosure_normal
  have hzL : z ∈ Subgroup.normalClosure ({z} : Set G) := Subgroup.subset_normalClosure rfl
  have hcom := conj_mul_inv_mem_oddCoreOf hL hzL hN hNodd hzN
  have hYodd : Odd (Nat.card (oddCoreOf (Subgroup.normalClosure ({z} : Set G)))) := by
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective (Subgroup.normalClosure ({z} : Set G)).subtype_injective]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hzα : z⁻¹ • α = α := inv_smul_eq_iff.mpr ((hα α).mpr rfl).symm
  apply isPretransitive_of_forall_smul_mem_orbit hzz hα
  · intro ω
    refine hYodd.of_dvd_nat ?_
    rw [Nat.card_coe_set_eq, ← index_stabilizer]
    exact Subgroup.index_dvd_card _
  · intro ω
    obtain ⟨g, rfl⟩ := exists_smul_eq G α ω
    have hmem : z * g * z⁻¹ * g⁻¹ ∈ oddCoreOf (Subgroup.normalClosure ({z} : Set G)) := by
      have := (oddCoreOf (Subgroup.normalClosure ({z} : Set G))).inv_mem (hcom g)
      rwa [show (g * z * g⁻¹ * z⁻¹)⁻¹ = z * g * z⁻¹ * g⁻¹ by group] at this
    refine ⟨⟨_, hmem⟩, ?_⟩
    change (z * g * z⁻¹ * g⁻¹) • g • α = z • g • α
    rw [smul_smul, show z * g * z⁻¹ * g⁻¹ * g = z * g * z⁻¹ by group, mul_smul, hzα, mul_smul]

end CFSG.Holt.General
