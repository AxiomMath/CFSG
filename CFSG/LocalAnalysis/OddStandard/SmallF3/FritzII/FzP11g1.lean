module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzY11b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AS81 CFSG.ABGLocalTools CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G} {T R : Subgroup G}

private theorem fz_q8_sq :
    ∀ g : QuaternionGroup 2, g ^ 2 = 1 ∨ g ^ 2 = QuaternionGroup.a 2 := by
  decide +kernel

private theorem fz_q8_commutator :
    ∀ g h : QuaternionGroup 2,
      g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = QuaternionGroup.a 2 := by
  decide +kernel

private theorem fz_q8_involution :
    ∀ g : QuaternionGroup 2, g ^ 2 = 1 → g = 1 ∨ g = QuaternionGroup.a 2 := by
  decide +kernel

private theorem fz_card_map_mul_card_inf_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (H : Subgroup X) : Nat.card ↥(H.map f) * Nat.card ↥(H ⊓ f.ker) = Nat.card ↥H := by
  have h := Subgroup.relIndex_mul_card (H := f.ker) (K := H)
  rw [Subgroup.relIndex_ker, inf_comm] at h
  exact h

theorem fz_g_q8_facts (hz : orderOf z = 2) (hR : Nonempty (R ≃* QuaternionGroup 2))
    (hzR : z ∈ R) :
    Nat.card R = 8 ∧ (∀ x ∈ R, x ^ 2 ∈ zpowers z) ∧
      ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
  obtain ⟨e⟩ := hR
  have hcard : Nat.card R = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hgz : e ⟨z, hzR⟩ ≠ 1 := by
    intro h
    have h1 : (⟨z, hzR⟩ : R) = 1 := e.injective (by rw [h, map_one])
    have hz1 : z = 1 := by simpa using congrArg Subtype.val h1
    rw [hz1, orderOf_one] at hz
    exact (by decide : (1 : ℕ) ≠ 2) hz
  have hz2G : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hz2R : (⟨z, hzR⟩ : R) ^ 2 = 1 := Subtype.ext (by simpa using hz2G)
  have he2 : e ⟨z, hzR⟩ ^ 2 = 1 := by
    rw [← map_pow, hz2R, map_one]
  have heq_a2 : e ⟨z, hzR⟩ = QuaternionGroup.a 2 := by
    rcases fz_q8_involution (e ⟨z, hzR⟩) he2 with h | h
    · exact absurd h hgz
    · exact h
  refine ⟨hcard, ?_, ?_⟩
  · intro x hx
    have hx2 : x ^ 2 ∈ R := by
      rw [pow_two]
      exact R.mul_mem hx hx
    have hxpow : (⟨x ^ 2, hx2⟩ : R) = ⟨x, hx⟩ ^ 2 := Subtype.ext rfl
    have hmem : (⟨x ^ 2, hx2⟩ : R) = 1 ∨ (⟨x ^ 2, hx2⟩ : R) = ⟨z, hzR⟩ := by
      rcases fz_q8_sq (e ⟨x, hx⟩) with h | h
      · left
        apply e.injective
        rw [hxpow, map_pow, h, map_one]
      · right
        apply e.injective
        rw [hxpow, map_pow, h, heq_a2]
    rcases hmem with h | h
    · have : x ^ 2 = 1 := congrArg Subtype.val h
      rw [this]
      exact one_mem _
    · have : x ^ 2 = z := congrArg Subtype.val h
      rw [this]
      exact Subgroup.mem_zpowers z
  · intro x hx y hy
    have hxy : x * y * x⁻¹ * y⁻¹ ∈ R :=
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)
    have hxypow : (⟨x * y * x⁻¹ * y⁻¹, hxy⟩ : R) =
        ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ := Subtype.ext rfl
    have hmem : (⟨x * y * x⁻¹ * y⁻¹, hxy⟩ : R) = 1 ∨
        (⟨x * y * x⁻¹ * y⁻¹, hxy⟩ : R) = ⟨z, hzR⟩ := by
      rcases fz_q8_commutator (e ⟨x, hx⟩) (e ⟨y, hy⟩) with h | h
      · left
        apply e.injective
        rw [hxypow]
        simpa only [map_mul, map_inv, map_one] using h
      · right
        apply e.injective
        rw [hxypow, heq_a2]
        simpa only [map_mul, map_inv, map_one] using h
    rcases hmem with h | h
    · have : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h
      rw [this]
      exact one_mem _
    · have : x * y * x⁻¹ * y⁻¹ = z := congrArg Subtype.val h
      rw [this]
      exact Subgroup.mem_zpowers z

theorem fz_bar_sylow (hT : FzSylow T) (hTz : T ≤ centralizer ({z} : Set G)) :
    IsSylowOf 2 (fzBar z T) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ (T.subgroupOf (centralizer ({z} : Set G))).index := by
    change ¬ 2 ∣ (T.comap (centralizer ({z} : Set G)).subtype).index
    rw [Subgroup.index_comap (H := T) (f := (centralizer ({z} : Set G)).subtype),
      Subgroup.range_subtype]
    exact fun h2 => hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTz))
  rw [isSylowOf_iff]
  refine ⟨le_top, ?_, ?_⟩
  · exact (hT.1.comap_subtype).map (QuotientGroup.mk' (zpowers (zC z)))
  · rw [Subgroup.relIndex_top_right]
    intro h2
    exact hodd (h2.trans (Subgroup.index_map_dvd
      (H := T.subgroupOf (centralizer ({z} : Set G)))
      (QuotientGroup.mk'_surjective (zpowers (zC z)))))

theorem fz_bar_card (hz : orderOf z = 2) (hR : Nonempty (R ≃* QuaternionGroup 2))
    (hzR : z ∈ R) (hRC : R ≤ centralizer ({z} : Set G)) : Nat.card (fzBar z R) = 4 := by
  obtain ⟨hcardR, -, -⟩ := fz_g_q8_facts hz hR hzR
  have hcardSub : Nat.card (R.subgroupOf (centralizer ({z} : Set G))) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv, hcardR]
  have hker : (QuotientGroup.mk' (zpowers (zC z))).ker = zpowers (zC z) :=
    QuotientGroup.ker_mk' _
  have hinf : R.subgroupOf (centralizer ({z} : Set G)) ⊓ zpowers (zC z) = zpowers (zC z) :=
    inf_eq_right.mpr (zpowers_le.mpr (mem_subgroupOf.mpr hzR))
  have hcardZ : Nat.card (zpowers (zC z)) = 2 := by
    rw [Nat.card_zpowers]
    have h1 := Subgroup.orderOf_coe (zC z)
    rw [← h1]
    change orderOf z = 2
    exact hz
  have hmain := fz_card_map_mul_card_inf_ker (QuotientGroup.mk' (zpowers (zC z)))
    (R.subgroupOf (centralizer ({z} : Set G)))
  rw [hker, hinf, hcardZ, hcardSub] at hmain
  have hmain' : Nat.card (fzBar z R) * 2 = 8 := hmain
  omega

theorem fz_bar_elemAbelian (hz : orderOf z = 2) (hR : Nonempty (R ≃* QuaternionGroup 2))
    (hzR : z ∈ R) (hRC : R ≤ centralizer ({z} : Set G)) : IsElemAbelian 2 (fzBar z R) := by
  obtain ⟨-, hsq, hcomm⟩ := fz_g_q8_facts hz hR hzR
  refine ⟨?_, ?_⟩
  · refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro a ⟨r, hr, rfl⟩ b ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul]
    simp only [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, mem_zpowers_zC]
    simpa [mul_assoc] using hcomm ((s : G)⁻¹) (R.inv_mem (mem_subgroupOf.mp hs))
      ((r : G)⁻¹) (R.inv_mem (mem_subgroupOf.mp hr))
  · intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [← map_pow]
    simp only [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff, mem_zpowers_zC]
    simpa using hsq (r : G) (mem_subgroupOf.mp hr)

end CFSG.OddStandard.SmallF3.FritzII
