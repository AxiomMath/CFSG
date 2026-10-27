module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9a
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Pgl

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5 CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G]

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem R_le_L₀ : S ⊓ L ≤ L ⊓ centralizer ({t} : Set G) := fun r hr =>
  mem_inf.mpr ⟨(mem_inf.mp hr).2, mem_centralizer_singleton_iff.mpr (H.sec5.tZ r (mem_inf.mp hr).1)⟩

theorem exists_normal_complement_L₀ :
    ∃ N : Subgroup G, N ≤ L ⊓ centralizer ({t} : Set G) ∧ Odd (Nat.card N) ∧
      (∀ c ∈ centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G), ∀ n ∈ N, c * n * c⁻¹ ∈ N) ∧
      L ⊓ centralizer ({t} : Set G) ≤ N ⊔ (S ⊓ L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L ⊓ centralizer ({t} : Set G) with hL₁
  have hRL : S ⊓ L ≤ L₁ := H.R_le_L₀
  have hRsyl : IsSylowOf 2 (S ⊓ L) L₁ := H.sec5.R_sylow.of_le hRL inf_le_left
  obtain ⟨ρ, b, j, hD, hc⟩ := H.exists_dihData_R
  set p' : ↥L₁ := ⟨ρ, hRL hD.ρ_mem⟩ with hp'
  set b' : ↥L₁ := ⟨b, hRL hD.s_mem⟩ with hb'
  have hop : orderOf p' = orderOf ρ := Subgroup.orderOf_mk _ _
  have D : GSThmB.Nine81.DihData ((S ⊓ L).subgroupOf L₁) p' b' :=
    { hp := mem_subgroupOf.mpr hD.ρ_mem
      hb := mem_subgroupOf.mpr hD.s_mem
      hcard := by
        rw [hop, Nat.card_congr (subgroupOfEquivOfLe hRL).toEquiv]
        exact (card_eq_two_mul hD).symm
      hbp := by
        intro hbz
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hbz
        apply not_mem_zpowers hD
        refine mem_zpowers_iff.mpr ⟨k, ?_⟩
        have h1 := congrArg Subtype.val hk
        rwa [Subgroup.coe_zpow] at h1
      hb2 := Subtype.ext hD.s_sq
      hrel := Subtype.ext (by
        change b * ρ * b⁻¹ = ρ⁻¹
        exact hD.s_conj)
      hp4 := by rw [hop, hD.ord]; exact Nat.le_mul_of_pos_right 4 (by positivity)
      hpow := ⟨j + 2, by rw [hop, hD.ord, pow_add]; ring⟩ }
  obtain ⟨Syl, hSyl⟩ := hRsyl.exists_sylow_eq_subgroupOf
  have hpt : ((p' ^ (orderOf p' / 2) : ↥L₁) : G) = t := by
    rw [Subgroup.coe_pow, hop, hD.ord, show 4 * 2 ^ j / 2 = 2 * 2 ^ j by omega, ← hc,
      DihData.zc, ← zpow_natCast]
    push_cast
    rfl
  obtain ⟨N, hNn, hNc, hNq⟩ := GSThmB.Nine81.hasNormalPComplement_of_dihedral D ⟨Syl, hSyl⟩
    fun x => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hpt]
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2)
  set N' := N.map L₁.subtype with hN'
  have hN'L : N' ≤ L₁ := map_subtype_le N
  have hN'odd : Odd (Nat.card N') := by
    rw [hN', card_map_of_injective L₁.subtype_injective]
    exact Nat.coprime_two_left.mp hNc
  have hodd : ∀ x ∈ L₁, Odd (orderOf x) → x ∈ N' := by
    intro x hx hxo
    refine ⟨⟨x, hx⟩, (QuotientGroup.eq_one_iff _).mp ?_, rfl⟩
    obtain ⟨k, hk⟩ := hNq (QuotientGroup.mk (⟨x, hx⟩ : ↥L₁))
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have h2 : orderOf (QuotientGroup.mk (⟨x, hx⟩ : ↥L₁) : ↥L₁ ⧸ N) ∣ orderOf x := by
      rw [← Subgroup.orderOf_mk x hx]
      exact orderOf_map_dvd (QuotientGroup.mk' N) _
    rcases i with _ | i
    · rw [pow_zero] at hi
      exact orderOf_eq_one_iff.mp hi
    · rw [hi] at h2
      exact absurd (Odd.of_dvd_nat hxo h2)
        (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero i⟩))
  have hconj : ∀ c, (∀ l ∈ L₁, c * l * c⁻¹ ∈ L₁) → ∀ n ∈ N', c * n * c⁻¹ ∈ N' := by
    intro c hc' n hn
    refine hodd _ (hc' n (hN'L hn)) ?_
    rw [orderOf_conj']
    exact Odd.of_dvd_nat hN'odd (Subgroup.orderOf_dvd_natCard N' hn)
  refine ⟨N', hN'L, hN'odd, fun c hcZ n hn => hconj c (fun l hl => ?_) n hn, ?_⟩
  · obtain ⟨hcz, hct⟩ := mem_inf.mp hcZ
    have hcN := H.sec5.centralizer_le_normalizer hcz
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hcN l).mp (mem_inf.mp hl).1, ?_⟩
    have h1 := mem_centralizer_singleton_iff.mp hct
    have h2 := mem_centralizer_singleton_iff.mp (mem_inf.mp hl).2
    have ht' : c⁻¹ * t * c = t := by rw [mul_assoc, ← h1]; group
    rw [mem_centralizer_singleton_iff]
    calc c * l * c⁻¹ * t = c * l * (c⁻¹ * t * c) * c⁻¹ := by group
      _ = c * (l * t) * c⁻¹ := by rw [ht']; group
      _ = c * (t * l) * c⁻¹ := by rw [h2]
      _ = (c * t) * l * c⁻¹ := by group
      _ = t * (c * l * c⁻¹) := by rw [h1]; group
  · have hRN : S ⊓ L ≤ normalizer (N' : Set G) := fun r hr =>
      mem_normalizer_iff.mpr fun n => ⟨fun hn => hconj r (fun l hl =>
        mul_mem (mul_mem (hRL hr) hl) (inv_mem (hRL hr))) n hn, fun hn => by
        have h1 := hconj r⁻¹ (fun l hl => mul_mem (mul_mem (inv_mem (hRL hr)) hl)
          (inv_mem (inv_mem (hRL hr)))) _ hn
        rwa [show r⁻¹ * (r * n * r⁻¹) * r⁻¹⁻¹ = n by group] at h1⟩
    have hdisj : Disjoint N' (S ⊓ L) := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      exact mem_bot.mpr (eq_one_of_mem_isPGroup_of_mem_odd H.sec5.R_sylow.isPGroup hN'odd
        (mem_inf.mp hx).2 (mem_inf.mp hx).1)
    have hcard := GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer N' (S ⊓ L) hRN
      hdisj
    have hle : Nat.card L₁ ≤ Nat.card N' * Nat.card ↥(S ⊓ L) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      obtain ⟨a, ha⟩ := hNq.exists_card_eq
      have h2 : 2 ^ a ∣ Nat.card L₁ := ⟨Nat.card N, by rw [h1, ha]⟩
      have h3 : 2 ^ a ≤ Nat.card ↥(S ⊓ L) := by
        rw [hRsyl.card_eq]
        exact Nat.pow_le_pow_right (by norm_num)
          ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h2)
      rw [h1, ha, hN', card_map_of_injective L₁.subtype_injective, mul_comm]
      exact Nat.mul_le_mul_left _ h3
    have heq : N' ⊔ (S ⊓ L) = L₁ :=
      Subgroup.eq_of_le_of_card_ge (sup_le hN'L hRL) (by rw [hcard]; exact hle)
    exact heq.ge

end Hyp

end CFSG.ComponentClassification.Sol78.F514
