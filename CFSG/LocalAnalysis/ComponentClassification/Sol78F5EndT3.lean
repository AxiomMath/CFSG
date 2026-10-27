module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Defs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L51A
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCoreBasic
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Tight

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem tightlyEmbedded_of_centralizer_le {K : Subgroup G} [IsSimpleGroup (K ⧸ pPrimeCore 2 K)]
    (hna : ∃ a b : K ⧸ pPrimeCore 2 K, a * b ≠ b * a)
    (hdih : GorensteinWalter.HasDihedralSylowTwo (K ⧸ pPrimeCore 2 K)) {t : G} (htK : t ∈ K)
    (ht2 : orderOf t = 2) (hCt : centralizer ({t} : Set G) ≤ normalizer (K : Set G)) :
    TightlyEmbedded K := by
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; omega
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  refine ⟨even_of_involution htK htt ht1, fun g hg => ?_⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨i, hi, hi2, hi1⟩ := exists_involution_of_even hodd
  obtain ⟨hiK, hig⟩ := mem_inf.mp hi
  rw [mem_rightConjugate_iff] at hig
  have hi2' : orderOf i = 2 := orderOf_eq_prime (by rw [sq]; exact hi2) hi1
  have hgi2 : orderOf (g * i * g⁻¹) = 2 := by rw [orderOf_conj', hi2']
  obtain ⟨k₁, hk₁K, -, hk₁⟩ := exists_conj_of_involutions (W := ⊥) hna hdih IsPGroup.of_bot
    bot_le hiK htK hi2' ht2 (mem_centralizer_bot _) (mem_centralizer_bot _)
  obtain ⟨k₂, hk₂K, -, hk₂⟩ := exists_conj_of_involutions (W := ⊥) hna hdih IsPGroup.of_bot
    bot_le hig htK hgi2 ht2 (mem_centralizer_bot _) (mem_centralizer_bot _)
  apply hg
  have hu : k₂⁻¹ * g * k₁ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hi' : i = k₁ * t * k₁⁻¹ := by rw [← hk₁]; group
    calc k₂⁻¹ * g * k₁ * t = k₂⁻¹ * (g * (k₁ * t * k₁⁻¹) * g⁻¹) * k₂ * (k₂⁻¹ * g * k₁) := by
          group
      _ = t * (k₂⁻¹ * g * k₁) := by rw [← hi', hk₂]
  rw [show g = k₂ * (k₂⁻¹ * g * k₁) * k₁⁻¹ by group]
  exact mul_mem (mul_mem (le_normalizer hk₂K) (hCt hu)) (inv_mem (le_normalizer hk₁K))

theorem false_of_tightlyEmbedded (h3 : Asc76.Asc76Theorem3Large) [IsSimpleGroup G]
    {a b : G} (hab : a * b ≠ b * a) {K R : Subgroup G} (hTE : TightlyEmbedded K)
    (hK1 : K ≠ ⊥) (hKtop : K ≠ ⊤) (hR : IsSylowOf 2 R K)
    (hRd : AschbacherTheorem3.IsDihedralTwoGroup R) (h4 : 4 < Nat.card R) : False := by
  have hNC : normalClosure (K : Set G) = ⊤ := by
    rcases (normalClosure_normal (s := (K : Set G))).eq_bot_or_eq_top with h | h
    · exact absurd (eq_bot_iff.mpr fun x hx => h ▸ subset_normalClosure hx) hK1
    · exact h
  have hO : standardComponentOddCore G = ⊥ := by
    rcases (inferInstance : (standardComponentOddCore G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have h1 := RankTwoSporadic.odd_card_standardComponentOddCore (G := G)
      rw [h, card_top] at h1
      have h2 := hTE.1
      have h3 : Nat.card K ∣ Nat.card G := card_subgroup_dvd_card K
      exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat h1 h3)) h2
  rcases h3 G K hTE hNC hO R hR hRd h4 with hn | ⟨-, h4', -⟩ | ⟨U, -, -, hUidx, hUab⟩
  · rcases hn.eq_bot_or_eq_top with h | h
    · exact hK1 h
    · exact hKtop h
  · omega
  · rcases (normalClosure_normal (s := (U : Set G))).eq_bot_or_eq_top with h | h
    · have hU : U = ⊥ := eq_bot_iff.mpr fun x hx => h ▸ subset_normalClosure hx
      rw [hU, relIndex_bot_left] at hUidx
      omega
    · apply hab
      have h1 := hUab.1.comm ⟨a, h ▸ mem_top a⟩ ⟨b, h ▸ mem_top b⟩
      exact congrArg Subtype.val h1

end CFSG.ComponentClassification.Sol78.F514
