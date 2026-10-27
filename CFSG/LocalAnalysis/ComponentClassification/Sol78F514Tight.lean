module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingMap
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientChain
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_involution_of_even {X : Subgroup Y} (h : Even (Nat.card X)) :
    ∃ i ∈ X, i * i = 1 ∧ i ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨i, hi⟩, hi2⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (even_iff_two_dvd.mp h)
  rw [Subgroup.orderOf_mk] at hi2
  refine ⟨i, hi, by rw [← sq, ← hi2, pow_orderOf_eq_one], fun h1 => ?_⟩
  rw [h1, orderOf_one] at hi2
  norm_num at hi2

omit [Finite Y] in
theorem even_of_involution {X : Subgroup Y} {i : Y} (hi : i ∈ X) (hi2 : i * i = 1)
    (hi1 : i ≠ 1) : Even (Nat.card X) := by
  have h2 : orderOf i = 2 := orderOf_eq_prime (by rw [sq]; exact hi2) hi1
  have h := Subgroup.orderOf_dvd_natCard X hi
  rw [h2] at h
  exact even_iff_two_dvd.mpr h

omit [Finite Y] in
theorem not_mem_of_odd {N : Subgroup Y} (hN : Odd (Nat.card N)) {i : Y} (hi2 : i * i = 1)
    (hi1 : i ≠ 1) : i ∉ N := fun hiN =>
  (Nat.not_even_iff_odd.mpr hN) (even_of_involution hiN hi2 hi1)

theorem exists_conj_mem_of_isSylowOf {K R : Subgroup Y} (hR : IsSylowOf 2 R K) {i : Y}
    (hiK : i ∈ K) (hi2 : i * i = 1) (hi1 : i ≠ 1) : ∃ k ∈ K, k⁻¹ * i * k ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkK, hk⟩ := FooteLit.exists_conj_le_of_isSylowOf hR (zpowers_le_of_mem hiK)
    (FooteLit.isPGroup_zpowers_of_orderOf (orderOf_eq_prime (by rw [sq]; exact hi2) hi1))
  exact ⟨k, hkK, hk i (mem_zpowers i)⟩

theorem mem_normalizer_of_even {K R : Subgroup Y} (hR : IsSylowOf 2 R K) {c₁ c₂ : Y}
    (hcls : ∀ i ∈ R, i * i = 1 → i ≠ 1 →
      ∃ n ∈ normalizer (K : Set Y), n * i * n⁻¹ = c₁ ∨ n * i * n⁻¹ = c₂)
    (hnc : ∀ g : Y, g * c₁ * g⁻¹ ≠ c₂)
    (hC₁ : centralizer ({c₁} : Set Y) ≤ normalizer (K : Set Y))
    (hC₂ : centralizer ({c₂} : Set Y) ≤ normalizer (K : Set Y)) {x : Y}
    (hx : Even (Nat.card (K ⊓ rightConjugate K x : Subgroup Y))) :
    x ∈ normalizer (K : Set Y) := by
  obtain ⟨i, hi, hi2, hi1⟩ := exists_involution_of_even hx
  obtain ⟨hiK, hixK⟩ := mem_inf.mp hi
  rw [mem_rightConjugate_iff] at hixK
  have hK : ∀ j ∈ K, j * j = 1 → j ≠ 1 →
      ∃ m ∈ normalizer (K : Set Y), m * j * m⁻¹ = c₁ ∨ m * j * m⁻¹ = c₂ := by
    intro j hj hj2 hj1
    obtain ⟨k, hkK, hk⟩ := exists_conj_mem_of_isSylowOf hR hj hj2 hj1
    have hk2 : k⁻¹ * j * k * (k⁻¹ * j * k) = 1 := by
      rw [show k⁻¹ * j * k * (k⁻¹ * j * k) = k⁻¹ * (j * j) * k by group, hj2]; group
    have hk1 : k⁻¹ * j * k ≠ 1 := fun h => hj1 (by
      calc j = k * (k⁻¹ * j * k) * k⁻¹ := by group
        _ = 1 := by rw [h]; group)
    obtain ⟨n, hn, hnc⟩ := hcls _ hk hk2 hk1
    refine ⟨n * k⁻¹, mul_mem hn (inv_mem (le_normalizer hkK)), ?_⟩
    rw [show n * k⁻¹ * j * (n * k⁻¹)⁻¹ = n * (k⁻¹ * j * k) * n⁻¹ by group]
    exact hnc
  have hj2 : x * i * x⁻¹ * (x * i * x⁻¹) = 1 := by
    rw [show x * i * x⁻¹ * (x * i * x⁻¹) = x * (i * i) * x⁻¹ by group, hi2]; group
  have hj1 : x * i * x⁻¹ ≠ 1 := fun h => hi1 (by
    calc i = x⁻¹ * (x * i * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨m₁, hm₁, h₁⟩ := hK i hiK hi2 hi1
  obtain ⟨m₂, hm₂, h₂⟩ := hK _ hixK hj2 hj1
  have hg : ∀ c c', m₁ * i * m₁⁻¹ = c → m₂ * (x * i * x⁻¹) * m₂⁻¹ = c' →
      (m₂ * x * m₁⁻¹) * c * (m₂ * x * m₁⁻¹)⁻¹ = c' := by
    intro c c' h h'
    rw [← h, ← h']
    group
  have hfin : ∀ c, m₁ * i * m₁⁻¹ = c → m₂ * (x * i * x⁻¹) * m₂⁻¹ = c →
      centralizer ({c} : Set Y) ≤ normalizer (K : Set Y) → x ∈ normalizer (K : Set Y) := by
    intro c h h' hC
    have h3 := hg c c h h'
    have hgc : m₂ * x * m₁⁻¹ ∈ centralizer ({c} : Set Y) := by
      rw [mem_centralizer_singleton_iff]
      calc m₂ * x * m₁⁻¹ * c = (m₂ * x * m₁⁻¹) * c * (m₂ * x * m₁⁻¹)⁻¹ * (m₂ * x * m₁⁻¹) := by
            group
        _ = c * (m₂ * x * m₁⁻¹) := by rw [h3]
    have hx' : x = m₂⁻¹ * (m₂ * x * m₁⁻¹) * m₁ := by group
    rw [hx']
    exact mul_mem (mul_mem (inv_mem hm₂) (hC hgc)) hm₁
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact hfin c₁ h₁ h₂ hC₁
  · exact absurd (hg c₁ c₂ h₁ h₂) (hnc _)
  · refine absurd ?_ (hnc (m₂ * x * m₁⁻¹)⁻¹)
    rw [← hg c₂ c₁ h₁ h₂]
    group
  · exact hfin c₂ h₁ h₂ hC₂

section Quotient

variable {N : Subgroup Y} [N.Normal] (hN : Odd (Nat.card N))
include hN

theorem isSylowOf_sup_of_odd {K R : Subgroup Y} (hR : IsSylowOf 2 R K) :
    IsSylowOf 2 R (K ⊔ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hR ⊢
  obtain ⟨hRK, hRp, hdvd⟩ := hR
  refine ⟨hRK.trans le_sup_left, hRp, fun h2 => ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex R K (K ⊔ N) hRK le_sup_left] at h2
  have hodd : Odd (K.relIndex (K ⊔ N)) := by
    rw [sup_comm, relIndex_sup_eq_relIndex_of_normal N K]
    exact Odd.of_dvd_nat hN (Subgroup.relIndex_dvd_card K N)
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hdvd h
  · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem tightlyEmbedded_map_mk {K R : Subgroup Y} (hR : IsSylowOf 2 R K)
    (hReven : Even (Nat.card R))
    (htight : ∀ x : Y, Even (Nat.card (K ⊓ rightConjugate K x : Subgroup Y)) →
      x ∈ normalizer (K : Set Y)) :
    TightlyEmbedded (K.map (QuotientGroup.mk' N)) :=
  RankTwoBender.tightlyEmbedded_map_of_odd_ker _ (QuotientGroup.mk'_surjective N)
    (by rwa [QuotientGroup.ker_mk'])
    ⟨even_iff_two_dvd.2 ((even_iff_two_dvd.1 hReven).trans (Subgroup.card_dvd_of_le hR.le)),
      fun x hx => by
        by_contra hodd
        exact hx (htight x (Nat.not_odd_iff_even.1 hodd))⟩

theorem isSylowOf_map_mk {K R : Subgroup Y} (hR : IsSylowOf 2 R K) :
    IsSylowOf 2 (R.map (QuotientGroup.mk' N)) (K.map (QuotientGroup.mk' N)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRKN := isSylowOf_sup_of_odd hN hR
  rw [isSylowOf_iff] at hR hRKN ⊢
  refine ⟨map_mono hR.1, hR.2.1.map _, fun h2 => hRKN.2.2 ?_⟩
  rw [Subgroup.relIndex_map_map, QuotientGroup.ker_mk'] at h2
  rw [← Subgroup.relIndex_mul_relIndex R (R ⊔ N) (K ⊔ N) le_sup_left
    (sup_le_sup_right hR.1 N)]
  exact h2.mul_left _

end Quotient

end CFSG.ComponentClassification.Sol78.F514
