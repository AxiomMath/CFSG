module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74XShape

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ}

theorem card_centralizer_mul_spinJ₂ (hF4 : F4) (hA3 : A3) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) {a b : spinGroup (quadOdd 3 K)}
    (ha : a ∈ spinJ₁ K) (hb : b ∈ spinJ₂ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hap : a ^ p = 1)
    (hbp : b ^ p = 1) :
    Nat.card ↥(centralizer ({a * b} : Set (spinGroup (quadOdd 3 K)))) ≤
      4 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1) := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨-, -, h33, h34⟩ := hA3 K hodd
  obtain ⟨g, hg, c, hc, hga⟩ := h33 a ha ha1 (by rw [ringChar_eq hp hK]; exact hap)
  obtain ⟨h, hh, d, hd, hhb⟩ := h34 b hb hb1 (by rw [ringChar_eq hp hK]; exact hbp)
  have hha : h * a = a * h := (commute_spinJ₁_spinJ₂ ha hh).symm
  have hgb : g * (h * b * h⁻¹) * g⁻¹ = h * b * h⁻¹ := by
    rw [commute_spinJ₁_spinJ₂ hg (mul_mem (mul_mem hh hb) (inv_mem hh)), mul_inv_cancel_right]
  have hconj : (g * h) * (a * b) * (g * h)⁻¹ = shortSeven K (upperSL2 c) *
      (oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true (upperSL2 d) := by
    calc (g * h) * (a * b) * (g * h)⁻¹ = g * (h * a) * b * h⁻¹ * g⁻¹ := by group
      _ = g * (a * h) * b * h⁻¹ * g⁻¹ := by rw [hha]
      _ = (g * a * g⁻¹) * (g * (h * b * h⁻¹) * g⁻¹) := by group
      _ = (g * a * g⁻¹) * (h * b * h⁻¹) := by rw [hgb]
      _ = _ := by rw [hga, hhb]
  rw [← card_centralizer_conj' (g * h), hconj]
  exact hF4 K hodd (hK ▸ h5) c d hc hd

theorem card_centralizer_mul (hF4 : F4) (hA3 : A3) {i : spinGroup (quadOdd 3 K)}
    (hI : IsIBar K i) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f)
    {a b : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K) (hb : b ∈ spinJ₂ K ∨ b ∈ spinJ₃ K)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hap : a ^ p = 1) (hbp : b ^ p = 1) :
    Nat.card ↥(centralizer ({a * b} : Set (spinGroup (quadOdd 3 K)))) ≤
      4 * Nat.card K ^ 7 * (Nat.card K ^ 2 - 1) := by
  rcases hb with hb | hb
  · exact card_centralizer_mul_spinJ₂ hF4 hA3 hp hp2 hK h5 ha hb ha1 hb1 hap hbp
  · have hb' : i * b * i⁻¹ ∈ spinJ₂ K := hI.conj_mem_spinJ₂ hp hp2 hK h5 hb
    have hb1' : i * b * i⁻¹ ≠ 1 := fun h => hb1 (by
      calc b = i⁻¹ * (i * b * i⁻¹) * i := by group
        _ = 1 := by rw [h]; group)
    have hbp' : (i * b * i⁻¹) ^ p = 1 := by rw [conj_pow, hbp, mul_one, mul_inv_cancel]
    have hia : i * a * i⁻¹ = a := by rw [hI.commute_J₁ a ha, mul_inv_cancel_right]
    have e : i * (a * b) * i⁻¹ = a * (i * b * i⁻¹) := by
      calc i * (a * b) * i⁻¹ = (i * a * i⁻¹) * (i * b * i⁻¹) := by group
        _ = a * (i * b * i⁻¹) := by rw [hia]
    rw [← card_centralizer_conj' i, e]
    exact card_centralizer_mul_spinJ₂ hF4 hA3 hp hp2 hK h5 ha hb' ha1 hb1' hap hbp'

theorem spinFacts_of (hF1 : F1) (hF2b : F2b) (hF4 : F4) (hA1 : A1) (hA2 : A2) (hA3 : A3)
    (hA4 : A4) (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) :
    SpinFacts K p := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  obtain ⟨i, hI⟩ := exists_isIBar hA1 hodd
  obtain ⟨h31, h32, -, -⟩ := hA3 K hodd
  refine ⟨qThree_pow_p hp hK, qThree_ne_one', ?_, fun y hy hy1 hyp => h32 y hy hy1 (by
    rw [ringChar_eq hp hK]; exact hyp), fun y hy hy1 hyp => h31 y hy hy1 (by
    rw [ringChar_eq hp hK]; exact hyp), fun a ha b hb ha1 hb1 hap hbp =>
    card_centralizer_mul hF4 hA3 hI hp hp2 hK h5 ha hb ha1 hb1 hap hbp, ⟨i, ?_⟩⟩
  · rw [card_centralizer_inf hA2 hp hp2 hK h5, card_spinJ₂, card_spinJ₃]
    exact le_of_eq (by ring)
  · exact ⟨hI.mul_self, hI.commute_J₁, hI.conj_t, hI.card_M hp hp2 hK h5,
      fun w hw hww hwt => hI.conj_M hA2 hp hp2 hK h5 hw hww hwt,
      fun l hl => shape hF1 hF2b hA2 hA3 hI hp hp2 hK h5 hl,
      exists_sylowFacts hF1 hA2 hA4 hI hp hp2 hK h5⟩

end Model

theorem spinFactsAll_of (hF1 : F1) (hF2b : F2b) (hF4 : F4) (hA1 : A1) (hA2 : A2) (hA3 : A3)
    (hA4 : A4) : SpinFactsAll := fun _ _ _ _ _ hp hp2 hK h5 =>
  spinFacts_of hF1 hF2b hF4 hA1 hA2 hA3 hA4 hp hp2 hK h5

end CFSG.ComponentClassification.HarrisLit.T1.S74
