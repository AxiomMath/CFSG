module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L53E

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_centralizer_conj (c x : G) :
    Nat.card (centralizer ({c * x * c⁻¹} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  have h1 : centralizer ({c * x * c⁻¹} : Set G) = conjugate (centralizer ({x} : Set G)) c⁻¹ := by
    ext y
    rw [mem_conjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, inv_inv]
    constructor
    · intro h2
      calc c⁻¹ * y * c * x = c⁻¹ * (y * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * x * c⁻¹) * y) * c := by rw [h2]
        _ = x * (c⁻¹ * y * c) := by group
    · intro h2
      calc y * (c * x * c⁻¹) = c * (c⁻¹ * y * c * x) * c⁻¹ := by group
        _ = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by rw [h2]
        _ = c * x * c⁻¹ * y := by group
  rw [h1, card_conjugate_eq_card]

theorem exists_normalizer_conj_of_isSylowOf {P : Subgroup G} {x y : G}
    (hx : IsSylowOf 2 P (centralizer ({x} : Set G)))
    (hy : IsSylowOf 2 P (centralizer ({y} : Set G))) (hxy : IsConj x y) :
    ∃ b ∈ normalizer (P : Set G), b⁻¹ * x * b = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
  have hle : conjugate P c⁻¹ ≤ centralizer ({c * x * c⁻¹} : Set G) := by
    refine conjugate_le_of_forall fun p hp => mem_centralizer_singleton_iff.mpr ?_
    rw [inv_inv]
    have h1 := mem_centralizer_singleton_iff.mp (hx.le hp)
    calc c * p * c⁻¹ * (c * x * c⁻¹) = c * (p * x) * c⁻¹ := by group
      _ = c * (x * p) * c⁻¹ := by rw [h1]
      _ = c * x * c⁻¹ * (c * p * c⁻¹) := by group
  have hsyl : IsSylowOf 2 (conjugate P c⁻¹) (centralizer ({c * x * c⁻¹} : Set G)) := by
    refine isSylowOf_of_twoPart_le (hx.isPGroup.map _) hle ?_
    rw [card_conjugate_eq_card, hx.card_eq, twoPart, card_centralizer_conj]
  obtain ⟨k, hkC, hk⟩ := exists_conj_eq_of_isSylowOf hy hsyl
  refine ⟨c⁻¹ * k, mem_normalizer_of_conjugate_eq ?_, ?_⟩
  · rw [← UnbalancedLayer.conjugate_conjugate]
    exact hk
  · rw [show (c⁻¹ * k)⁻¹ * x * (c⁻¹ * k) = k⁻¹ * (c * x * c⁻¹) * k by group,
      mul_assoc, ← mem_centralizer_singleton_iff.mp hkC, ← mul_assoc, inv_mul_cancel, one_mul]

theorem isSylowOf_centralizer_of_isConj {P : Subgroup G} {x y : G}
    (hP : IsSylowOf 2 P (centralizer ({x} : Set G))) (hPy : P ≤ centralizer ({y} : Set G))
    (hxy : IsConj x y) : IsSylowOf 2 P (centralizer ({y} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
  refine isSylowOf_of_twoPart_le hP.isPGroup hPy ?_
  rw [hP.card_eq, twoPart, card_centralizer_conj]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
include h

omit [Finite 𝕊] in
theorem isConj_w_mul_t {w A n : G} (hwQ : w ∈ Q) (hw2 : orderOf w = 2) (hwz : w ≠ z)
    (hnw : ∀ y, (∀ s ∈ S, s * y = y * s) → ¬ IsConj w y) (hnS : n ∈ S)
    (hn : n * w * n⁻¹ = w * z) (hA : A ∈ S ⊓ centralizer ({w} : Set G)) (hAQ : A ∉ Q)
    (hAc : IsConj w A) (hAA : A * A = 1) (hinn : actG L ε A ∈ innAut5 𝕊) :
    IsConj w (w * t) := by
  obtain ⟨q, ρ, hqW, -, -, hAe, hk⟩ := h.exists_conj_qt ε hwQ hw2 hwz (mem_inf.mp hA).1
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hA).2) hAA hinn
  have hqQ : q ∈ Q := by
    rcases hqW with hq | hq | hq | hq <;> rw [hq]
    · exact one_mem _
    · exact hwQ
    · exact h.zQ
    · exact mul_mem hwQ h.zQ
  have hρ1 : ρ ≠ 1 := fun h2 => hAQ (by rw [hAe, h2, mul_one]; exact hqQ)
  obtain ⟨k, -, -, hk'⟩ := hk hρ1
  have hwqt : IsConj w (q * t) := hAc.trans (isConj_iff.mpr ⟨k⁻¹, by rw [inv_inv, hk']⟩)
  have hwt : IsConj (w * t) (w * z * t) := isConj_iff.mpr ⟨n, by
    rw [show n * (w * t) * n⁻¹ = n * w * n⁻¹ * (n * t * n⁻¹) by group, hn,
      h.tZ n hnS, mul_inv_cancel_right]⟩
  rcases hqW with hq | hq | hq | hq <;> rw [hq] at hwqt
  · exact (hnw t h.tZ (by rwa [one_mul] at hwqt)).elim
  · exact hwqt
  · exact (hnw _ h.zt_center hwqt).elim
  · exact hwqt.trans hwt.symm

theorem exists_b {w : G}
    (hS₀ : IsSylowOf 2 (S ⊓ centralizer ({w} : Set G)) (centralizer ({w} : Set G)))
    (hwt : IsConj w (w * t)) :
    ∃ b ∈ normalizer ((S ⊓ centralizer ({w} : Set G) : Subgroup G) : Set G),
      b⁻¹ * w * b = w * t := by
  have hle : S ⊓ centralizer ({w} : Set G) ≤ centralizer ({w * t} : Set G) := by
    intro s hs
    refine mem_centralizer_singleton_iff.mpr ?_
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hs).2
    have h2 := h.tZ s (mem_inf.mp hs).1
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  exact exists_normalizer_conj_of_isSylowOf hS₀
    (isSylowOf_centralizer_of_isConj hS₀ hle hwt) hwt

end Sec5

end CFSG.ComponentClassification.Foote5
