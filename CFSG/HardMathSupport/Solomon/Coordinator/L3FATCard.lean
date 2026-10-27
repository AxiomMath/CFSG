module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AEta
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ABridge
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank

theorem card_slPi_quot_true {p f : ℕ} {K : Type} [Field K] (hK : PiField true p f K) :
    Nat.card (↥(slPi true 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi true 3 (p ^ f) K)) *
        Nat.gcd 3 (p ^ f - 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1)) := by
  have := hK.finite
  rw [Nat.card_congr (etaTrue (p ^ f) K).toEquiv, Nat.card_congr (psiO K).symm.toEquiv]
  have h := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := K)
  rw [hK.card] at h
  rw [mul_assoc] at h
  exact h

theorem card_slPi_quot_false {p f : ℕ} {K : Type} [Field K] (hK : PiField false p f K)
    (hq2 : 2 < p ^ f) :
    Nat.card (↥(slPi false 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi false 3 (p ^ f) K)) *
        Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  rw [Nat.card_congr (etaFalse hK hq2).toEquiv, Nat.card_congr (psuO hK.unitary).toEquiv]
  have h := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSU_three_mul hK.unitary
  rw [mul_assoc] at h
  exact h

theorem type_eq_of_mulEquiv {π₁ π₂ : Bool} {p₁ f₁ p₂ f₂ : ℕ} {K₁ K₂ : Type} [Field K₁] [Field K₂]
    (hK₁ : PiField π₁ p₁ f₁ K₁) (hK₂ : PiField π₂ p₂ f₂ K₂) (h₁ : π₁ = false → 2 < p₁ ^ f₁) (h₂ : π₂ = false → 2 < p₂ ^ f₂)
    (e : (↥(slPi π₁ 3 (p₁ ^ f₁) K₁) ⧸ Subgroup.center ↥(slPi π₁ 3 (p₁ ^ f₁) K₁)) ≃*
      (↥(slPi π₂ 3 (p₂ ^ f₂) K₂) ⧸ Subgroup.center ↥(slPi π₂ 3 (p₂ ^ f₂) K₂))) :
    π₁ = π₂ ∧ p₁ ^ f₁ = p₂ ^ f₂ := by
  have hcard := Nat.card_congr e.toEquiv
  have hp₁ := hK₁.prime
  have hp₂ := hK₂.prime
  have hf₁ := hK₁.one_le
  have hf₂ := hK₂.one_le
  cases π₁ <;> cases π₂
  ·
    have c₁ := card_slPi_quot_false hK₁ (h₁ rfl)
    have c₂ := card_slPi_quot_false hK₂ (h₂ rfl)
    refine ⟨rfl, order_psu3_inj hp₁ hp₂ hf₁ hf₂ ?_⟩
    rw [← c₁, ← c₂, hcard]
    ring
  ·
    exfalso
    have c₁ := card_slPi_quot_false hK₁ (h₁ rfl)
    have c₂ := card_slPi_quot_true hK₂
    refine LocalBalance.AutL3Arith.order_psl3_ne_psu3 hp₂ hp₁ hf₂ hf₁ ?_
    rw [← c₁, ← c₂, hcard]
    ring
  ·
    exfalso
    have c₁ := card_slPi_quot_true hK₁
    have c₂ := card_slPi_quot_false hK₂ (h₂ rfl)
    refine LocalBalance.AutL3Arith.order_psl3_ne_psu3 hp₁ hp₂ hf₁ hf₂ ?_
    rw [← c₁, ← c₂, hcard]
    ring
  ·
    have c₁ := card_slPi_quot_true hK₁
    have c₂ := card_slPi_quot_true hK₂
    refine ⟨rfl, order_psl3_inj hp₁ hp₂ hf₁ hf₂ ?_⟩
    rw [← c₁, ← c₂, hcard]
    ring

end CFSG.HardMathSupport.Solomon.Coordinator
