module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWGoursatJ
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJField
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.HandbackPhi6

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.Steinberg.TwistedD4
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
  CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
open scoped MatrixGroups

theorem goursatJ_twisted {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hq5 : 5 ≤ ℓ ^ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσq : ∀ c, σ c = c ^ (ℓ ^ f))
    (hσ : ∀ c, σ.toRingHom (σ.toRingHom (σ.toRingHom c)) = c)
    (D : Subgroup (twistedGroup σ.toRingHom)) (hDs : IsSimpleGroup D)
    (hDc : Nat.card D = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) / 2)
    (hDM : D ≤ invCentGroup σ.toRingHom hσ) (hDJ : D ≤ JTw σ.toRingHom)
    (ν : twistedGroup σ.toRingHom) (hν : ν ∈ invCentGroup σ.toRingHom hσ) :
    ν ∈ JTw σ.toRingHom ∨
      invCentGroup σ.toRingHom hσ ≤ D ⊔ D.map (MulAut.conj ν).toMonoidHom := by
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hcardF : Nat.card (fixedField σ.toRingHom) = ℓ ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hℓ hf hK σ hσq
  have hq2 : 2 ≤ ℓ ^ f := by omega
  have h3 : Module.finrank (fixedField σ.toRingHom) K = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := fixedField σ.toRingHom) (V := K)
    rw [hK, hcardF] at h
    exact (Nat.pow_right_injective hq2 h).symm
  have hodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hcardSL : Nat.card SL(2, fixedField σ.toRingHom) = ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) := by
    rw [CFSG.GorensteinWalter.sl2_card_formula, hcardF]
  have hDc2 : 2 * Nat.card D = Nat.card SL(2, fixedField σ.toRingHom) := by
    rw [hcardSL, hDc]
    have h2 : 2 ∣ ℓ ^ f * ((ℓ ^ f) ^ 2 - 1) := by
      obtain ⟨k, hk⟩ := hodd
      have : (ℓ ^ f) ^ 2 - 1 = 2 * (2 * k * k + 2 * k) := by
        rw [hk]
        have : (2 * k + 1) ^ 2 = 2 * (2 * k * k + 2 * k) + 1 := by ring
        omega
      rw [this]
      exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _
    exact Nat.mul_div_cancel' h2
  have hJcomm : ∀ a b, slLong σ.toRingHom hσ a * slB σ.toRingHom hσ b =
      slB σ.toRingHom hσ b * slLong σ.toRingHom hσ a := fun a b => slLong_comm_slB hσ a b
  exact GoursatJ.goursatJ h3 hK2 (by rw [hcardF]; exact hq5) (slLong σ.toRingHom hσ)
    (slB σ.toRingHom hσ) (slLong_injective hσ) (slB_injective hσ) hJcomm
    (slB_neg_one hσ).symm (JTw σ.toRingHom) (slLong_mem_JTw hσ)
    (fun b => slB_mem_JTw_iff hσ b) D hDs hDc2 hDM hDJ ν hν

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
