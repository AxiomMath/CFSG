module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcFacts
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTrialityOrient
public import CFSG.HardMathSupport.Dickson.I271.Support.ChevInner
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv isLTwoTwentySeven_of_mulEquiv)

theorem pow_pow_add_mul_eq_of_card {k : Type*} [Field k] [Finite k] {ℓ m : ℕ}
    (hk : Nat.card k = ℓ ^ m) (a b : ℕ) (c : k) : c ^ ℓ ^ (m * a + b) = c ^ ℓ ^ b := by
  have : Fintype k := Fintype.ofFinite k
  have hq : Fintype.card k = ℓ ^ m := by rw [← Nat.card_eq_fintype_card, hk]
  have he : ℓ ^ (m * a + b) = (ℓ ^ m) ^ a * ℓ ^ b := by rw [pow_add, pow_mul]
  rw [he, pow_mul, ← hq, FiniteField.pow_card_pow]

theorem exists_cubic_exponent {p f' : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {K : Type} [Field K]
    (K₀ : Subfield K) [Finite K₀] (hk : Nat.card K₀ = p ^ (3 * f')) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ p ^ (f' * p)) :
    ∃ r : ℕ, (r = 1 ∨ r = 2) ∧ ∀ c : K₀, σ (c : K) = ((c ^ ((p ^ f') ^ r) : K₀) : K) := by
  have hp3' : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : ¬ 3 ∣ p := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
      omega
    omega
  refine ⟨p % 3, hp3', fun c => ?_⟩
  have hpe : f' * p = 3 * f' * (p / 3) + f' * (p % 3) := by
    have := Nat.div_add_mod p 3
    nlinarith [this]
  have h1 := pow_pow_add_mul_eq_of_card (ℓ := p) (m := 3 * f') (k := K₀) hk (p / 3) (f' * (p % 3)) c
  rw [← hpe] at h1
  rw [hσ, SubmonoidClass.coe_pow, ← pow_mul]
  have h2 := congrArg Subtype.val h1
  rw [SubmonoidClass.coe_pow, SubmonoidClass.coe_pow] at h2
  exact h2

section Cubic


theorem chevSimple_graphFixedRootGroup_cubic {p f' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf' : 1 ≤ f') (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f') ^ 3)
    (σ : K ≃+* K) {r : ℕ} (hr : r = 1 ∨ r = 2) (hσ : ∀ c, σ c = c ^ ((p ^ f') ^ r)) :
    IsChevSimple p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      p ∣ Nat.card (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∧
      (p = 3 → ¬ IsLTwoTwentySeven (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  obtain ⟨σ₁, hσ₁, ⟨e⟩⟩ : ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ (p ^ f')) ∧
      Nonempty (graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) := by
    rcases hr with rfl | rfl
    · exact ⟨σ, fun c => by rw [hσ, pow_one], ⟨MulEquiv.refl _⟩⟩
    · have h₁ : ∀ c, σ.symm c = c ^ (p ^ f') := fun c => by
        rw [RingEquiv.symm_apply_eq, hσ, ← pow_mul,
          show p ^ f' * (p ^ f') ^ 2 = (p ^ f') ^ 3 by ring]
        have : Fintype K := Fintype.ofFinite K
        have hq : Fintype.card K = (p ^ f') ^ 3 := by rw [← Nat.card_eq_fintype_card, hK]
        rw [← hq]
        exact (FiniteField.pow_card c).symm
      exact ⟨σ.symm, h₁, exists_mulEquiv_graphFixedRootGroup_inv_D4 K σ σ.symm
        (fun c => σ.apply_symm_apply c)⟩
  have hmodel := excTwistedModel_graphFixedRootGroup TwistTag.D4 hp hf' K hK σ₁ hσ₁
  obtain ⟨hchev, hdvd, h27⟩ := excModel_facts (t := .trialityD4) (by decide) hp2
    (G := graphFixedRootGroup TwistTag.D4 K σ₁.toRingHom) (p := p) (f := f')
    ⟨⟨hp, hf', rfl⟩, hmodel⟩
  refine ⟨isChevSimple_of_mulEquiv e.symm hchev, ?_, fun h hL => h27 h
    (isLTwoTwentySeven_of_mulEquiv e hL)⟩
  rw [Nat.card_congr e.toEquiv]
  exact hdvd

end Cubic

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
