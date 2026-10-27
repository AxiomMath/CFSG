module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoToral

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.GH74.GLS.Stage2.Bender.Thm1 (A2Core)

theorem a2Core_two {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq : (2 ^ f) % 3 = 1) {d : Kˣ} (hfix : Units.map σ.toRingHom.toMonoidHom d = d)
    (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) : A2Core σ d (2 ^ f) :=
  ⟨Nat.le_self_pow (by omega) 2, hK, hσ, hq,
    map_twistedGroup_eq_graphFixedRootGroup_two hf hK σ hσ, hfix, hd3, hd1⟩

theorem a2Core_of_frame_two {f : ℕ} (hf : 1 ≤ f) (hq : (2 ^ f) % 3 = 2) {K₄ : Type} [Field K₄]
    [Finite K₄] (hK₄ : Nat.card K₄ = ((2 ^ f) ^ 4) ^ 3) {σ₄ : K₄ ≃+* K₄}
    (hσ₄ : ∀ c, σ₄ c = c ^ ((2 ^ f) ^ 4)) {b : K₄ˣ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) :
    A2Core σ₄ b ((2 ^ f) ^ 4) := by
  have h4 : (2 ^ f) ^ 4 = 2 ^ (f * 4) := (pow_mul 2 f 4).symm
  have hmod : (2 ^ (f * 4)) % 3 = 1 := by rw [← h4, Nat.pow_mod, hq]
  rw [h4] at hK₄ hσ₄ ⊢
  refine a2Core_two (by omega) hK₄ hσ₄ hmod ?_ hb3 hb1
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ (f * 4) = 3 * k + 1 := ⟨2 ^ (f * 4) / 3, by omega⟩
  apply Units.ext
  change σ₄ (b : K₄) = (b : K₄)
  rw [hσ₄, ← Units.val_pow_eq_pow_val, hk, pow_succ, pow_mul, hb3, one_pow, one_mul]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
