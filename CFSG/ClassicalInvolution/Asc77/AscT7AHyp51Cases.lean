module

public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7A

section Words

variable {G : Type} [Group G] {z u t : G}

theorem pow_eq_pow_mod_two {x : G} (hx : x * x = 1) (n : ℕ) : x ^ n = x ^ (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  rw [pow_add, pow_mul, pow_two, hx, one_pow, mul_one]

theorem word_mul (hzu : Commute z u) (hzt : Commute z t) (hut : Commute u t)
    (a b c a' b' c' : ℕ) :
    (z ^ a * u ^ b * t ^ c) * (z ^ a' * u ^ b' * t ^ c') =
      z ^ (a + a') * u ^ (b + b') * t ^ (c + c') := by
  have h1 : t ^ c * z ^ a' = z ^ a' * t ^ c := (hzt.symm.pow_pow c a').eq
  have h2 : t ^ c * u ^ b' = u ^ b' * t ^ c := (hut.symm.pow_pow c b').eq
  have h3 : u ^ b * z ^ a' = z ^ a' * u ^ b := (hzu.symm.pow_pow b a').eq
  calc (z ^ a * u ^ b * t ^ c) * (z ^ a' * u ^ b' * t ^ c')
      = z ^ a * u ^ b * (t ^ c * z ^ a') * u ^ b' * t ^ c' := by simp only [mul_assoc]
    _ = z ^ a * u ^ b * (z ^ a' * t ^ c) * u ^ b' * t ^ c' := by rw [h1]
    _ = z ^ a * (u ^ b * z ^ a') * t ^ c * u ^ b' * t ^ c' := by simp only [mul_assoc]
    _ = z ^ a * (z ^ a' * u ^ b) * t ^ c * u ^ b' * t ^ c' := by rw [h3]
    _ = z ^ a * z ^ a' * u ^ b * (t ^ c * u ^ b') * t ^ c' := by simp only [mul_assoc]
    _ = z ^ a * z ^ a' * u ^ b * (u ^ b' * t ^ c) * t ^ c' := by rw [h2]
    _ = z ^ (a + a') * u ^ (b + b') * t ^ (c + c') := by
      rw [pow_add, pow_add, pow_add]
      simp only [mul_assoc]

theorem mem_closure_words (hz : z * z = 1) (hu : u * u = 1) (ht : t * t = 1)
    (hzu : Commute z u) (hzt : Commute z t) (hut : Commute u t) {x : G}
    (hx : x ∈ Subgroup.closure ({z, u, t} : Set G)) :
    ∃ a b c : ℕ, x = z ^ a * u ^ b * t ^ c := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, c, rfl⟩ := hx
    obtain ⟨a', b', c', rfl⟩ := hy
    exact ⟨a + a', b + b', c + c', word_mul hzu hzt hut a b c a' b' c'⟩
  | inv x _ hx =>
    obtain ⟨a, b, c, rfl⟩ := hx
    refine ⟨a, b, c, inv_eq_of_mul_eq_one_right ?_⟩
    rw [word_mul hzu hzt hut, ← two_mul, ← two_mul, ← two_mul, pow_mul, pow_mul, pow_mul,
      pow_two, pow_two, pow_two, hz, hu, ht]
    simp

end Words

end T7A

section Cases

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]

theorem twinFrameHyp51_of_cases (hz : TwinFrameHyp51z p f) (ht : TwinFrameHyp51t p f)
    (hu : TwinFrameHyp51u p f) : TwinFrameHyp51 p f := by
  intro G _ _ _ Ω K K' J z u t hs
  have hfr := hs.frame
  have hcg := hfr.comm_gen hs.odd hs.hyp
  have hzu : Commute z u := hcg z (by simp) u (by simp)
  have hzt : Commute z t := hcg z (by simp) t (by simp)
  have hut : Commute u t := hcg u (by simp) t (by simp)
  have hz2 : z * z = 1 := hfr.hz.sq
  have hu2 : u * u = 1 := hfr.hu2
  have ht2 : t * t = 1 := hfr.ht.sq
  refine ⟨twinFrame_isElemAbelian hs.odd hs.hyp hfr,
    twinFrame_natCard_eight hs.odd hs.five hs.hyp hfr, ?_⟩
  intro c hc hc1
  obtain ⟨a, b, d, rfl⟩ := T7A.mem_closure_words hz2 hu2 ht2 hzu hzt hut hc
  have hz' := hz G Ω K K' J z u t hs
  have ht' := ht G Ω K K' J z u t hs
  have hu' := hu G Ω K K' J z u t hs
  rw [T7A.pow_eq_pow_mod_two hz2 a, T7A.pow_eq_pow_mod_two hu2 b,
    T7A.pow_eq_pow_mod_two ht2 d] at hc1 ⊢
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;> rw [ha, hb, hd] at hc1 ⊢
  · exact absurd (by simp) hc1
  · simpa using ht'.1
  · simpa using hu'.1
  · simpa [hut.eq] using hu'.2.2.1
  · simpa using hz'
  · simpa [hzt.eq] using ht'.2
  · simpa [hzu.eq] using hu'.2.1
  · have e : z * u * t = u * t * z := by
      calc z * u * t = u * z * t := by rw [hzu.eq]
        _ = u * (z * t) := by rw [mul_assoc]
        _ = u * (t * z) := by rw [hzt.eq]
        _ = u * t * z := by rw [mul_assoc]
    simpa [e] using hu'.2.2.2

end Cases

end CFSG.ClassicalInvolution.Asc77
