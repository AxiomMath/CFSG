module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideOrbit
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.AGLEmbedding

variable {Y : Type} [Group Y]

theorem mem_of_mul_pow_mem {L : Subgroup Y} {x zb s : Y} (hxz : x * zb = zb * x)
    (hz3 : zb ^ 3 = 1) (hsz : s * zb = zb * s) (hsx : s * x * s⁻¹ = x⁻¹)
    (hsL : s ∈ Subgroup.normalizer (L : Set Y)) {a : ℕ} (h3a : ¬ 3 ∣ a)
    (hyL : x * zb ^ a ∈ L) : zb ∈ L := by
  have hy' : s * (x * zb ^ a) * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hsL _).mp hyL
  have hy'eq : s * (x * zb ^ a) * s⁻¹ = x⁻¹ * zb ^ a := by
    have hza : s * zb ^ a * s⁻¹ = zb ^ a := by
      rw [(Commute.pow_right (show Commute s zb from hsz) a).eq, mul_inv_cancel_right]
    calc s * (x * zb ^ a) * s⁻¹ = (s * x * s⁻¹) * (s * zb ^ a * s⁻¹) := by group
      _ = x⁻¹ * zb ^ a := by rw [hsx, hza]
  rw [hy'eq] at hy'
  have hprod : x * zb ^ a * (x⁻¹ * zb ^ a) = zb ^ (2 * a) := by
    have hxz' : x * zb ^ a = zb ^ a * x := ((Commute.pow_right hxz a)).eq
    rw [hxz', two_mul, pow_add]
    group
  have h2a : zb ^ (2 * a) ∈ L := hprod ▸ L.mul_mem hyL hy'
  have hmod : (2 * a) * (2 * a) % 3 = 1 := by
    have : a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hzpow : zb = (zb ^ (2 * a)) ^ (2 * a) := by
    rw [← pow_mul, ← Nat.mod_add_div ((2 * a) * (2 * a)) 3, pow_add, pow_mul, hz3, one_pow,
      mul_one, hmod, pow_one]
  rw [hzpow]
  exact L.pow_mem h2a _

variable [Finite Y]

theorem mem_normalizer_of_mem_of_not_mem_centralizer {L : Subgroup Y} (hL : CFSG.IsComponent L)
    {zb t : Y} (htz : t * zb = zb * t) (hzL : zb ∈ L)
    (hzC : zb ∉ Subgroup.centralizer (L : Set Y)) : t ∈ Subgroup.normalizer (L : Set Y) := by
  by_contra hn
  have hne : L.map (MulAut.conj t).toMonoidHom ≠ L := fun h =>
    hn (SPLMSide.mem_normalizer_of_map_conj_eq h)
  have hc := SPLMSide.commute_of_ne hL
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hL) hne
  have hzt : zb ∈ L.map (MulAut.conj t).toMonoidHom :=
    ⟨zb, hzL, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, htz, mul_inv_cancel_right]⟩
  exact hzC (Subgroup.mem_centralizer_iff.mpr fun l hl => hc l hl zb hzt)

theorem eq_bot_or_eq_of_card_nine {X K' : Subgroup Y} {t : Y} (hXcard : Nat.card X = 9)
    (hline : ∀ F : Subgroup Y, F ≤ X → Nat.card F = 3 → t ∉ Subgroup.normalizer (F : Set Y))
    (hK'X : K' ≤ X) (htK' : t ∈ Subgroup.normalizer (K' : Set Y)) : K' = ⊥ ∨ K' = X := by
  have hdvd : Nat.card K' ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hXcard]
    exact Subgroup.card_dvd_of_le hK'X
  obtain ⟨i, hi, hKi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases i
  · rw [pow_zero] at hKi
    exact Or.inl (Subgroup.card_eq_one.mp hKi)
  · exact absurd htK' (hline K' hK'X (by simpa using hKi))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hK'X (by rw [hKi, hXcard]; norm_num))

omit [Finite Y] in
theorem mem_normalizer_centralizer_of_mem_normalizer_ib3 {L : Subgroup Y} {t : Y}
    (htL : t ∈ Subgroup.normalizer (L : Set Y)) :
    t ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc'
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have hc : ∀ h ∈ L, h * c = c * h := Subgroup.mem_centralizer_iff.mp hc'
    have hl' : t⁻¹ * l * t ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htL) l).mp hl
      simpa using this
    have := hc _ hl'
    calc l * (t * c * t⁻¹) = t * ((t⁻¹ * l * t) * c) * t⁻¹ := by group
      _ = t * (c * (t⁻¹ * l * t)) * t⁻¹ := by rw [this]
      _ = t * c * t⁻¹ * l := by group
  · intro hc'
    refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
    have hc : ∀ h ∈ L, h * (t * c * t⁻¹) = (t * c * t⁻¹) * h :=
      Subgroup.mem_centralizer_iff.mp hc'
    have hl' : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL l).mp hl
    have := hc _ hl'
    calc l * c = t⁻¹ * ((t * l * t⁻¹) * (t * c * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * c * t⁻¹) * (t * l * t⁻¹)) * t := by rw [this]
      _ = c * l := by group

theorem le_centralizer_blocks_of_torus {X : Subgroup Y}
    {zb t : Y} (hXcard : Nat.card X = 9)
    (hzX : ∀ x ∈ X, x * zb = zb * x) (hz3 : zb ^ 3 = 1)
    (htX : t ∈ Subgroup.normalizer (X : Set Y)) (htz : t * zb = zb * t)
    (hline : ∀ F : Subgroup Y, F ≤ X → Nat.card F = 3 → t ∉ Subgroup.normalizer (F : Set Y))
    (hinv : ∀ x ∈ X, t ^ 2 * x * (t ^ 2)⁻¹ = x⁻¹)
    (B : Subgroup Y → Prop) (hBc : ∀ L, B L → CFSG.IsComponent L)
    (hBt2 : ∀ L, B L → t ^ 2 ∈ Subgroup.normalizer (L : Set Y))
    (hBz : ∀ L, B L → zb ∉ Subgroup.centralizer (L : Set Y))
    (hBy : ∀ L, B L → ∃ x ∈ X, ∃ a : ℕ, ¬ 3 ∣ a ∧ x * zb ^ a ∈ L)
    (hBa : ∀ L, B L → t ∈ Subgroup.normalizer (L : Set Y) →
      X ⊓ Subgroup.centralizer (L : Set Y) ≠ ⊥) :
    ∀ L, B L → X ≤ Subgroup.centralizer (L : Set Y) := by
  have ht2z : t ^ 2 * zb = zb * t ^ 2 := ((Commute.pow_left htz 2)).eq
  intro L hL
  obtain ⟨x, hx, a, h3a, hyL⟩ := hBy L hL
  have hzL : zb ∈ L := mem_of_mul_pow_mem (hzX x hx) hz3 ht2z (hinv x hx) (hBt2 L hL) h3a hyL
  have htL := mem_normalizer_of_mem_of_not_mem_centralizer (hBc L hL) htz hzL (hBz L hL)
  have hKc := eq_bot_or_eq_of_card_nine hXcard hline inf_le_left
    (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨htX, mem_normalizer_centralizer_of_mem_normalizer_ib3 htL⟩)
  rcases hKc with h | h
  · exact absurd h (hBa L hL htL)
  · exact inf_eq_left.mp h

end CFSG.AGLEmbedding
