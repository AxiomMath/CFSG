module

public import CFSG.GH74.BNPair.RootGroups

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

@[expose] def Rt (n : ℕ) (p : ℤ) : ℤ :=
  if p % (2 * (n : ℤ)) < n then p % (2 * (n : ℤ)) + 1 else -(p % (2 * (n : ℤ)) - n + 1)

theorem Rt_congr {n : ℕ} {p p' : ℤ} (h : p % (2 * (n : ℤ)) = p' % (2 * (n : ℤ))) :
    Rt n p = Rt n p' := by
  unfold Rt
  rw [h]

theorem Rt_add_mul (n : ℕ) (p k : ℤ) : Rt n (p + 2 * (n : ℤ) * k) = Rt n p :=
  Rt_congr (Int.add_mul_emod_self_left _ _ _)

theorem Rt_of_lt {n : ℕ} {p : ℤ} (h0 : 0 ≤ p) (h1 : p < n) : Rt n p = p + 1 := by
  have h2 : p % (2 * (n : ℤ)) = p := Int.emod_eq_of_lt h0 (by omega)
  unfold Rt
  rw [h2, ite_eq_left h1]

theorem Rt_of_ge {n : ℕ} {p : ℤ} (h0 : (n : ℤ) ≤ p) (h1 : p < 2 * (n : ℤ)) :
    Rt n p = -(p - n + 1) := by
  have h2 : p % (2 * (n : ℤ)) = p := Int.emod_eq_of_lt (by omega) h1
  unfold Rt
  rw [h2, ite_eq_right (by omega)]

theorem Rt_of_neg {n : ℕ} {p : ℤ} (h0 : -(n : ℤ) ≤ p) (h1 : p < 0) : Rt n p = -(p + n + 1) := by
  have := Rt_add_mul n p 1
  rw [mul_one] at this
  rw [← this, Rt_of_ge (by omega) (by omega)]
  ring

theorem Rt_isRoot {n : ℕ} (hn : 0 < n) (p : ℤ) : IsRoot n (Rt n p) := by
  have h0 := Int.emod_nonneg p (show (2 * (n : ℤ)) ≠ 0 by omega)
  have h1 := Int.emod_lt_of_pos p (show 0 < 2 * (n : ℤ) by omega)
  unfold IsRoot Rt
  split_ifs with h <;> refine ⟨by omega, by omega⟩


section Conj

variable {X : Type*} [Group X]

theorem mem_of_conjBy_inv {m x : X} {A B : Subgroup X} (h : conjBy m⁻¹ A = B) (hx : x ∈ A) :
    m * x * m⁻¹ ∈ B := by
  rw [← h]
  exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

end Conj

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

@[expose] def ActsPos (m : X) (f : ℤ → ℤ) : Prop :=
  ∀ q : ℤ, ∀ x ∈ D.root (Rt n q), m * x * m⁻¹ ∈ D.root (Rt n (f q))

variable {D}

theorem ActsPos.mul {m m' : X} {f g : ℤ → ℤ} (hm : D.ActsPos m f) (hm' : D.ActsPos m' g) :
    D.ActsPos (m * m') (fun q => f (g q)) := by
  intro q x hx
  have := hm (g q) _ (hm' q x hx)
  have e : m * (m' * x * m'⁻¹) * m⁻¹ = m * m' * x * (m * m')⁻¹ := by group
  rwa [e] at this

theorem ActsPos.one : D.ActsPos (1 : X) id := by
  intro q x hx
  simpa using hx

theorem ActsPos.of_mk_eq {c m : D.N} {f : ℤ → ℤ} (hc : D.ActsPos (c : X) f)
    (hcm : (c : D.Weyl) = (m : D.Weyl)) (hn : 0 < n) : D.ActsPos (m : X) f := by
  intro q x hx
  have hB : (c : X)⁻¹ * m ∈ D.B := mk_eq_mk_iff.1 hcm
  have hN : (c : X)⁻¹ * m ∈ D.N := D.N.mul_mem (D.N.inv_mem c.2) m.2
  have h1 := D.roots.invariant (Rt n q) (Rt_isRoot hn q) ((c : X)⁻¹ * m) ⟨hB, hN⟩ x hx
  have h2 := hc q _ h1
  have e : (c : X) * (((c : X)⁻¹ * m) * x * ((c : X)⁻¹ * m)⁻¹) * (c : X)⁻¹ =
      (m : X) * x * (m : X)⁻¹ := by group
  rwa [e] at h2

theorem lift₁_inv (m : D.N) (hm : (m : D.Weyl) = D.w₁) : ((m⁻¹ : D.N) : D.Weyl) = D.w₁ := by
  rw [QuotientGroup.mk_inv, hm]
  exact inv_eq_of_mul_eq_one_right D.w₁_mul_self

theorem lift₂_inv (m : D.N) (hm : (m : D.Weyl) = D.w₂) : ((m⁻¹ : D.N) : D.Weyl) = D.w₂ := by
  rw [QuotientGroup.mk_inv, hm]
  exact inv_eq_of_mul_eq_one_right D.w₂_mul_self

theorem actsPos_lift₁ (m : D.N) (hm : (m : D.Weyl) = D.w₁) :
    D.ActsPos (m : X) (fun q => (n : ℤ) - q) := by
  have hn := D.three_le
  obtain ⟨a1, a2, a3⟩ := D.roots.action₁ (m⁻¹) (lift₁_inv m hm)
  have hinv : ((m⁻¹ : D.N) : X) = (m : X)⁻¹ := by simp
  rw [hinv] at a1 a2 a3
  intro q x hx
  set v := q % (2 * (n : ℤ)) with hv
  have hv0 : 0 ≤ v := Int.emod_nonneg q (by omega)
  have hv1 : v < 2 * (n : ℤ) := Int.emod_lt_of_pos q (by omega)
  have hq : Rt n q = Rt n v := Rt_congr (by rw [hv, Int.emod_emod])
  have hq' : Rt n ((n : ℤ) - q) = Rt n ((n : ℤ) - v) :=
    Rt_congr (by rw [Int.sub_emod, Int.sub_emod (n : ℤ) v, hv, Int.emod_emod])
  rw [hq] at hx
  rw [hq']
  rcases Int.lt_trichotomy v 0 with h | h | h
  · omega
  · rw [h] at hx ⊢
    rw [Rt_of_lt (le_refl 0) (by omega)] at hx
    rw [sub_zero, Rt_of_ge (le_refl _) (by omega)]
    have := mem_of_conjBy_inv a1 hx
    simpa using this
  · rcases lt_trichotomy v n with h' | h' | h'
    ·
      rw [Rt_of_lt (by omega) h'] at hx
      rw [Rt_of_lt (by omega) (by omega)]
      have := mem_of_conjBy_inv (a3 (v + 1) (by omega) (by omega)).1 hx
      convert this using 2
      ring
    · rw [h'] at hx ⊢
      rw [Rt_of_ge (le_refl _) (by omega)] at hx
      rw [sub_self, Rt_of_lt (le_refl 0) (by omega)]
      have hx' : x ∈ D.root (-1) := by
        convert hx using 2
        ring
      have := mem_of_conjBy_inv a2 hx'
      simpa using this
    ·
      rw [Rt_of_ge h'.le hv1] at hx
      rw [Rt_of_neg (by omega) (by omega)]
      have := mem_of_conjBy_inv (a3 (v - n + 1) (by omega) (by omega)).2 hx
      convert this using 2
      ring

theorem actsPos_lift₂ (m : D.N) (hm : (m : D.Weyl) = D.w₂) :
    D.ActsPos (m : X) (fun q => (n : ℤ) - 2 - q) := by
  have hn := D.three_le
  obtain ⟨b1, b2, b3⟩ := D.roots.action₂ (m⁻¹) (lift₂_inv m hm)
  have hinv : ((m⁻¹ : D.N) : X) = (m : X)⁻¹ := by simp
  rw [hinv] at b1 b2 b3
  intro q x hx
  set v := q % (2 * (n : ℤ)) with hv
  have hv0 : 0 ≤ v := Int.emod_nonneg q (by omega)
  have hv1 : v < 2 * (n : ℤ) := Int.emod_lt_of_pos q (by omega)
  have hq : Rt n q = Rt n v := Rt_congr (by rw [hv, Int.emod_emod])
  have hq' : Rt n ((n : ℤ) - 2 - q) = Rt n ((n : ℤ) - 2 - v) :=
    Rt_congr (by rw [Int.sub_emod, Int.sub_emod ((n : ℤ) - 2) v, hv, Int.emod_emod])
  rw [hq] at hx
  rw [hq']
  by_cases h1 : v ≤ (n : ℤ) - 2
  ·
    rw [Rt_of_lt hv0 (by omega)] at hx
    rw [Rt_of_lt (by omega) (by omega)]
    have := mem_of_conjBy_inv (b3 (v + 1) (by omega) (by omega)).1 hx
    convert this using 2
    ring
  by_cases h2 : v = (n : ℤ) - 1
  · rw [h2, Rt_of_lt (by omega) (by omega)] at hx
    rw [h2, Rt_of_neg (by omega) (by omega)]
    have hx' : x ∈ D.root (n : ℤ) := by
      convert hx using 2
      ring
    have := mem_of_conjBy_inv b1 hx'
    convert this using 2
    ring
  by_cases h3 : v = 2 * (n : ℤ) - 1
  · rw [h3, Rt_of_ge (by omega) (by omega)] at hx
    rw [h3, show (n : ℤ) - 2 - (2 * (n : ℤ) - 1) = ((n : ℤ) - 1) + 2 * (n : ℤ) * (-1) by ring,
      Rt_add_mul, Rt_of_lt (by omega) (by omega)]
    have hx' : x ∈ D.root (-(n : ℤ)) := by
      convert hx using 2
      ring
    have := mem_of_conjBy_inv b2 hx'
    convert this using 2
    ring
  ·
    rw [Rt_of_ge (by omega) hv1] at hx
    rw [Rt_of_neg (by omega) (by omega)]
    have := mem_of_conjBy_inv (b3 (v - n + 1) (by omega) (by omega)).2 hx
    convert this using 2
    ring

end RankTwoSystem

end CFSG.GH74.BNPair
