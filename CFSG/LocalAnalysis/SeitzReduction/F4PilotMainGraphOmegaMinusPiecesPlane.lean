module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix

variable {k : Type} [Field k]

section Classify

@[expose] def anisoNorm (b c : k) (w : Fin 2 → k) : k :=
  w 0 ^ 2 + b * w 0 * w 1 + c * w 1 ^ 2

@[expose] def IsAnisoRot (b c : k) (X : Matrix (Fin 2) (Fin 2) k) : Prop :=
  X 0 1 = c * X 1 0 ∧ X 1 1 = X 0 0 + b * X 1 0

@[expose] def IsAnisoRef (b c : k) (X : Matrix (Fin 2) (Fin 2) k) : Prop :=
  X 0 1 = c * X 1 0 + b * X 0 0 ∧ X 1 1 = X 0 0

theorem ne_zero_of_irr [Finite k] [CharP k 2] {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    b ≠ 0 := by
  rintro rfl
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' c
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  exact hirr r (by linear_combination hr + r ^ 2 * h2)

theorem aniso_classify {b c p s r t : k} (hb : b ≠ 0) (h2 : (2 : k) = 0)
    (e0 : p ^ 2 + b * p * s + c * s ^ 2 = 1) (e1 : r ^ 2 + b * r * t + c * t ^ 2 = c)
    (e2 : (p + r) ^ 2 + b * (p + r) * (s + t) + c * (s + t) ^ 2 = 1 + b + c) :
    (r = c * s ∧ t = p + b * s) ∨ (r = c * s + b * p ∧ t = p) := by
  have hpt : p * t + r * s = 1 := by
    have h : b * (p * t + r * s - 1) = 0 := by
      linear_combination e2 - e0 - e1 - (p * r + c * s * t) * h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hb)
  obtain ⟨l, hl⟩ : ∃ l, l = (p + b * s) * r + c * s * t := ⟨_, rfl⟩
  have hr : r = l * p + c * s := by
    rw [hl]
    linear_combination (-r) * e0 - (c * s) * hpt + (c * s * (r * s - 1)) * h2
  have ht : t = l * s + p + b * s := by
    rw [hl]
    linear_combination t * e0 - (p + b * s) * hpt + (t - p - b * s - c * s ^ 2 * t) * h2
  have hll : l * (l + b) = 0 := by
    rw [hr, ht] at e1
    linear_combination e1 - (l ^ 2 + b * l + c) * e0 -
      (2 * c * p * l * s + b ^ 2 * c * s ^ 2 + b * c * p * s + b * c * l * s ^ 2) * h2
  rcases mul_eq_zero.1 hll with h | h
  · left
    rw [h] at hr ht
    exact ⟨by rw [hr]; ring, by rw [ht]; ring⟩
  · right
    have hlb : l = b := by linear_combination h - b * h2
    rw [hlb] at hr ht
    exact ⟨by rw [hr]; ring, by rw [ht]; linear_combination b * s * h2⟩

theorem isAnisoRot_or_isAnisoRef [Finite k] [CharP k 2] {b c : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) {X : Matrix (Fin 2) (Fin 2) k}
    (hX : ∀ w, anisoNorm b c (X *ᵥ w) = anisoNorm b c w) :
    IsAnisoRot b c X ∨ IsAnisoRef b c X := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have e0 := hX ![1, 0]
  have e1 := hX ![0, 1]
  have e2 := hX ![1, 1]
  simp only [anisoNorm, mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_add] at e0 e1 e2
  rcases aniso_classify (b := b) (c := c) (p := X 0 0) (s := X 1 0) (r := X 0 1) (t := X 1 1)
    (ne_zero_of_irr hirr) h2
    (by linear_combination e0) (by linear_combination e1) (by linear_combination e2) with h | h
  · exact Or.inl h
  · exact Or.inr h

end Classify

section Types

variable {b c : k}

@[expose] def AnisoType (b c : k) (n : ZMod 2) (X : Matrix (Fin 2) (Fin 2) k) : Prop :=
  (n = 0 ∧ IsAnisoRot b c X) ∨ (n = 1 ∧ IsAnisoRef b c X)

theorem mul_apply_fin_two (X Y : Matrix (Fin 2) (Fin 2) k) (i j : Fin 2) :
    (X * Y) i j = X i 0 * Y 0 j + X i 1 * Y 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

theorem IsAnisoRot.mul {X Y : Matrix (Fin 2) (Fin 2) k} (hX : IsAnisoRot b c X)
    (hY : IsAnisoRot b c Y) : IsAnisoRot b c (X * Y) := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  refine ⟨?_, ?_⟩ <;> simp only [mul_apply_fin_two, hX1, hX2, hY1, hY2] <;> ring

theorem isAnisoRot_one : IsAnisoRot b c (1 : Matrix (Fin 2) (Fin 2) k) :=
  ⟨by simp, by simp⟩

theorem IsAnisoRot.commute {X Y : Matrix (Fin 2) (Fin 2) k} (hX : IsAnisoRot b c X)
    (hY : IsAnisoRot b c Y) : X * Y = Y * X := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  ext i j
  rw [mul_apply_fin_two, mul_apply_fin_two]
  fin_cases i <;> fin_cases j <;> simp [hX1, hX2, hY1, hY2] <;> ring

theorem IsAnisoRot.inv {X : GL (Fin 2) k} (hX : IsAnisoRot b c (X : Matrix (Fin 2) (Fin 2) k)) :
    IsAnisoRot b c ((X⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
  obtain ⟨hX1, hX2⟩ := hX
  rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_⟩ <;> simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    smul_eq_mul, hX1, hX2] <;> ring

variable (b c) in
@[expose] def anisoRotGL : Subgroup (GL (Fin 2) k) where
  carrier := {X | IsAnisoRot b c (X : Matrix (Fin 2) (Fin 2) k)}
  one_mem' := isAnisoRot_one
  mul_mem' := fun {X Y} hX hY => by
    change IsAnisoRot b c ((X * Y : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
    rw [Units.val_mul]
    exact hX.mul hY
  inv_mem' := fun hX => IsAnisoRot.inv hX

theorem mem_anisoRotGL {X : GL (Fin 2) k} :
    X ∈ anisoRotGL b c ↔ IsAnisoRot b c (X : Matrix (Fin 2) (Fin 2) k) :=
  Iff.rfl

theorem commutator_anisoRotGL :
    ⁅anisoRotGL b c, anisoRotGL b c⁆ = (⊥ : Subgroup (GL (Fin 2) k)) := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro X hX Y hY
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact IsAnisoRot.commute hX hY)

theorem AnisoType.mul [CharP k 2] {m n : ZMod 2} {X Y : Matrix (Fin 2) (Fin 2) k}
    (hX : AnisoType b c m X) (hY : AnisoType b c n Y) : AnisoType b c (m + n) (X * Y) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rcases hX with ⟨rfl, hX1, hX2⟩ | ⟨rfl, hX1, hX2⟩ <;>
    rcases hY with ⟨rfl, hY1, hY2⟩ | ⟨rfl, hY1, hY2⟩
  · exact Or.inl ⟨by decide, IsAnisoRot.mul ⟨hX1, hX2⟩ ⟨hY1, hY2⟩⟩
  · refine Or.inr ⟨by decide, ?_, ?_⟩ <;> simp only [mul_apply_fin_two, hX1, hX2, hY1, hY2]
    · linear_combination (-(b * c * X 1 0 * Y 1 0)) * h2
    · linear_combination (b * X 1 0 * Y 0 0) * h2
  · refine Or.inr ⟨by decide, ?_, ?_⟩ <;> simp only [mul_apply_fin_two, hX1, hX2, hY1, hY2] <;>
      ring
  · refine Or.inl ⟨by decide, ?_, ?_⟩ <;> simp only [mul_apply_fin_two, hX1, hX2, hY1, hY2]
    · linear_combination (b * X 0 0 * Y 0 0) * h2
    · linear_combination (-(b * X 0 0 * Y 1 0)) * h2

theorem AnisoType.eq_zero_of_one (hb : b ≠ 0) {n : ZMod 2}
    (h : AnisoType b c n (1 : Matrix (Fin 2) (Fin 2) k)) : n = 0 := by
  rcases h with ⟨rfl, -⟩ | ⟨-, h1, -⟩
  · rfl
  · exfalso
    simp at h1
    exact hb h1.symm

theorem AnisoType.eq_of_mul_eq_one [CharP k 2] (hb : b ≠ 0) {m n : ZMod 2}
    {X Y : Matrix (Fin 2) (Fin 2) k} (hX : AnisoType b c m X) (hY : AnisoType b c n Y)
    (hXY : X * Y = 1) : n = m := by
  have h1 := hX.mul hY
  rw [hXY] at h1
  have h := h1.eq_zero_of_one hb
  rcases hX with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases hY with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

theorem isAnisoRot_mul_mul_mul [CharP k 2] (hb : b ≠ 0) {m m' n n' : ZMod 2}
    {X X' Y Y' : Matrix (Fin 2) (Fin 2) k} (hX : AnisoType b c m X) (hX' : AnisoType b c m' X')
    (hY : AnisoType b c n Y) (hY' : AnisoType b c n' Y') (hXX : X * X' = 1) (hYY : Y * Y' = 1) :
    IsAnisoRot b c (X * Y * X' * Y') := by
  have hm := hX.eq_of_mul_eq_one hb hX' hXX
  have hn := hY.eq_of_mul_eq_one hb hY' hYY
  rw [hm] at hX'
  rw [hn] at hY'
  have h := ((hX.mul hY).mul hX').mul hY'
  have h0 : m + n + m + n = 0 := by
    have h2 : (2 : ZMod 2) = 0 := rfl
    linear_combination (m + n) * h2
  rw [h0] at h
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

end Types

end CFSG.SeitzReduction.F4Pilot
