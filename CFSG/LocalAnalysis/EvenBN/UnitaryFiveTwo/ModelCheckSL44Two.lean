module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSL44
import all CFSG.Fischer.F4
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow

open Matrix Subgroup CFSG.Fischer
open scoped MatrixGroups

theorem exists_eq_mul_of_apply_eq_zero : ∀ a b c d : F4, ¬(a = 0 ∧ b = 0) →
    c * a + d * b = 0 → ∃ l, d = l * a ∧ c = l * b := by
  decide

theorem eq_zero_of_apply_eq_zero : ∀ a b a' b' c d : F4, a * b' + b * a' ≠ 0 →
    c * a + d * b = 0 → c * a' + d * b' = 0 → c = 0 ∧ d = 0 := by
  decide

theorem apply_eq_zero_of_det_eq_zero : ∀ a b c d a' b' : F4, ¬(a = 0 ∧ b = 0) →
    c * a + d * b = 0 → a * b' + b * a' = 0 → c * a' + d * b' = 0 := by
  decide

theorem apply_self_eq_zero {x : SL(4, F4)} (hx : x ∈ MK) (hxx : x * x = 1) :
    x 3 1 * x 1 0 + x 3 2 * x 2 0 = 0 := by
  obtain ⟨a, b, c, d, z, rfl⟩ := mem_MK.1 hx
  exact mSL_mul_self_eq_one_iff.1 hxx

theorem apply_eq_apply {x y : SL(4, F4)} (hx : x ∈ MK) (hy : y ∈ MK) (hxy : x * y = y * x) :
    x 3 1 * y 1 0 + x 3 2 * y 2 0 = y 3 1 * x 1 0 + y 3 2 * x 2 0 := by
  obtain ⟨a, b, c, d, z, rfl⟩ := mem_MK.1 hx
  obtain ⟨a', b', c', d', z', rfl⟩ := mem_MK.1 hy
  exact mSL_mul_comm_iff.1 hxy

theorem le_of_elemAb_line {E : Subgroup SL(4, F4)} (hE : E ≤ MK)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) :
    E ≤ B₁K ∨ E ≤ B₂K ∨ (∃ l : F4, l ≠ 0 ∧ E ≤ UK l) ∨
      ∃ p q : F4, ¬(p = 0 ∧ q = 0) ∧ E ≤ Z₂Line p q := by
  have F1 : ∀ x ∈ E, x 3 1 * x 1 0 + x 3 2 * x 2 0 = 0 := fun x hx =>
    apply_self_eq_zero (hE hx) (hs x hx)
  have F2 : ∀ x ∈ E, ∀ y ∈ E, x 3 1 * y 1 0 + x 3 2 * y 2 0 = y 3 1 * x 1 0 + y 3 2 * x 2 0 :=
    fun x hx y hy => apply_eq_apply (hE hx) (hE hy) (hc x hx y hy)
  by_cases h₁ : ∀ x ∈ E, x 1 0 = 0 ∧ x 2 0 = 0
  · exact Or.inr (Or.inl fun x hx => mem_mSub.2 ⟨hE hx, h₁ x hx⟩)
  simp only [not_forall, exists_prop] at h₁
  obtain ⟨x, hx, hv⟩ := h₁
  obtain ⟨l, hl₁, hl₂⟩ := exists_eq_mul_of_apply_eq_zero _ _ _ _ hv (F1 x hx)
  by_cases h₂ : ∀ y ∈ E, x 1 0 * y 2 0 + x 2 0 * y 1 0 = 0
  · refine Or.inr (Or.inr (Or.inr ⟨x 1 0, x 2 0, hv, fun y hy => mem_mSub.2 ⟨hE hy, ?_, ?_⟩⟩))
    · linear_combination h₂ y hy - x 1 0 * y 2 0 * F4.two_eq_zero
    · linear_combination
        apply_eq_zero_of_det_eq_zero _ _ _ _ _ _ hv (F1 x hx) (h₂ y hy) - F2 x hx y hy
  simp only [not_forall, exists_prop] at h₂
  obtain ⟨y, hy, hdet⟩ := h₂
  have hvy : ¬(y 1 0 = 0 ∧ y 2 0 = 0) := fun ⟨h1, h2⟩ => hdet (by rw [h1, h2]; ring)
  obtain ⟨l', hl'₁, hl'₂⟩ := exists_eq_mul_of_apply_eq_zero _ _ _ _ hvy (F1 y hy)
  have hll' : l = l' := by
    have e := F2 x hx y hy
    rw [hl₁, hl₂, hl'₁, hl'₂] at e
    have e' : (l - l') * (x 1 0 * y 2 0 + x 2 0 * y 1 0) = 0 := by linear_combination e
    exact sub_eq_zero.1 ((mul_eq_zero.1 e').resolve_right hdet)
  rw [← hll'] at hl'₁ hl'₂
  have key : ∀ z ∈ E, z 3 2 = l * z 1 0 ∧ z 3 1 = l * z 2 0 := by
    intro z hz
    by_cases hvz : z 1 0 = 0 ∧ z 2 0 = 0
    · obtain ⟨hz1, hz2⟩ := hvz
      have h1 := F2 x hx z hz
      have h2 := F2 y hy z hz
      rw [hz1, hz2] at h1 h2
      obtain ⟨hc', hd'⟩ := eq_zero_of_apply_eq_zero _ _ _ _ (z 3 1) (z 3 2) hdet
        (by linear_combination -h1) (by linear_combination -h2)
      rw [hz1, hz2, hc', hd', mul_zero]
      exact ⟨rfl, rfl⟩
    · obtain ⟨l'', h''₁, h''₂⟩ := exists_eq_mul_of_apply_eq_zero _ _ _ _ hvz (F1 z hz)
      by_cases hl : l = l''
      · subst hl
        exact ⟨h''₁, h''₂⟩
      exfalso
      have e1 := F2 x hx z hz
      rw [hl₁, hl₂, h''₁, h''₂] at e1
      have e2 := F2 y hy z hz
      rw [hl'₁, hl'₂, h''₁, h''₂] at e2
      have e1' : (l - l'') * (z 2 0 * x 1 0 + z 1 0 * x 2 0) = 0 := by linear_combination e1
      have e2' : (l - l'') * (z 2 0 * y 1 0 + z 1 0 * y 2 0) = 0 := by linear_combination e2
      have hl0 : l - l'' ≠ 0 := sub_ne_zero.2 hl
      obtain ⟨h20, h10⟩ := eq_zero_of_apply_eq_zero _ _ _ _ _ _ hdet
        ((mul_eq_zero.1 e1').resolve_left hl0) ((mul_eq_zero.1 e2').resolve_left hl0)
      exact hvz ⟨h10, h20⟩
  by_cases hl0 : l = 0
  · subst hl0
    refine Or.inl fun z hz => mem_mSub.2 ⟨hE hz, ?_, ?_⟩
    · rw [(key z hz).2, zero_mul]
    · rw [(key z hz).1, zero_mul]
  · exact Or.inr (Or.inr (Or.inl ⟨l, hl0, fun z hz => mem_mSub.2 ⟨hE hz, key z hz⟩⟩))

@[expose] def levMat (c : F4) : Matrix (Fin 4) (Fin 4) F4 :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, c, 0; 0, 0, 0, 1]

theorem det_levMat (c : F4) : (levMat c).det = 1 := by
  simp [levMat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, CharTwo.neg_eq]

@[expose] def levSL (c : F4) : SL(4, F4) := ⟨levMat c, det_levMat c⟩

theorem levSL_mul (c a b c' d z : F4) :
    levSL c * pSL a 0 d b c' z = pSL b 0 c' (a + c * b) (c * c' + d) z * levSL c := by
  ext i j
  change (levMat c * pMat a 0 d b c' z) i j =
    (pMat b 0 c' (a + c * b) (c * c' + d) z * levMat c) i j
  fin_cases i <;> fin_cases j <;> simp [pMat, levMat, Matrix.mul_apply, Fin.sum_univ_four]
  revert c a b c' d z
  decide

theorem levSL_mem_normalizer (c : F4) : levSL c ∈ normalizer (MK : Set SL(4, F4)) := by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨a, b, c', d, z, rfl⟩ := mem_MK.1 hx
  rw [levSL_mul, mul_inv_cancel_right]
  exact mem_MK.2 ⟨_, _, _, _, _, rfl⟩

theorem Z₂Line_one_le_map (c : F4) :
    Z₂Line 1 c ≤ Z₂K.map (MulAut.conj (levSL c)).toMonoidHom := by
  intro x hx
  obtain ⟨hxM, h₁, h₂⟩ := mem_mSub.1 hx
  rw [eq_pSL_of_mem_MK hxM]
  refine ⟨pSL 0 0 0 (x 1 0) (x 3 2) (x 3 0), mem_mSub.2 ⟨mem_MK.2 ⟨_, _, _, _, _, rfl⟩, rfl, rfl⟩,
    ?_⟩
  change levSL c * _ * (levSL c)⁻¹ = _
  rw [levSL_mul, mul_inv_cancel_right, pSL_eq_pSL_iff]
  refine ⟨rfl, rfl, rfl, ?_, ?_, rfl⟩
  · linear_combination h₁
  · linear_combination h₂ - x 3 1 * F4.two_eq_zero

theorem Z₂Line_zero_le {q : F4} (hq : q ≠ 0) : Z₂Line 0 q ≤ Z₂K := by
  intro x hx
  obtain ⟨hxM, h₁, h₂⟩ := mem_mSub.1 hx
  refine mem_mSub.2 ⟨hxM, ?_, ?_⟩
  · rw [mul_zero] at h₁
    exact (mul_eq_zero.1 h₁).resolve_right hq
  · rw [mul_zero, zero_add] at h₂
    exact (mul_eq_zero.1 h₂).resolve_right hq

theorem map_conj_one (H : Subgroup SL(4, F4)) :
    H.map (MulAut.conj (1 : SL(4, F4))).toMonoidHom = H := by
  ext x
  simp

theorem exists_Z₂Line_le_map {p q : F4} (hpq : ¬(p = 0 ∧ q = 0)) :
    ∃ g ∈ normalizer (MK : Set SL(4, F4)), Z₂Line p q ≤ Z₂K.map (MulAut.conj g).toMonoidHom := by
  by_cases hp : p = 0
  · subst hp
    refine ⟨1, one_mem _, ?_⟩
    rw [map_conj_one]
    exact Z₂Line_zero_le fun hq => hpq ⟨rfl, hq⟩
  · refine ⟨levSL (q * p⁻¹), levSL_mem_normalizer _, fun x hx => Z₂Line_one_le_map _ ?_⟩
    obtain ⟨hxM, h₁, h₂⟩ := mem_mSub.1 hx
    refine mem_mSub.2 ⟨hxM, ?_, ?_⟩
    · rw [mul_one, ← mul_assoc, h₁, mul_assoc, mul_inv_cancel₀ hp, mul_one]
    · rw [mul_one]
      have e : (x 3 1 * p + x 3 2 * q) * p⁻¹ = 0 := by rw [h₂, zero_mul]
      rw [add_mul, mul_assoc, mul_inv_cancel₀ hp, mul_one, mul_assoc] at e
      exact e

theorem le_of_elemAb {E : Subgroup SL(4, F4)} (hE : E ≤ MK)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) :
    E ≤ B₁K ∨ E ≤ B₂K ∨ (∃ l : F4, l ≠ 0 ∧ E ≤ UK l) ∨
      ∃ g ∈ normalizer (MK : Set SL(4, F4)), E ≤ Z₂K.map (MulAut.conj g).toMonoidHom := by
  rcases le_of_elemAb_line hE hc hs with h | h | h | ⟨p, q, hpq, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · obtain ⟨g, hg, hle⟩ := exists_Z₂Line_le_map hpq
    exact Or.inr (Or.inr (Or.inr ⟨g, hg, h.trans hle⟩))

theorem card_map_Z₂K (g : SL(4, F4)) : Nat.card (Z₂K.map (MulAut.conj g).toMonoidHom) = 2 ^ 6 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_Z₂K]

theorem card_le_of_elemAb {E : Subgroup SL(4, F4)} (hE : E ≤ MK)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 ^ 6 := by
  rcases le_of_elemAb hE hc hs with h | h | ⟨l, -, h⟩ | ⟨g, -, h⟩
  · exact card_B₁K ▸ Subgroup.card_le_of_le h
  · exact card_B₂K ▸ Subgroup.card_le_of_le h
  · exact card_UK l ▸ Subgroup.card_le_of_le h
  · exact card_map_Z₂K g ▸ Subgroup.card_le_of_le h

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
