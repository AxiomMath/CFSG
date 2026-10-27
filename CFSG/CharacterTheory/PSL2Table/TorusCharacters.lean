module

public import CFSG.CharacterTheory.PSL2Table.Tori
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.PSL2Table

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem diag_neg (a : Fˣ) : diag (-a) = -diag a := by
  apply SL_ext
  · rw [neg_apply_SL]
    simp
  · rw [neg_apply_SL]
    simp
  · rw [neg_apply_SL]
    simp
  · rw [neg_apply_SL]
    simp only [coe_diag, Units.val_neg, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [inv_neg]

theorem card_sq_eq_one_splitTorus [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) :
    Nat.card {t : splitTorus F // t ^ 2 = 1} = if IsSquare (-1 : F) then 2 else 1 := by
  have h2 := Ring.two_ne_zero hF
  have hsq : ∀ t : splitTorus F, t ^ 2 = 1 ↔
      ∃ a : Fˣ, (t : PSL(2, F)) = mk (diag a) ∧ ((a : F) ^ 2 = 1 ∨ (a : F) ^ 2 = -1) := by
    intro t
    obtain ⟨a, ha⟩ := (mem_splitTorus_iff_exists (t : PSL(2, F))).mp t.2
    constructor
    · intro ht
      refine ⟨a, ha, ?_⟩
      have h1 : ((t : PSL(2, F))) ^ 2 = 1 := by rw [← Subgroup.coe_pow, ht, Subgroup.coe_one]
      rw [ha, sq, ← map_mul, ← diag_mul, mk_diag_eq_one_iff, Units.val_mul] at h1
      have : ((a : F) ^ 2) * ((a : F) ^ 2) = 1 := by rw [← h1]; ring
      exact mul_self_eq_one_iff.mp this
    · rintro ⟨b, hb, hb2⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, hb, sq, ← map_mul, ← diag_mul, mk_diag_eq_one_iff,
        Units.val_mul]
      rcases hb2 with h | h
      · rw [← sq, h, one_pow]
      · rw [← sq, h]
        ring
  split_ifs with hm
  · obtain ⟨i, hi⟩ := hm
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hi
      exact one_ne_zero (neg_eq_zero.mp hi)
    let iu : Fˣ := Units.mk0 i hi0
    let ι : splitTorus F := ⟨mk (diag iu), mk_diag_mem_splitTorus iu⟩
    have hι : ι ≠ 1 := by
      intro h
      have h' := congrArg Subtype.val h
      change mk (diag iu) = 1 at h'
      rw [mk_diag_eq_one_iff, Units.val_mk0, sq, ← hi] at h'
      exact h2 (by linear_combination -h')
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, by rw [one_pow]⟩, ⟨ι, (hsq ι).mpr ⟨iu, rfl, Or.inr (by
      rw [Units.val_mk0, sq, ← hi])⟩⟩, fun h => hι (congrArg Subtype.val h).symm, ?_⟩
    ext ⟨t, ht⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨a, ha, ha2⟩ := (hsq t).mp ht
    rcases ha2 with h | h
    · left
      apply Subtype.ext
      apply Subtype.ext
      change (t : PSL(2, F)) = 1
      rw [ha, mk_diag_eq_one_iff, h]
    · right
      apply Subtype.ext
      apply Subtype.ext
      change (t : PSL(2, F)) = mk (diag iu)
      rw [ha, mk_eq_mk_iff]
      have : ((a : F) - i) * ((a : F) + i) = 0 := by linear_combination h + hi
      rcases mul_eq_zero.mp this with h' | h'
      · left
        congr 1
        exact Units.ext (by rw [Units.val_mk0]; linear_combination -h')
      · right
        have hia : iu = -a := Units.ext (by
          rw [Units.val_mk0, Units.val_neg]
          linear_combination h')
        rw [hia, diag_neg]
  · rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, by rw [one_pow]⟩, ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨a, ha, ha2⟩ := (hsq t).mp ht
    rcases ha2 with h | h
    · apply Subtype.ext
      apply Subtype.ext
      change (t : PSL(2, F)) = 1
      rw [ha, mk_diag_eq_one_iff, h]
    · exact (hm ⟨a, by rw [← sq, h]⟩).elim

theorem isSquare_mul_of_not_isSquare [Fintype F] [DecidableEq F]
    {a b : F} (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  have ha0 : a ≠ 0 := ne_zero_of_not_isSquare ha
  have hb0 : b ≠ 0 := ne_zero_of_not_isSquare hb
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0), map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha, quadraticChar_neg_one_iff_not_isSquare.mpr hb]
  norm_num

theorem sq_mk_eq_one_iff_of_nonsplit (hF : ringChar F ≠ 2) {ν : F} (hν0 : ν ≠ 0) {C : SL(2, F)}
    (hC : C ∈ nonsplitSL ν) (hy : (C : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    (mk C) ^ 2 = 1 ↔ (C : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
  have h2 := Ring.two_ne_zero hF
  obtain ⟨h1, h2'⟩ := hC
  have hdet := det_entries C
  rw [h1, h2'] at hdet
  set x := (C : Matrix (Fin 2) (Fin 2) F) 0 0
  set y := (C : Matrix (Fin 2) (Fin 2) F) 1 0
  rw [sq, ← map_mul, mk_eq_one_iff]
  have e00 : ((C * C : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = x ^ 2 + ν * y ^ 2 := by
    rw [mul_apply_SL, h2']
    ring
  have e10 : ((C * C : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 2 * x * y := by
    rw [mul_apply_SL, h1]
    ring
  constructor
  · rintro (h | h)
    · exfalso
      have h10 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h
      have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp only [e10, e00, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq,
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h10 h00
      have : (2 * ν) * (y * y) = 0 := by linear_combination h00 - hdet
      rcases mul_eq_zero.mp this with h' | h'
      · exact mul_ne_zero h2 hν0 h'
      · exact hy (mul_self_eq_zero.mp h')
    · have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
      simp only [e00, neg_apply_SL, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_eq] at h00
      have : 2 * (x * x) = 0 := by linear_combination h00 + hdet
      exact mul_self_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
  · intro hx
    right
    rw [hx] at hdet
    apply SL_ext
    · rw [e00, neg_apply_SL, hx]
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
      linear_combination -hdet
    · rw [mul_apply_SL, neg_apply_SL, h1, h2', hx]
      simp only [Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), neg_zero]
      have hx' : (C : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := hx
      rw [hx']
      ring
    · rw [e10, neg_apply_SL, hx]
      simp
    · rw [mul_apply_SL, neg_apply_SL, h1, h2', hx]
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
      linear_combination -hdet

theorem card_sq_eq_one_nonsplitTorus [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) {ν : F}
    (hν : ¬ IsSquare ν) :
    Nat.card {s : nonsplitTorus ν // s ^ 2 = 1} = if IsSquare (-1 : F) then 1 else 2 := by
  have h2 := Ring.two_ne_zero hF
  have hν0 := ne_zero_of_not_isSquare hν
  have hchar : ∀ s : nonsplitTorus ν, s ≠ 1 → (s ^ 2 = 1 ↔
      ∃ C : SL(2, F), C ∈ nonsplitSL ν ∧ (C : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 ∧
        (s : PSL(2, F)) = mk C ∧ (C : Matrix (Fin 2) (Fin 2) F) 0 0 = 0) := by
    intro s hs
    have hs' : (s : PSL(2, F)) ≠ 1 := fun h => hs (Subtype.ext h)
    obtain ⟨C, hC, hy, hsC⟩ := exists_of_mem_nonsplitTorus s.2 hs'
    have hsq : s ^ 2 = 1 ↔ (s : PSL(2, F)) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, Subtype.ext_iff, Subgroup.coe_one]
    rw [hsq]
    constructor
    · intro h
      refine ⟨C, hC, hy, hsC, ?_⟩
      rw [hsC] at h
      exact (sq_mk_eq_one_iff_of_nonsplit hF hν0 hC hy).mp h
    · rintro ⟨C', hC', hy', hsC', hx'⟩
      rw [hsC']
      exact (sq_mk_eq_one_iff_of_nonsplit hF hν0 hC' hy').mpr hx'
  split_ifs with hm
  · rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, by rw [one_pow]⟩, ?_⟩
    rintro ⟨s, hs⟩
    apply Subtype.ext
    by_contra hs1
    obtain ⟨C, ⟨h1, h2'⟩, hy, -, hx⟩ := (hchar s hs1).mp hs
    have hdet := det_entries C
    rw [h1, h2', hx] at hdet
    obtain ⟨c, hc⟩ := hm
    apply hν
    refine ⟨c / (C : Matrix (Fin 2) (Fin 2) F) 1 0, ?_⟩
    field_simp
    linear_combination -hdet + hc
  ·
    have hsq : IsSquare ((-1 : F) * ν⁻¹) :=
      isSquare_mul_of_not_isSquare hm (fun h => hν (isSquare_inv.mp h))
    obtain ⟨y₀, hy₀⟩ := hsq
    have hy₀' : (0 : F) ^ 2 - ν * y₀ ^ 2 = 1 := by
      have : ν * (y₀ * y₀) = -1 := by rw [← hy₀]; field_simp
      linear_combination -this
    have hy₀0 : y₀ ≠ 0 := by
      rintro rfl
      simp at hy₀'
    let C₀ := nsElem ν 0 y₀ hy₀'
    have hC₀ : C₀ ∈ nonsplitSL ν := nsElem_mem_nonsplitSL ν _ _ _
    let s₀ : nonsplitTorus ν := ⟨mk C₀, ⟨C₀, hC₀, rfl⟩⟩
    have hs₀1 : s₀ ≠ 1 := by
      intro h
      have h' := congrArg Subtype.val h
      change mk C₀ = 1 at h'
      rcases (mk_eq_one_iff C₀).mp h' with h'' | h''
      · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h''
        simp [C₀] at this
        exact hy₀0 this
      · have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h''
        simp [C₀, neg_apply_SL] at this
        exact hy₀0 this
    have hs₀ : s₀ ^ 2 = 1 := (hchar s₀ hs₀1).mpr ⟨C₀, hC₀, by simpa [C₀] using hy₀0, rfl,
      by simp [C₀]⟩
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨1, by rw [one_pow]⟩, ⟨s₀, hs₀⟩, fun h => hs₀1 (congrArg Subtype.val h).symm, ?_⟩
    ext ⟨s, hs⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_cases hs1 : s = 1
    · left
      exact Subtype.ext hs1
    · right
      apply Subtype.ext
      obtain ⟨C, ⟨h1, h2'⟩, hy, hsC, hx⟩ := (hchar s hs1).mp hs
      apply Subtype.ext
      change (s : PSL(2, F)) = mk C₀
      rw [hsC, mk_eq_mk_iff]
      have hdet := det_entries C
      rw [h1, h2', hx] at hdet
      have hyy : ((C : Matrix (Fin 2) (Fin 2) F) 1 0 - y₀) *
          ((C : Matrix (Fin 2) (Fin 2) F) 1 0 + y₀) = 0 := by
        have : ν * (((C : Matrix (Fin 2) (Fin 2) F) 1 0 - y₀) *
            ((C : Matrix (Fin 2) (Fin 2) F) 1 0 + y₀)) = 0 := by
          linear_combination -hdet + hy₀'
        exact (mul_eq_zero.mp this).resolve_left hν0
      rcases mul_eq_zero.mp hyy with h' | h'
      · left
        have hyv : (C : Matrix (Fin 2) (Fin 2) F) 1 0 = y₀ := by linear_combination h'
        apply SL_ext
        · simp [C₀, hx]
        · simp [C₀, h2', hyv]
        · simp [C₀, hyv]
        · simp [C₀, h1, hx]
      · right
        have hyv : (C : Matrix (Fin 2) (Fin 2) F) 1 0 = -y₀ := by linear_combination h'
        apply SL_ext
        · simp [C₀, hx, neg_apply_SL]
        · simp [C₀, h2', hyv, neg_apply_SL]
        · simp [C₀, hyv, neg_apply_SL]
        · simp [C₀, h1, hx, neg_apply_SL]

theorem card_units_hom_of_comm {A : Type} [Group A] [Finite A]
    (hcomm : ∀ a b : A, a * b = b * a) :
    Nat.card (A →* ℂˣ) = Nat.card A ∧
      Nat.card {α : A →* ℂˣ // α ^ 2 = 1} = Nat.card {a : A // a ^ 2 = 1} := by
  let _ : CommGroup A := { (inferInstance : Group A) with mul_comm := hcomm }
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity A ℂ
  refine ⟨Nat.card_congr e.toEquiv, Nat.card_congr ?_⟩
  exact
    { toFun := fun α => ⟨e α, by rw [← map_pow, α.2, map_one]⟩
      invFun := fun a => ⟨e.symm a, by rw [← map_pow, a.2, map_one]⟩
      left_inv := fun α => Subtype.ext (e.symm_apply_apply α)
      right_inv := fun a => Subtype.ext (e.apply_symm_apply a) }

theorem splitTorus_comm (a b : splitTorus F) : a * b = b * a :=
  Subtype.ext (splitTorus_mul_comm a.2 b.2)

theorem nonsplitTorus_comm {ν : F} (a b : nonsplitTorus ν) : a * b = b * a :=
  Subtype.ext (nonsplitTorus_mul_comm a.2 b.2)

end CFSG.PSL2Table
