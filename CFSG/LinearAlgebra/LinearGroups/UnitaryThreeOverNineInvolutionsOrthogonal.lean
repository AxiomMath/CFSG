module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsLines

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] {h : UnitaryFieldData 3 1 F} {hF : Nat.card F = 9}

theorem statedSU_ext {g g' : StatedSU 3 3 F}
    (hgg : ∀ y, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y =
      ((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) : g = g' :=
  Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.mpr hgg))

theorem mul_mulVec (g g' : StatedSU 3 3 F) (y : Fin 3 → F) :
    (((g * g' : StatedSU 3 3 F) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y =
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((g' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y) := by
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem tauLine_mulVec_gen (L : NonisoLine F) (y : Fin 3 → F) :
    ((((tauLine h hF L : StatedSU 3 3 F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y =
      tauLin h L.gen y := by
  rw [coe_tauLine, tauGL_mulVec]

theorem tauLin_of_orth {v w : Fin 3 → F}
    (hvw : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) v w = 0) : tauLin h v w = -w := by
  rw [tauLin_apply, hvw, zero_div, mul_zero, zero_smul, zero_sub]

theorem eq_zero_of_smul_eq_smul {L M : NonisoLine F} (hLM : L ≠ M) {u u' : Fin 3 → F}
    (hu : u ∈ L.1) (hu0 : u ≠ 0) (hu' : u' ∈ M.1) {a b : F} (hab : a • u = b • u') : a = 0 := by
  by_contra ha
  have huM : u ∈ M.1 := by
    have := M.1.smul_mem (a⁻¹ * b) hu'
    rwa [mul_smul, ← hab, smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  exact hLM (Subtype.ext (by rw [eq_span_of_mem L hu hu0, eq_span_of_mem M huM hu0]))

theorem orth_iff_gen (L M : NonisoLine F) :
    (∀ x ∈ L.1, ∀ y ∈ M.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y = 0) ↔
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen M.gen = 0 := by
  refine ⟨fun hLM => hLM _ L.gen_mem _ M.gen_mem, fun h0 x hx y hy => ?_⟩
  rw [L.eq_span_gen] at hx
  rw [M.eq_span_gen] at hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [gramForm_smul_left, gramForm_smul_right, h0, mul_zero, mul_zero]

theorem orth_sup_iff (L M : NonisoLine F) (y : Fin 3 → F) :
    (∀ x ∈ L.1 ⊔ M.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y = 0) ↔
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen y = 0 ∧
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) M.gen y = 0 := by
  constructor
  · intro hy
    exact ⟨hy _ (Submodule.mem_sup_left L.gen_mem), hy _ (Submodule.mem_sup_right M.gen_mem)⟩
  · rintro ⟨h0, h0'⟩ x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [L.eq_span_gen] at ha
    rw [M.eq_span_gen] at hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_add, LinearMap.add_apply, gramForm_smul_left, gramForm_smul_left, h0, h0', mul_zero,
      mul_zero, add_zero]

theorem tauLine_commute_iff {L M : NonisoLine F} (hLM : L ≠ M) :
    (tauLine h hF L : StatedSU 3 3 F) * tauLine h hF M =
        (tauLine h hF M : StatedSU 3 3 F) * tauLine h hF L ↔
      ∀ x ∈ L.1, ∀ y ∈ M.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y = 0 := by
  rw [orth_iff_gen]
  have hu := L.gramForm_gen (h := h)
  have hu' := M.gramForm_gen (h := h)
  constructor
  · intro hc
    have hfix : tauLin h M.gen (tauLin h L.gen M.gen) = tauLin h L.gen M.gen := by
      have := congrArg (fun g : StatedSU 3 3 F =>
        ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ M.gen) hc
      simp only [mul_mulVec, tauLine_mulVec_gen, tauLin_self hu'] at this
      exact this.symm
    rw [tauLin_eq_self_iff hu'] at hfix
    obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp hfix
    rw [tauLin_apply] at hc'
    have hab : (2 * (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen M.gen /
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen L.gen)) • L.gen = (c + 1) • M.gen := by
      rw [add_smul, one_smul, hc', sub_add_cancel]
    have h0 := eq_zero_of_smul_eq_smul hLM L.gen_mem L.gen_ne_zero M.gen_mem hab
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact absurd h0 (two_ne_zero' h)
    · exact (div_eq_zero_iff.mp h0).resolve_right hu
  · intro h0
    have h0' : gramForm h (1 : Matrix (Fin 3) (Fin 3) F) M.gen L.gen = 0 := by
      rw [← bar_gramForm, h0, map_zero]
    refine statedSU_ext fun y => ?_
    simp only [mul_mulVec, tauLine_mulVec_gen]
    have hL : tauLin h L.gen y = (2 * (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen y /
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen L.gen)) • L.gen - y := tauLin_apply h _ _
    have hM : tauLin h M.gen y = (2 * (gramForm h (1 : Matrix (Fin 3) (Fin 3) F) M.gen y /
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) M.gen M.gen)) • M.gen - y := tauLin_apply h _ _
    rw [hM, hL, map_sub, map_sub, map_smul, map_smul, tauLin_of_orth h0, tauLin_of_orth h0', hL,
      hM, smul_neg, smul_neg]
    abel

theorem tauLin_tauLin_eq_self_iff {L M : NonisoLine F} (hLM : L ≠ M) (y : Fin 3 → F) :
    tauLin h L.gen (tauLin h M.gen y) = y ↔
      gramForm h (1 : Matrix (Fin 3) (Fin 3) F) L.gen y = 0 ∧
        gramForm h (1 : Matrix (Fin 3) (Fin 3) F) M.gen y = 0 := by
  have hu := L.gramForm_gen (h := h)
  have hu' := M.gramForm_gen (h := h)
  have h2 := two_ne_zero' h
  constructor
  · intro hy
    have h1 : tauLin h M.gen y = tauLin h L.gen y := by
      have := congrArg (tauLin h L.gen) hy
      rwa [tauLin_tauLin hu] at this
    rw [tauLin_apply, tauLin_apply, sub_left_inj] at h1
    have ha := eq_zero_of_smul_eq_smul hLM L.gen_mem L.gen_ne_zero M.gen_mem h1.symm
    rw [ha, zero_smul, smul_eq_zero] at h1
    have hb := h1.resolve_right M.gen_ne_zero
    rcases mul_eq_zero.mp ha with ha | ha
    · exact absurd ha h2
    rcases mul_eq_zero.mp hb with hb | hb
    · exact absurd hb h2
    exact ⟨(div_eq_zero_iff.mp ha).resolve_right hu, (div_eq_zero_iff.mp hb).resolve_right hu'⟩
  · rintro ⟨h0, h0'⟩
    rw [tauLin_of_orth h0', map_neg, tauLin_of_orth h0, neg_neg]

theorem exists_tauLine_mul_eq {L M : NonisoLine F} (hLM : L ≠ M)
    (horth : ∀ x ∈ L.1, ∀ y ∈ M.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y = 0) :
    ∃ T : NonisoLine F, (T.1 : Set (Fin 3 → F)) =
        {y | ∀ x ∈ L.1 ⊔ M.1, gramForm h (1 : Matrix (Fin 3) (Fin 3) F) x y = 0} ∧
      (tauLine h hF L : StatedSU 3 3 F) * tauLine h hF M = tauLine h hF T := by
  have hc := (tauLine_commute_iff (hF := hF) hLM).mpr horth
  have hsq : ∀ N : NonisoLine F, (tauLine h hF N : StatedSU 3 3 F) ^ 2 = 1 := fun N =>
    orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq (tauLine h hF N).2)
  have hinv : orderOf ((tauLine h hF L : StatedSU 3 3 F) * tauLine h hF M) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ fun h1 => hLM (tauLine_injective (h := h) (hF := hF) ?_)
    · rw [Commute.mul_pow hc, hsq, hsq, one_mul]
    · apply Subtype.ext
      rw [eq_inv_of_mul_eq_one_left h1]
      exact inv_eq_of_mul_eq_one_right (by rw [← sq, hsq])
  obtain ⟨T, hT⟩ := tauLine_surjective (h := h) (hF := hF) ⟨_, hinv⟩
  have hT' : (tauLine h hF T : StatedSU 3 3 F) = tauLine h hF L * tauLine h hF M :=
    congrArg Subtype.val hT
  refine ⟨T, Set.ext fun y => ?_, hT'.symm⟩
  rw [SetLike.mem_coe, mem_line_iff_tauLine (h := h) (hF := hF), hT', mul_mulVec,
    tauLine_mulVec_gen, tauLine_mulVec_gen, tauLin_tauLin_eq_self_iff hLM, Set.mem_ofPred_eq,
    orth_sup_iff]

end CFSG.LinearGroups.UnitaryThreeOverNine
