module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X7
public import CFSG.ClassicalInvolution.Asc77.AscCX9X5

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2L

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem rootInv_mul_self : rootInv F (show 2 ≤ 4 by norm_num) * rootInv F (show 2 ≤ 4 by norm_num) =
    1 := by
  rw [rootInv, ← map_mul, neg_one_mul, neg_neg, map_one]

theorem coe_rootInv_four : ((rootInv F (show 2 ≤ 4 by norm_num) : SL(4, F)) :
    Matrix (Fin 4) (Fin 4) F) = diagonal ![-1, -1, 1, 1] := by
  rw [coe_rootInv, negBlock_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem spForm_mul_z (m n : F) : spForm m n * diagonal ![-1, -1, 1, 1] = spForm (-m) n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spForm, Matrix.mul_diagonal]

theorem slConj_rootInv (A : GL (Fin 4) F) (s : SL(4, F)) :
    slConjugation 4 F (A * Matrix.SpecialLinearGroup.toGL (rootInv F (show 2 ≤ 4 by norm_num)))
        ((s⁻¹).transpose) =
      slConjugation 4 F A ((rootInv F (show 2 ≤ 4 by norm_num) * s *
        (rootInv F (show 2 ≤ 4 by norm_num))⁻¹)⁻¹).transpose := by
  set r := rootInv F (show 2 ≤ 4 by norm_num) with hr
  have hri : r⁻¹ = r := inv_eq_of_mul_eq_one_right rootInv_mul_self
  have hR : (r : Matrix (Fin 4) (Fin 4) F) = diagonal ![-1, -1, 1, 1] := coe_rootInv_four
  have hRt : (r : Matrix (Fin 4) (Fin 4) F)ᵀ = r := by rw [hR, diagonal_transpose]
  have e : (r * s * r⁻¹)⁻¹ = r * s⁻¹ * r := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, hri, mul_assoc]
  apply Subtype.ext
  rw [slConjugation_matrix, slConjugation_matrix, e, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul, Matrix.transpose_mul, hRt,
    _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  have hti : ((Matrix.SpecialLinearGroup.toGL r)⁻¹ : GL (Fin 4) F).val =
      (r : Matrix (Fin 4) (Fin 4) F) := by
    rw [← map_inv, hri]
    rfl
  rw [hti]
  show (A : Matrix (Fin 4) (Fin 4) F) * r * _ * (r * _) = _
  simp only [Matrix.mul_assoc]

section Wit

variable {p f : ℕ} [Fact p.Prime]


theorem reflWit_std (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hsq : ¬ IsSquare (-1 : GaloisField p f))
    {Y : Type} [Group Y] [Finite Y] (θ : SL(4, GaloisField p f) →* Y)
    (hθ : Function.Surjective θ) (hθker : θ.ker = scalars 4 (GaloisField p f))
    {Φ : Set (Subgroup Y)} {a₀ b₀ : Y}
    (htw : TwinSect0 Φ ((blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ)
      ((blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ)
      (θ (rootInv (GaloisField p f) (show 2 ≤ 4 by norm_num))) a₀ b₀)
    (hconj : ∀ J ∈ Φ, ∀ y : Y, conjSub y J ∈ Φ) (β : MulAut Y)
    (hβA : ∀ y ∈ (blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ, β y = y)
    (hβA' : ∀ y ∈ (blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ, β y = y)
    (hβ2 : β * β = 1) (hβ1 : β ≠ 1)
    (hβz : β ≠ MulAut.conj (θ (rootInv (GaloisField p f) (show 2 ≤ 4 by norm_num)))) :
    ∃ (hA : (blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup β))
      (hA' : (blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup β))
      (hB : (blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup
          (β * MulAut.conj (θ (rootInv (GaloisField p f) (show 2 ≤ 4 by norm_num))))))
      (hB' : (blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ ≤
        Goldschmidt75.perfRes (fixSubgroup
          (β * MulAut.conj (θ (rootInv (GaloisField p f) (show 2 ≤ 4 by norm_num)))))),
      IsOm5 p f (centTG _ _ β hA hA') ∧ IsOm5 p f (centTG _ _ _ hB hB') ∧
        DiagWit p (centTG _ _ β hA hA') (centTG _ _ _ hB hB') := by
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h, pow_zero] at hq
      omega
    · exact h
  have h2 : (2 : GaloisField p f) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 :=
      (CharP.cast_eq_zero_iff (GaloisField p f) p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 hdvd)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f (by omega)]
    omega
  set r := rootInv (GaloisField p f) (show 2 ≤ 4 by norm_num) with hr
  set e := eTheta θ hθ hθker with he
  set β₀ : MulAut (projectiveSL 4 (GaloisField p f)) := (e.trans β).trans e.symm with hβ₀
  have hβ₀e : ∀ x, e (β₀ x) = β (e x) := fun x => e.apply_symm_apply _
  have hep : ∀ s, e (proj 4 (GaloisField p f) s) = θ s := fun s => rfl
  have hfix : CX4.L4.FixBlocks β₀ := by
    refine ⟨fun s hs => e.injective ?_, fun s hs => e.injective ?_⟩
    · rw [hβ₀e, hep, hβA _ ⟨s, hs, rfl⟩]
    · rw [hβ₀e, hep, hβA' _ ⟨s, hs, rfl⟩]
  have hββ : ∀ y, β (β y) = y := fun y => by
    rw [← MulAut.mul_apply, hβ2, MulAut.one_apply]
  have hk : β₀ ^ (2 ^ 1) = 1 := by
    ext x
    apply e.injective
    rw [pow_one, sq, MulAut.mul_apply, hβ₀e, hβ₀e, hββ, MulAut.one_apply]
  rcases CX4.L4.two_elem_cases h2 hsq hfix hk with (h | h) | ⟨M, m, n, hm, hn, hM, hβ₀M⟩
  · exfalso
    apply hβ1
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hβ₀e, h, MulAut.one_apply, MulAut.one_apply]
  · exfalso
    apply hβz
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← hβ₀e, h, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rfl
  have hβθ : ∀ s, β (θ s) = θ (slConjugation 4 (GaloisField p f) M ((s⁻¹).transpose)) := by
    intro s
    rw [← hep, ← hβ₀e, hβ₀M, MulAut.mul_apply, dualAut_proj, conjAut_proj, hep]
  set M' := M * Matrix.SpecialLinearGroup.toGL r with hM'def
  have hM' : (M' : Matrix (Fin 4) (Fin 4) (GaloisField p f)) = spForm (-m) n := by
    rw [hM'def, Units.val_mul, hM, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hr,
      coe_rootInv_four]
    exact spForm_mul_z m n
  have hβθ' : ∀ s, (β * MulAut.conj (θ r)) (θ s) =
      θ (slConjugation 4 (GaloisField p f) M' ((s⁻¹).transpose)) := by
    intro s
    rw [MulAut.mul_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hβθ, hM'def,
      slConj_rootInv]
  have hX₁ := perfRes_fix_eq h4 hm hn θ hθ hθker M hM β hβθ
  have hX₂ := perfRes_fix_eq h4 (neg_ne_zero.mpr hm) hn θ hθ hθker M' hM' _ hβθ'
  have hA : (blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β) := by
    rw [hX₁]
    exact Subgroup.map_mono (block0_le_spM m n)
  have hA' : (blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup β) := by
    rw [hX₁]
    exact Subgroup.map_mono (block2_le_spM m n)
  have hB : (blockSL (GaloisField p f) 4 2 0 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj (θ r))) := by
    rw [hX₂]
    exact Subgroup.map_mono (block0_le_spM (-m) n)
  have hB' : (blockSL (GaloisField p f) 4 2 2 (by norm_num)).range.map θ ≤
      Goldschmidt75.perfRes (fixSubgroup (β * MulAut.conj (θ r))) := by
    rw [hX₂]
    exact Subgroup.map_mono (block2_le_spM (-m) n)
  exact ⟨hA, hA', hB, hB', ⟨_, _, _, _, om5Data_T hp2 hq hm hn θ hθker _ hX₁ htw hconj⟩,
    ⟨_, _, _, _, om5Data_T hp2 hq (neg_ne_zero.mpr hm) hn θ hθker _ hX₂ htw hconj⟩,
    diagWit_of_graph θ hθ hθker p hsq h4 hm hn M M' hM hM' β _ hβθ hβθ' hA hA' hB hB'⟩

end Wit

end CFSG.ClassicalInvolution.Asc77.CX.MF2L
