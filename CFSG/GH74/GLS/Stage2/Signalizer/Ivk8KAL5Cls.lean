module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL5Def

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem ka_pl5_isSquare_of_det {F : Type} [Field F] {c d : Fˣ} (h : d * d = c ^ 5) :
    ∃ μ : Fˣ, μ * μ = c := by
  refine ⟨c ^ 3 * d⁻¹, ?_⟩
  calc c ^ 3 * d⁻¹ * (c ^ 3 * d⁻¹) = c ^ 3 * c ^ 3 * (d⁻¹ * d⁻¹) := by rw [mul_mul_mul_comm]
    _ = c ^ 3 * c ^ 3 * (d * d)⁻¹ := by rw [_root_.mul_inv_rev]
    _ = c ^ 3 * c ^ 3 * (c ^ 5)⁻¹ := by rw [h]
    _ = c := by group

theorem kaAll_pl5 (h4 : KAL5B4) (h3 : KAL5B3) (h3' : KAL5B3Three) (hO : KAL5GOrth)
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (hfodd : Odd f) (hK2 : ringChar F ≠ 2)
    {α : MulAut (projectiveSL 5 F)} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
  classical
  have hFodd : Odd (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hK2)
  have hc35 : Nat.card F = 3 ∨ 5 ≤ Nat.card F := by
    have hlt := Finite.one_lt_card (α := F)
    obtain ⟨k, hk⟩ := hFodd
    omega
  have hα : α ^ 2 = 1 := by rw [sq]; exact hα2
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := 5) (by norm_num)).2 α
  rw [hαeq] at hα hα1 ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα hα1 ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 5 F), mul_one] at hα hα1 ⊢
      have h1 : conjAut 5 F (A * A) * fieldAut 5 F 1 = 1 := by
        rw [map_one, mul_one, map_mul, ← sq, hα]
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1
      have hdet : Matrix.GeneralLinearGroup.det A * Matrix.GeneralLinearGroup.det A = c ^ 5 := by
        rw [← map_mul, ← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
      obtain ⟨μ, hμ⟩ := ka_pl5_isSquare_of_det hdet
      set B' : GL (Fin 5) F := GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * A with hB'
      have hcB : conjAut 5 F B' = conjAut 5 F A := by
        rw [hB', map_mul, conjAut_scalar, one_mul]
      have hs : μ⁻¹ * μ⁻¹ * c = 1 := by
        rw [← hμ]
        group
      have hBB : B' * B' = 1 := by
        calc B' * B' = GeneralLinearGroup.scalar (Fin 5) μ⁻¹ *
              GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * (A * A) := by
              rw [hB', mul_assoc, ← mul_assoc A, ← GeneralLinearGroup.scalar_commute]
              group
          _ = 1 := by rw [← hc, ← map_mul, ← map_mul, hs, map_one]
      have hBm : (B' : Matrix (Fin 5) (Fin 5) F) * B' = 1 := by
        rw [← Units.val_mul, hBB, Units.val_one]
      have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hK2 hBm)
      rw [Module.finrank_fin_fun] at hsum
      have hker : LinearMap.ker (toLin' ((-B' : GL (Fin 5) F).val) - 1) =
          LinearMap.ker (toLin' B'.val + 1) := by
        ext v
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
          Module.End.one_apply, Units.val_neg, neg_mulVec]
        rw [← neg_add', neg_eq_zero]
      rw [← hcB]
      have hα1' : conjAut 5 F B' ≠ 1 := by rw [hcB]; exact hα1
      have hspace : Module.finrank F (Fin 5 → F) = 5 := Module.finrank_fin_fun F
      by_cases hd5 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 5
      · exfalso
        apply hα1'
        have htop : LinearMap.ker (toLin' B'.val - 1) = ⊤ :=
          Submodule.eq_top_of_finrank_eq (by rw [hd5, hspace])
        have h0 : toLin' B'.val - 1 = 0 := LinearMap.ker_eq_top.1 htop
        have h1' : toLin' B'.val = toLin' (1 : Matrix (Fin 5) (Fin 5) F) := by
          rw [Matrix.toLin'_one]
          exact sub_eq_zero.1 h0
        have hB1 : B' = 1 := Units.ext (Matrix.toLin'.injective h1')
        rw [hB1, map_one]
      by_cases hd0 : Module.finrank F (LinearMap.ker (toLin' B'.val + 1)) = 5
      · exfalso
        apply hα1'
        have htop : LinearMap.ker (toLin' B'.val + 1) = ⊤ :=
          Submodule.eq_top_of_finrank_eq (by rw [hd0, hspace])
        have h0 : toLin' B'.val + 1 = 0 := LinearMap.ker_eq_top.1 htop
        have h1' : toLin' B'.val = toLin' (-1 : Matrix (Fin 5) (Fin 5) F) := by
          rw [map_neg, Matrix.toLin'_one]
          exact eq_neg_of_add_eq_zero_left h0
        have hB1 : B' = -1 := by
          apply Units.ext
          rw [Units.val_neg, Units.val_one]
          exact Matrix.toLin'.injective h1'
        rw [hB1, conjAut_neg, map_one]
      have hBneg : (-B') * (-B') = 1 := by rw [neg_mul_neg, hBB]
      by_cases hd4 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 4
      · exact h4 F hK2 B' hBB hd4
      by_cases hd1 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 1
      · have hd4' : Module.finrank F (LinearMap.ker (toLin' ((-B' : GL (Fin 5) F).val) - 1)) =
            4 := by rw [hker]; omega
        have := h4 F hK2 (-B') hBneg hd4'
        rwa [conjAut_neg] at this
      by_cases hd3 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 3
      · rcases hc35 with h35 | h35
        · exact h3' F h35 B' hBB hd3
        · exact h3 F hK2 h35 B' hBB hd3
      have hd2 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 2 := by omega
      have hd3' : Module.finrank F (LinearMap.ker (toLin' ((-B' : GL (Fin 5) F).val) - 1)) =
          3 := by rw [hker]; omega
      rcases hc35 with h35 | h35
      · have := h3' F h35 (-B') hBneg hd3'
        rwa [conjAut_neg] at this
      · have := h3 F hK2 h35 (-B') hBneg hd3'
        rwa [conjAut_neg] at this
    · exfalso
      exact (Nat.not_even_iff_odd.2 hfodd)
        (linear_field_involution_descent hp hf hcard (by norm_num) A σ hσ hα).1
  · rw [pow_one] at hα hα1 ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 5 F), mul_one] at hα hα1 ⊢
      rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα with hA | hA
      · exact hO F hK2 A hA
      · exfalso
        have hd := congrArg Matrix.det hA
        rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hd
        have h5 : ((-1 : F)) ^ 5 = -1 := by norm_num
        rw [h5, neg_one_mul] at hd
        have h2 : (2 : F) * (A : Matrix (Fin 5) (Fin 5) F).det = 0 := by linear_combination hd
        have h20 : (2 : F) ≠ 0 := Ring.two_ne_zero hK2
        have hdet0 : (A : Matrix (Fin 5) (Fin 5) F).det = 0 :=
          (mul_eq_zero.1 h2).resolve_left h20
        refine (Matrix.GeneralLinearGroup.det A).ne_zero ?_
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        exact hdet0
    · exfalso
      exact (Nat.not_even_iff_odd.2 hfodd)
        (odd_linear_graph_field_involution_conjugacy hp hf hcard (by norm_num) A σ hσ hα).1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
