module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Def

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kaAll_pl4 (h3 : KAL4B3) (h2 : KAL4B2) (h2' : KAL4B2Three) (hNS : KAL4NS)
    (hO : KAL4GOrth) (hO' : KAL4GOrthThree) (hS : KAL4GSp)
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f) (hfodd : Odd f) (hK2 : ringChar F ≠ 2)
    {α : MulAut (projectiveSL 4 F)} (hα2 : α * α = 1) (hα1 : α ≠ 1) : KAAll α := by
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
  obtain ⟨A, σ, ε, hε, hαeq⟩ := (automorphism_generation (K := F) (n := 4) (by norm_num)).2 α
  rw [hαeq] at hα hα1 ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα hα1 ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 4 F), mul_one] at hα hα1 ⊢
      have h1 : conjAut 4 F (A * A) * fieldAut 4 F 1 = 1 := by
        rw [map_one, mul_one, map_mul, ← sq, hα]
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1
      by_cases hsq : IsSquare (c : F)
      · obtain ⟨μ, hμ⟩ := hsq
        have hμ0 : μ ≠ 0 := by
          rintro rfl
          rw [zero_mul] at hμ
          exact c.ne_zero hμ
        set B' : GL (Fin 4) F :=
          GeneralLinearGroup.scalar (Fin 4) (Units.mk0 μ hμ0)⁻¹ * A with hB'
        have hcB : conjAut 4 F B' = conjAut 4 F A := by
          rw [hB', map_mul, conjAut_scalar, one_mul]
        have hs : (Units.mk0 μ hμ0)⁻¹ * (Units.mk0 μ hμ0)⁻¹ * c = 1 := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_one]
          rw [hμ]
          field_simp
        have hBB : B' * B' = 1 := by
          calc B' * B' = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 μ hμ0)⁻¹ *
                GeneralLinearGroup.scalar (Fin 4) (Units.mk0 μ hμ0)⁻¹ * (A * A) := by
                rw [hB', mul_assoc, ← mul_assoc A, ← GeneralLinearGroup.scalar_commute]
                group
            _ = 1 := by rw [← hc, ← map_mul, ← map_mul, hs, map_one]
        have hBm : (B' : Matrix (Fin 4) (Fin 4) F) * B' = 1 := by
          rw [← Units.val_mul, hBB, Units.val_one]
        have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hK2 hBm)
        rw [Module.finrank_fin_fun] at hsum
        have hker : LinearMap.ker (toLin' ((-B' : GL (Fin 4) F).val) - 1) =
            LinearMap.ker (toLin' B'.val + 1) := by
          ext v
          simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
            Module.End.one_apply, Units.val_neg, neg_mulVec]
          rw [← neg_add', neg_eq_zero]
        rw [← hcB]
        have hα1' : conjAut 4 F B' ≠ 1 := by rw [hcB]; exact hα1
        have hspace : Module.finrank F (Fin 4 → F) = 4 := Module.finrank_fin_fun F
        by_cases hd4 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 4
        · exfalso
          apply hα1'
          have htop : LinearMap.ker (toLin' B'.val - 1) = ⊤ :=
            Submodule.eq_top_of_finrank_eq (by rw [hd4, hspace])
          have h0 : toLin' B'.val - 1 = 0 := LinearMap.ker_eq_top.1 htop
          have h1' : toLin' B'.val = toLin' (1 : Matrix (Fin 4) (Fin 4) F) := by
            rw [Matrix.toLin'_one]
            exact sub_eq_zero.1 h0
          have hB1 : B' = 1 := Units.ext (Matrix.toLin'.injective h1')
          rw [hB1, map_one]
        by_cases hd0 : Module.finrank F (LinearMap.ker (toLin' B'.val + 1)) = 4
        · exfalso
          apply hα1'
          have htop : LinearMap.ker (toLin' B'.val + 1) = ⊤ :=
            Submodule.eq_top_of_finrank_eq (by rw [hd0, hspace])
          have h0 : toLin' B'.val + 1 = 0 := LinearMap.ker_eq_top.1 htop
          have h1' : toLin' B'.val = toLin' (-1 : Matrix (Fin 4) (Fin 4) F) := by
            rw [map_neg, Matrix.toLin'_one]
            exact eq_neg_of_add_eq_zero_left h0
          have hB1 : B' = -1 := by
            apply Units.ext
            rw [Units.val_neg, Units.val_one]
            exact Matrix.toLin'.injective h1'
          rw [hB1, conjAut_neg, map_one]
        have hBneg : (-B') * (-B') = 1 := by rw [neg_mul_neg, hBB]
        by_cases hd3 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 3
        · exact h3 F hK2 B' hBB hd3
        by_cases hd1 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 1
        · have hd3' : Module.finrank F (LinearMap.ker (toLin' ((-B' : GL (Fin 4) F).val) - 1)) =
              3 := by rw [hker]; omega
          have := h3 F hK2 (-B') hBneg hd3'
          rwa [conjAut_neg] at this
        have hd2 : Module.finrank F (LinearMap.ker (toLin' B'.val - 1)) = 2 := by omega
        rcases hc35 with h35 | h35
        · exact h2' F h35 B' hBB hd2
        · exact h2 F hK2 h35 B' hBB hd2
      · exact hNS F hK2 A c hc.symm hsq
    · exfalso
      exact (Nat.not_even_iff_odd.2 hfodd)
        (linear_field_involution_descent hp hf hcard (by norm_num) A σ hσ hα).1
  · rw [pow_one] at hα hα1 ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one (fieldAut 4 F), mul_one] at hα hα1 ⊢
      rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα with hA | hA
      · rcases hc35 with h | h
        · exact hO' F h A hA
        · exact hO F hK2 h A hA
      · exact hS F hK2 A hA
    · exfalso
      exact (Nat.not_even_iff_odd.2 hfodd)
        (odd_linear_graph_field_involution_conjugacy hp hf hcard (by norm_num) A σ hσ hα).1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
