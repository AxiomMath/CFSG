module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.UnitaryFourTorus
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.OddLie.DiagBlockOrder

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie

open CFSG.Open CFSG.GH74.Filter.ClassicalOdd CFSG.SectionRank.ClassicalOdd Matrix

theorem exists_orderOf_sixteen_PSU_four {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (h16 : 16 ∣ (p ^ f) ^ 2 - 1) :
    ∃ x : StatedProj (StatedSU 4 (p ^ f) K), orderOf x = 16 := by
  set σ := iterateFrobenius K p f with hσdef
  have hσ : ∀ x, σ x = x ^ (p ^ f) := fun x => frob_apply x
  have hσσ : ∀ x, σ (σ x) = x := frob_frob hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  obtain ⟨u, -, hu, -, -⟩ := exists_unitary_elems hp2 hK
  have hσu : σ u * u = -1 := by rw [hσ]; exact hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hσu
  obtain ⟨t, ht⟩ := exists_units_orderOf (F := K) (d := 16) (by rw [hK]; exact h16)
  have ht16 : t ^ 16 = 1 := ht ▸ pow_orderOf_eq_one t
  set s : Kˣ := (Units.map (σ : K →* K) t)⁻¹ with hs
  have hsv : (s : K) = (σ (t : K))⁻¹ := by
    simp [hs]
  have htne : σ (t : K) ≠ 0 := by
    rw [hσ]
    exact pow_ne_zero _ t.ne_zero
  have hxy : σ (t : K) * s = 1 := by rw [hsv, mul_inv_cancel₀ htne]
  have hyx : σ (s : K) * t = 1 := by
    rw [hsv, map_inv₀, hσσ, inv_mul_cancel₀ t.ne_zero]
  have hs16 : s ^ 16 = 1 := by
    rw [hs, inv_pow, ← map_pow, ht16, map_one, inv_one]
  set A : GL (Fin 2) K := torusHom u h2 hu0 (t, s) with hA
  have hAord : orderOf A = 16 := by
    rw [hA, orderOf_injective _ (torusHom_injective u h2 hu0), Prod.orderOf, ht]
    exact Nat.lcm_eq_left (orderOf_dvd_of_pow_eq_one hs16)
  have hdet : Matrix.GeneralLinearGroup.det A = t * s := det_torusHom u h2 hu0 t s
  have hmem : diag22 (A, diagOneHom (Matrix.GeneralLinearGroup.det A)⁻¹) ∈
      StatedSU 4 (p ^ f) K := by
    refine Subgroup.subset_closure ⟨det_diag22_det_inv A, ?_⟩
    have hfun : (fun x : K => x ^ (p ^ f)) = σ := funext fun x => (hσ x).symm
    change ((diag22 (A, diagOneHom (Matrix.GeneralLinearGroup.det A)⁻¹) :
      Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).map (fun x : K => x ^ (p ^ f)))ᵀ * _ = 1
    rw [hfun, coe_diag22]
    refine IsUni.diagBlock (σ := σ) (isUni_torusMat h2 hu0 hσu hxy hyx) ?_
    rw [coe_diagOneHom]
    refine isUni_diagonal_one ?_
    rw [hdet]
    have h1 : σ (t : K) * σ (s : K) * ((t : K) * s) = 1 := by
      linear_combination (σ (s : K) * t) * hxy + hyx
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, map_inv₀, map_mul]
    rw [← mul_inv, h1, inv_one]
  obtain ⟨x, hx⟩ := exists_orderOf_statedProj_diag (H := StatedSU 4 (p ^ f) K) A hmem
  exact ⟨x, hx.trans hAord⟩

end CFSG.EvenSporadicStandard.M12Std.SolomonK.OddLie
