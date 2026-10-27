module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticBound

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOddQuadratic

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_eq_zero_of_mem_span_of_orth {P R : HypPair Q} (h : P.Orth R) {x : V}
    (hx : x ∈ Submodule.span K {R.e, R.f}) : polar Q P.e x = 0 ∧ polar Q P.f x = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp only [polar_add_right, polar_smul_right_eq, h.ee, h.ef, h.fe, h.ff, mul_zero, add_zero,
    and_self]

theorem iSupIndep_span_of_hypPair_orth {ι : Type*} {P : ι → HypPair Q}
    (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    iSupIndep fun i => Submodule.span K {(P i).e, (P i).f} := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  have hpair : ∀ w : V, (∀ j ∈ s, j ≠ i → polar Q w (v j) = 0) →
      polar Q w (v i) = 0 := by
    intro w hw
    have h0 : polarBilin Q w (∑ j ∈ s, v j) = 0 := by rw [hsum, map_zero]
    rw [map_sum, Finset.sum_eq_single i] at h0
    · rwa [polarBilin_apply_apply] at h0
    · intro j hj hji
      rw [polarBilin_apply_apply]
      exact hw j hj hji
    · exact fun h => absurd hi h
  have he := hpair (P i).e fun j hj hji =>
    (polar_eq_zero_of_mem_span_of_orth (hP i j (Ne.symm hji)) (hv j hj)).1
  have hf := hpair (P i).f fun j hj hji =>
    (polar_eq_zero_of_mem_span_of_orth (hP i j (Ne.symm hji)) (hv j hj)).2
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hv i hi)
  rw [← hab] at he hf ⊢
  simp only [polar_add_right, polar_smul_right_eq, (P i).polar_ee, (P i).polar_ef,
    (P i).polar_fe, (P i).polar_ff, mul_zero, mul_one, zero_add, add_zero] at he hf
  rw [he, hf, zero_smul, zero_smul, add_zero]

variable [Finite K] [FiniteDimensional K V]

theorem finite_odd_quadratic_low_Witt_dimension_bound (hodd : Odd (Nat.card K))
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) :
    (3 ≤ Module.finrank K V → ∃ v : V, v ≠ 0 ∧ Q v = 0) ∧
    (∃ (m : ℕ) (P : Fin m → HypPair Q) (A : Submodule K V),
      (∀ i j, i ≠ j → (P i).Orth (P j)) ∧
      (∀ i, Module.finrank K (Submodule.span K {(P i).e, (P i).f}) = 2 ∧
        Nonempty ((hyperbolicPairForm K).IsometryEquiv
          (Q.restrict (Submodule.span K {(P i).e, (P i).f})))) ∧
      iSupIndep (fun i => Submodule.span K {(P i).e, (P i).f}) ∧
      A = ⨅ i, (P i).perp ∧
      A = LinearMap.BilinForm.orthogonal Q.polarBilin
        (⨆ i, Submodule.span K {(P i).e, (P i).f}) ∧
      IsCompl (⨆ i, Submodule.span K {(P i).e, (P i).f}) A ∧
      (Q.restrict A).Anisotropic ∧ Module.finrank K A ≤ 2 ∧
      Module.finrank K V = 2 * m + Module.finrank K A ∧
      Nonempty (Q.IsometryEquiv ((hyperbolicSumForm K m).prod (Q.restrict A)))) ∧
    ((¬ ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) →
      Module.finrank K V ≤ 6) := by
  refine ⟨exists_isotropic_of_three_le hodd Q hQ, ?_,
    finrank_le_six_of_no_totallySingular_three hodd Q hQ⟩
  obtain ⟨m, P, A, hA2, hani, hdim, horth, hplanes, hperp, hcompl, hIsCompl, he⟩ :=
    exists_original_hyperbolic_decomposition hodd Q hQ
  exact ⟨m, P, A, horth, hplanes, iSupIndep_span_of_hypPair_orth horth, hperp, hcompl,
    hIsCompl, hani, hA2, hdim, he⟩

end CFSG.LocalAnalysis.ComponentInitial
