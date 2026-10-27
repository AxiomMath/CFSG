module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenRestrict
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLevi

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module Matrix
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type} [Field K]

@[expose] noncomputable def extMatHom :
    Matrix (Fin 3) (Fin 3) K →* Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) K where
  toFun A := fromBlocks A 0 0 1
  map_one' := fromBlocks_one
  map_mul' A B := by rw [fromBlocks_multiply]; simp

@[expose] noncomputable def extGL : GL (Fin 3) K →* GL (Fin 4) K :=
  Units.map ((reindexAlgEquiv K K finSumFinEquiv).toRingEquiv.toMonoidHom.comp extMatHom)

theorem finSumFinEquiv_symm_castSucc (i : Fin 3) :
    (finSumFinEquiv (m := 3) (n := 1)).symm i.castSucc = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

theorem extGL_apply (A : GL (Fin 3) K) (i j : Fin 4) :
    ((extGL A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
      fromBlocks (A : Matrix (Fin 3) (Fin 3) K) 0 0 1
        ((finSumFinEquiv (m := 3) (n := 1)).symm i) ((finSumFinEquiv (m := 3) (n := 1)).symm j) :=
  rfl

theorem extGL_castSucc_castSucc (A : GL (Fin 3) K) (i j : Fin 3) :
    ((extGL A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i.castSucc j.castSucc =
      (A : Matrix (Fin 3) (Fin 3) K) i j := by
  rw [extGL_apply, finSumFinEquiv_symm_castSucc, finSumFinEquiv_symm_castSucc, fromBlocks_apply₁₁]

theorem extGL_castSucc_last (A : GL (Fin 3) K) (i : Fin 3) :
    ((extGL A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i.castSucc (Fin.last 3) = 0 := by
  rw [extGL_apply, finSumFinEquiv_symm_castSucc, finSumFinEquiv_symm_last, fromBlocks_apply₁₂,
    Matrix.zero_apply]

theorem extGL_last_castSucc (A : GL (Fin 3) K) (j : Fin 3) :
    ((extGL A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (Fin.last 3) j.castSucc = 0 := by
  rw [extGL_apply, finSumFinEquiv_symm_castSucc, finSumFinEquiv_symm_last, fromBlocks_apply₂₁,
    Matrix.zero_apply]

theorem extGL_last_last (A : GL (Fin 3) K) :
    ((extGL A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) (Fin.last 3) (Fin.last 3) = 1 := by
  rw [extGL_apply, finSumFinEquiv_symm_last, fromBlocks_apply₂₂, one_apply_eq]

section Levi

variable {r : ℕ}

theorem levi_apply_eq (A : GL (Fin r) K) (v : Fin r ⊕ Fin r → K) :
    levi r K A v = blockDiagInv (A : Matrix (Fin r) (Fin r) K) *ᵥ v := rfl

theorem levi_single_inl_inl (A : GL (Fin r) K) (m k : Fin r) :
    levi r K A (Pi.single (.inl m) 1) (.inl k) = (A : Matrix (Fin r) (Fin r) K) k m := by
  rw [levi_apply_eq, mulVec_single_one, col_apply, blockDiagInv, fromBlocks_apply₁₁]

theorem levi_single_inl_inr (A : GL (Fin r) K) (m k : Fin r) :
    levi r K A (Pi.single (.inl m) 1) (.inr k) = 0 := by
  rw [levi_apply_eq, mulVec_single_one, col_apply, blockDiagInv, fromBlocks_apply₂₁,
    Matrix.zero_apply]

theorem levi_single_inr_inl (A : GL (Fin r) K) (m k : Fin r) :
    levi r K A (Pi.single (.inr m) 1) (.inl k) = 0 := by
  rw [levi_apply_eq, mulVec_single_one, col_apply, blockDiagInv, fromBlocks_apply₁₂,
    Matrix.zero_apply]

theorem levi_single_inr_inr (A : GL (Fin r) K) (m k : Fin r) :
    levi r K A (Pi.single (.inr m) 1) (.inr k) = ((A⁻¹ : GL (Fin r) K) : Matrix _ _ K) m k := by
  rw [levi_apply_eq, mulVec_single_one, col_apply, blockDiagInv, fromBlocks_apply₂₂,
    transpose_apply, coe_units_inv]

end Levi

variable {t : Module.End K (Fin 4 ⊕ Fin 4 → K)}

namespace Frame

variable (F : Frame (quadPlus 4 K) t)

@[expose] noncomputable def basis : Basis (Fin 4 ⊕ Fin 4) K (Fin 4 ⊕ Fin 4 → K) :=
  Basis.mk (linearIndependent_of_hyp F.polar_lr F.polar_ll F.polar_rr) (by
    rw [top_le_iff]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card (linearIndependent_of_hyp F.polar_lr F.polar_ll F.polar_rr),
      Fintype.card_sum, Fintype.card_fin, finrank_split])

theorem coe_basis : ⇑F.basis = F.b := Basis.coe_mk _ _

@[expose] noncomputable def phi : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  F.basis.equivFun.symm

theorem phi_apply (v : Fin 4 ⊕ Fin 4 → K) : F.phi v = ∑ z, v z • F.b z := by
  rw [phi, Basis.equivFun_symm_apply, coe_basis]

theorem phi_single (z : Fin 4 ⊕ Fin 4) : F.phi (Pi.single z 1) = F.b z := by
  rw [phi, Basis.equivFun_symm_single, coe_basis]

theorem phi_symm_b (z : Fin 4 ⊕ Fin 4) : F.phi.symm (F.b z) = Pi.single z 1 := by
  rw [LinearEquiv.symm_apply_eq, phi_single]

theorem quadPlus_phi (v : Fin 4 ⊕ Fin 4 → K) : quadPlus 4 K (F.phi v) = quadPlus 4 K v := by
  rw [phi_apply, map_sum_of_hyp F.polar_lr F.polar_ll F.polar_rr F.Q_b, quadPlus_apply]

end Frame

@[expose] noncomputable def leviConj (F : Frame (quadPlus 4 K) t) :
    GL (Fin 3) K →* ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
  (MulAut.conj F.phi).toMonoidHom.comp ((levi 4 K).comp extGL)

variable (F : Frame (quadPlus 4 K) t)

theorem leviConj_apply (A : GL (Fin 3) K) (v : Fin 4 ⊕ Fin 4 → K) :
    leviConj F A v = F.phi (levi 4 K (extGL A) (F.phi.symm v)) := rfl

theorem leviConj_mem (A : GL (Fin 3) K) :
    leviConj F A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  rw [leviConj_apply, F.quadPlus_phi,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (levi_mem_orthogonalGroup _),
    ← F.quadPlus_phi, LinearEquiv.apply_symm_apply]

theorem leviConj_e (A : GL (Fin 3) K) (i : Fin 3) :
    leviConj F A (F.e i) = ∑ k : Fin 3, (A : Matrix (Fin 3) (Fin 3) K) k i • F.e k := by
  rw [leviConj_apply, F.phi_symm_b, F.phi_apply, Fintype.sum_sum_type, Fin.sum_univ_castSucc]
  simp only [levi_single_inl_inl, levi_single_inl_inr, zero_smul, Finset.sum_const_zero,
    add_zero, extGL_castSucc_castSucc, extGL_last_castSucc]

theorem leviConj_f (A : GL (Fin 3) K) (i : Fin 3) :
    leviConj F A (F.f i) =
      ∑ k : Fin 3, ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i k • F.f k := by
  rw [leviConj_apply, F.phi_symm_b, F.phi_apply, Fintype.sum_sum_type, Fin.sum_univ_castSucc
    (f := fun k => levi 4 K (extGL A) (Pi.single (.inr i.castSucc) 1) (.inr k) • F.b (.inr k))]
  simp only [levi_single_inr_inl, levi_single_inr_inr, zero_smul, Finset.sum_const_zero,
    zero_add, ← map_inv, extGL_castSucc_castSucc, extGL_castSucc_last, add_zero]

theorem leviConj_w₁ (A : GL (Fin 3) K) : leviConj F A F.w₁ = F.w₁ := by
  rw [leviConj_apply, F.phi_symm_b, F.phi_apply, Fintype.sum_sum_type, Fin.sum_univ_castSucc]
  simp only [levi_single_inl_inl, levi_single_inl_inr, zero_smul, Finset.sum_const_zero,
    add_zero, zero_add, extGL_castSucc_last, extGL_last_last, one_smul]

theorem leviConj_w₂ (A : GL (Fin 3) K) : leviConj F A F.w₂ = F.w₂ := by
  rw [leviConj_apply, F.phi_symm_b, F.phi_apply, Fintype.sum_sum_type, Fin.sum_univ_castSucc
    (f := fun k => levi 4 K (extGL A) (Pi.single (.inr (Fin.last 3)) 1) (.inr k) • F.b (.inr k))]
  simp only [levi_single_inr_inl, levi_single_inr_inr, zero_smul, Finset.sum_const_zero,
    zero_add, ← map_inv, extGL_last_castSucc, extGL_last_last, one_smul]

theorem polar_leviConj_e_f (A : GL (Fin 3) K) (i j : Fin 3) :
    polar (quadPlus 4 K) (leviConj F A (F.e i)) (F.f j) = (A : Matrix (Fin 3) (Fin 3) K) j i := by
  rw [leviConj_e, CFSG.LocalAnalysis.ComponentInitial.polar_sum_smul_left]
  simp only [F.polar_e_f, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

section Stab

variable (h7 : t ^ 7 = 1) (h2 : (2 : K) = 0)
  (hQt : ∀ v, quadPlus 4 K (t v) = quadPlus 4 K v)
include h7 h2 hQt

theorem leviConj_apply_mem_spU₁ (A : GL (Fin 3) K) {x : Fin 4 ⊕ Fin 4 → K} (hx : x ∈ spU₁ t) :
    leviConj F A x ∈ spU₁ t := by
  rw [eq_sum_of_mem_spU₁ finrank_split h7 h2 hQt F hx, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul, leviConj_e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (F.mem_U₁ l))

theorem leviConj_apply_mem_spU₂ (A : GL (Fin 3) K) {y : Fin 4 ⊕ Fin 4 → K} (hy : y ∈ spU₂ t) :
    leviConj F A y ∈ spU₂ t := by
  rw [eq_sum_of_mem_spU₂ finrank_split h7 h2 hQt F hy, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [map_smul, leviConj_f]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (F.mem_U₂ l))

theorem map_leviConj_spU₁ (A : GL (Fin 3) K) :
    (spU₁ t).map (leviConj F A : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = spU₁ t := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact leviConj_apply_mem_spU₁ F h7 h2 hQt A hx
  · intro x hx
    refine ⟨leviConj F A⁻¹ x, leviConj_apply_mem_spU₁ F h7 h2 hQt A⁻¹ hx, ?_⟩
    change leviConj F A (leviConj F A⁻¹ x) = x
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one, id]

theorem map_leviConj_spU₂ (A : GL (Fin 3) K) :
    (spU₂ t).map (leviConj F A : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = spU₂ t := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact leviConj_apply_mem_spU₂ F h7 h2 hQt A hx
  · intro x hx
    refine ⟨leviConj F A⁻¹ x, leviConj_apply_mem_spU₂ F h7 h2 hQt A⁻¹ hx, ?_⟩
    change leviConj F A (leviConj F A⁻¹ x) = x
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, LinearEquiv.coe_one, id]

theorem leviConj_mem_levStab (A : GL (Fin 3) K) : leviConj F A ∈ levStab (quadPlus 4 K) t F :=
  mem_levStab.2 ⟨leviConj_mem F A, leviConj_w₁ F A, leviConj_w₂ F A,
    map_leviConj_spU₁ F h7 h2 hQt A, map_leviConj_spU₂ F h7 h2 hQt A⟩

theorem restrictGL_leviConj (A : GL (Fin 3) K) :
    restrictGL finrank_split h7 h2 hQt F ⟨leviConj F A, leviConj_mem_levStab F h7 h2 hQt A⟩ =
      A := by
  apply Units.ext
  ext j i
  rw [coe_restrictGL, restrictHom_apply]
  exact polar_leviConj_e_f F A i j

end Stab

end CFSG.AGLEmbedding.TrialityTwo.Seven
