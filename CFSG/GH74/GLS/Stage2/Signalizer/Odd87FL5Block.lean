module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K]

theorem det_blockGL {k m : ℕ} (X : GL (Fin k) K) :
    ((blockGL K k m X : GL (Fin (k + m)) K) : Matrix (Fin (k + m)) (Fin (k + m)) K).det =
      (X : Matrix (Fin k) (Fin k) K).det := by
  rw [coe_blockGL, Matrix.reindex_apply, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

variable (K) in
@[expose] noncomputable def slBlock (k m : ℕ) :
    SpecialLinearGroup (Fin k) K →* SpecialLinearGroup (Fin (k + m)) K where
  toFun g := ⟨(blockGL K k m (SpecialLinearGroup.toGL g) : Matrix (Fin (k + m)) (Fin (k + m)) K), by
    rw [det_blockGL]
    simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    simp only [map_mul, Units.val_mul]
    rfl)

theorem injective_proj_slBlock {k m : ℕ} (hm : 1 ≤ m) :
    Function.Injective ((proj (k + m) K).comp (slBlock K k m)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hg)
  by_contra hne
  have hne' : (SpecialLinearGroup.toGL g : GL (Fin k) K) ≠ 1 := fun h =>
    hne (SpecialLinearGroup.toGL_injective (h.trans (map_one _).symm))
  exact blockGL_ne_scalar_of_ne_one hm hne' c hc

theorem exists_fixed_sl3_block_of_sq (hK : ringChar K ≠ 2) (B : GL (Fin (3 + 2)) K) (hB : B * B = 1)
    (h3 : 3 ≤ finrank K (LinearMap.ker (toLin' B.val - 1))) :
    ∃ ρ : SpecialLinearGroup (Fin 3) K →* projectiveSL (3 + 2) K, Function.Injective ρ ∧
      ∀ g, conjAut (3 + 2) K B (ρ g) = ρ g := by
  have hBm : (B : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K) * B = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
  obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B
  set k := finrank K (LinearMap.ker (toLin' B.val - 1)) with hk
  set d : Fin (3 + 2) → K := fun i => if (i : ℕ) < k then 1 else -1 with hd
  have hDd : (D : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K) = diagonal d := by
    rw [hD]
    ext a c
    rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, map_smul, Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
    by_cases hac : a = c
    · subst hac
      simp [hd]
    · simp [hac, Ne.symm hac]
  have hconj : conjAut (3 + 2) K B =
      conjAut (3 + 2) K P * conjAut (3 + 2) K D * (conjAut (3 + 2) K P)⁻¹ := by
    rw [← hPD, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  set θ : SpecialLinearGroup (Fin 3) K →* projectiveSL (3 + 2) K :=
    (proj (3 + 2) K).comp (slBlock K 3 2) with hθ
  have hfixD : ∀ g, conjAut (3 + 2) K D (θ g) = θ g := by
    intro g
    refine (conjAut_proj D _).trans ?_
    show proj (3 + 2) K _ = proj (3 + 2) K _
    congr 1
    apply Subtype.ext
    refine (coe_slConjugation D _).trans ?_
    change (D : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K) *
        (blockGL K 3 2 (SpecialLinearGroup.toGL g) : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K) *
        ((D⁻¹ : GL (Fin (3 + 2)) K) : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K) = _
    rw [hDd, ← blockGL_mul_diagonal_comm, Matrix.mul_assoc, ← hDd, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.mul_one]
    · rfl
    · intro i j
      have hi : ((finSumFinEquiv (Sum.inl i : Fin 3 ⊕ Fin 2) : Fin (3 + 2)) : ℕ) < k := by
        simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
        omega
      have hj : ((finSumFinEquiv (Sum.inl j : Fin 3 ⊕ Fin 2) : Fin (3 + 2)) : ℕ) < k := by
        simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
        omega
      simp only [hd, hi, hj, ↓reduceIte]
  refine ⟨(conjAut (3 + 2) K P : MulAut (projectiveSL (3 + 2) K)).toMonoidHom.comp θ, ?_, ?_⟩
  · exact (conjAut (3 + 2) K P).injective.comp (injective_proj_slBlock (by norm_num))
  · intro g
    rw [hconj]
    change conjAut (3 + 2) K P (conjAut (3 + 2) K D ((conjAut (3 + 2) K P)⁻¹
      (conjAut (3 + 2) K P (θ g)))) = conjAut (3 + 2) K P (θ g)
    rw [MulAut.inv_apply_self, hfixD]

theorem exists_fixed_sl3_block [Finite K] (hK : ringChar K ≠ 2) (B : GL (Fin (3 + 2)) K)
    (hB : conjAut (3 + 2) K B ^ 2 = 1) :
    ∃ ρ : SpecialLinearGroup (Fin 3) K →* projectiveSL (3 + 2) K, Function.Injective ρ ∧
      ∀ g, conjAut (3 + 2) K B (ρ g) = ρ g := by
  have h1 : conjAut (3 + 2) K (B * B) * fieldAut (3 + 2) K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← sq, hB]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by norm_num) _ _ h1
  have hdet : ((B : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K).det) * (B : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K).det =
      (c : K) ^ 5 := by
    have h2 := congrArg (fun M : GL (Fin (3 + 2)) K => (M : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K).det) hc
    simp only [Units.val_mul, Matrix.det_mul, GeneralLinearGroup.coe_scalar, scalar_apply,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    exact h2.symm
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ * μ = c := by
    refine ⟨(B : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K).det / (c : K) ^ 2, ?_⟩
    field_simp
    rw [sq]
    exact hdet
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hμ
    exact hc0 hμ.symm
  set B' : GL (Fin (3 + 2)) K := GeneralLinearGroup.scalar (Fin (3 + 2)) (Units.mk0 μ hμ0)⁻¹ * B with hB'
  have hcB : conjAut (3 + 2) K B' = conjAut (3 + 2) K B := by
    rw [hB', map_mul, conjAut_scalar, one_mul]
  have hs : (Units.mk0 μ hμ0)⁻¹ * (Units.mk0 μ hμ0)⁻¹ * c = 1 := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_one]
    rw [← hμ]
    field_simp
  have hBB : B' * B' = 1 := by
    calc B' * B' = GeneralLinearGroup.scalar (Fin (3 + 2)) (Units.mk0 μ hμ0)⁻¹ *
          GeneralLinearGroup.scalar (Fin (3 + 2)) (Units.mk0 μ hμ0)⁻¹ * (B * B) := by
          rw [hB', mul_assoc, ← mul_assoc B, ← GeneralLinearGroup.scalar_commute]
          group
      _ = 1 := by rw [← hc, ← map_mul, ← map_mul, hs, map_one]
  have hBm : (B' : Matrix (Fin (3 + 2)) (Fin (3 + 2)) K) * B' = 1 := by
    rw [← Units.val_mul, hBB, Units.val_one]
  have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hK hBm)
  rw [finrank_fin_fun] at hsum
  by_cases h3 : 3 ≤ finrank K (LinearMap.ker (toLin' B'.val - 1))
  · obtain ⟨ρ, hinj, hfix⟩ := exists_fixed_sl3_block_of_sq hK B' hBB h3
    exact ⟨ρ, hinj, fun g => by rw [← hcB]; exact hfix g⟩
  · have hker : LinearMap.ker (toLin' ((-B' : GL (Fin (3 + 2)) K).val) - 1) =
        LinearMap.ker (toLin' B'.val + 1) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
        Module.End.one_apply, Units.val_neg, neg_mulVec]
      rw [← neg_add', neg_eq_zero]
    obtain ⟨ρ, hinj, hfix⟩ := exists_fixed_sl3_block_of_sq hK (-B') (by rw [neg_mul_neg, hBB])
      (by rw [hker]; omega)
    exact ⟨ρ, hinj, fun g => by rw [← hcB, ← conjAut_neg]; exact hfix g⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
