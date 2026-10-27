module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquareLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearSemilinearConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {n : ℕ} {K : Type} [Field K]

@[expose] def signSL (S : Finset (Fin n)) (hS : Even S.card) : SpecialLinearGroup (Fin n) K :=
  ⟨signDiag S, by rw [det_signDiag, hS.neg_one_pow]⟩

theorem signSL_mul_self (S : Finset (Fin n)) (hS : Even S.card) :
    (signSL S hS * signSL S hS : SpecialLinearGroup (Fin n) K) = 1 :=
  Subtype.ext (signDiag_mul_self S)

theorem fieldAut_proj_signSL (σ : K ≃+* K) (S : Finset (Fin n)) (hS : Even S.card) :
    fieldAut n K σ (proj n K (signSL S hS)) = proj n K (signSL S hS) := by
  rw [fieldAut_proj]
  congr 1
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  change σ (signDiag S i j) = signDiag S i j
  rw [signDiag_apply]
  split_ifs <;> simp

theorem dualAut_proj_signSL (S : Finset (Fin n)) (hS : Even S.card) :
    dualAut n K (proj n K (signSL S hS)) = proj n K (signSL S hS) := by
  rw [dualAut_proj, inv_eq_of_mul_eq_one_right (signSL_mul_self S hS)]
  congr 1
  exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_transpose]; exact transpose_signDiag S)

theorem proj_signSL_ne_one (h2 : (2 : K) ≠ 0) {S : Finset (Fin n)} (hS : Even S.card)
    {i j : Fin n} (hi : i ∈ S) (hj : j ∉ S) : proj n K (signSL S hS) ≠ 1 := by
  intro h
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 h
  refine signDiag_ne_smul h2 hi hj (c : K) ?_
  change signDiag S = _ at hc
  rw [hc, scalar_apply, ← smul_one_eq_diagonal]

theorem exists_sign_four_group (hK : ringChar K ≠ 2) (hn : 3 ≤ n) :
    ∃ V : Subgroup (projectiveSL n K), CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧
      (∀ σ : K ≃+* K, ∀ v ∈ V, fieldAut n K σ v = v) ∧ ∀ v ∈ V, dualAut n K v = v := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [i₀, i₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [i₁, i₂, Fin.ext_iff]
  have hS₁ : Even ({i₀, i₁} : Finset (Fin n)).card := by rw [Finset.card_pair h01]; exact even_two
  have hS₂ : Even ({i₁, i₂} : Finset (Fin n)).card := by rw [Finset.card_pair h12]; exact even_two
  have hS₃ : Even ({i₀, i₂} : Finset (Fin n)).card := by rw [Finset.card_pair h02]; exact even_two
  set X : SpecialLinearGroup (Fin n) K := signSL {i₀, i₁} hS₁
  set Y : SpecialLinearGroup (Fin n) K := signSL {i₁, i₂} hS₂
  have hsd : symmDiff ({i₀, i₁} : Finset (Fin n)) {i₁, i₂} = {i₀, i₂} := by
    ext k
    simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
    by_cases hk0 : k = i₀ <;> by_cases hk1 : k = i₁ <;> by_cases hk2 : k = i₂ <;> simp_all
  have hXY : X * Y = signSL {i₀, i₂} hS₃ := by
    refine Subtype.ext ?_
    change signDiag _ * signDiag _ = signDiag _
    rw [CLSFourGroupScalarSquare.signDiag_mul_signDiag, hsd]
  set x := proj n K X
  set y := proj n K Y
  have hx : x * x = 1 := by rw [← map_mul, signSL_mul_self, map_one]
  have hy : y * y = 1 := by rw [← map_mul, signSL_mul_self, map_one]
  have hxy : x * y = y * x := by
    rw [← map_mul, ← map_mul]
    exact congrArg (proj n K) (Subtype.ext (signDiag_comm _ _))
  have hx1 : x ≠ 1 := proj_signSL_ne_one h2 hS₁ (i := i₀) (j := i₂) (by simp)
    (by simp [h12.symm, Ne.symm h02])
  have hy1 : y ≠ 1 := proj_signSL_ne_one h2 hS₂ (i := i₁) (j := i₀) (by simp) (by simp [h01, h02])
  have hne : x ≠ y := by
    intro h
    have h1 : proj n K (X * Y) = 1 := by rw [map_mul]; change x * y = 1; rw [h, hy]
    rw [hXY] at h1
    exact proj_signSL_ne_one h2 hS₃ (i := i₀) (j := i₁) (by simp) (by simp [h01.symm, h12]) h1
  obtain ⟨V, hVmem, -, hV, hVcard⟩ := FourGroup.exists_kleinFour hx hy hxy hx1 hy1 hne
  have hfx : ∀ σ : K ≃+* K, fieldAut n K σ x = x := fun σ => fieldAut_proj_signSL σ _ hS₁
  have hfy : ∀ σ : K ≃+* K, fieldAut n K σ y = y := fun σ => fieldAut_proj_signSL σ _ hS₂
  have hdx : dualAut n K x = x := dualAut_proj_signSL _ hS₁
  have hdy : dualAut n K y = y := dualAut_proj_signSL _ hS₂
  refine ⟨V, hV, hVcard, fun σ v hv => ?_, fun v hv => ?_⟩
  · rcases hVmem v hv with rfl | rfl | rfl | rfl
    · exact map_one _
    · exact hfx σ
    · exact hfy σ
    · rw [map_mul, hfx σ, hfy σ]
  · rcases hVmem v hv with rfl | rfl | rfl | rfl
    · exact map_one _
    · exact hdx
    · exact hdy
    · rw [map_mul, hdx, hdy]

open CFSG.ComponentClassification.CatalogueBLinearSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
  CFSG.ComponentClassification.CatalogueBHigherLinearField

theorem projEquiv_semilinearAction (A : GL (Fin n) K) (σ : K ≃+* K)
    (x : ProjectiveSpecialLinearGroup (Fin n) K) :
    LinearCover.projectiveSpecialLinearEquivProjectiveSL n K (semilinearAction n K A σ x) =
      (conjAut n K A * fieldAut n K σ)
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (SpecialLinearGroup (Fin n) K)) x
  rw [semilinearAction_mk]
  rfl

theorem congr_semilinearAction (A : GL (Fin n) K) (σ : K ≃+* K) :
    MulAut.congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
        (semilinearAction n K A σ) = conjAut n K A * fieldAut n K σ := by
  ext x
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    projEquiv_semilinearAction, MulEquiv.apply_symm_apply]

theorem field_involution_conjugacy [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) :
    ∃ H : GL (Fin n) K,
      conjAut n K A * fieldAut n K σ = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
  set Ψ := MulAut.congr (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K) with hΨ
  have hsq : semilinearAction n K A σ ^ 2 = 1 := by
    apply Ψ.injective
    rw [map_pow, congr_semilinearAction, hα, map_one]
  obtain ⟨-, -, H, hH⟩ := odd_linear_field_involution_conjugacy n K p f hp
    (hp.odd_of_ne_two hp2) hf hK (by omega) (Or.inl hn) A σ hσ hsq
  have hI : Ψ (innerDiagonalAction n K H) = conjAut n K H := by
    rw [← semilinearAction_one_field, congr_semilinearAction, map_one, mul_one]
  have hF : Ψ (pslFieldAut (Fin n) K σ) = fieldAut n K σ := by
    have h1 : semilinearAction n K 1 σ = pslFieldAut (Fin n) K σ := by
      change innerDiagonalAction n K 1 * pslFieldAut (Fin n) K σ = _
      rw [map_one, one_mul]
    rw [← h1, congr_semilinearAction, map_one, one_mul]
  refine ⟨H, ?_⟩
  have h := congrArg Ψ hH
  rw [congr_semilinearAction, map_mul, map_mul, map_inv, hI, hF] at h
  exact h

theorem transpose_eq_or_eq_neg_of_sq [Finite K] (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hα : (conjAut n K A * fieldAut n K 1 * dualAut n K) ^ 2 = 1) :
    (A : Matrix (Fin n) (Fin n) K)ᵀ = A ∨ (A : Matrix (Fin n) (Fin n) K)ᵀ = -A := by
  rw [sq_conjAut_fieldAut_dualAut] at hα
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ hα
  have hmap : ∀ X : GL (Fin n) K, GeneralLinearGroup.map ((1 : K ≃+* K) : K →+* K) X = X :=
    fun X => Units.ext (by ext i j; rfl)
  rw [hmap] at hc
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with hMdef
  set N : Matrix (Fin n) (Fin n) K := ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hNdef
  have hMN : M * N = 1 := by rw [hMdef, hNdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * M = 1 := by rw [hMdef, hNdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hscal : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [smul_one_eq_diagonal]
    rfl
  have hc' : (c : K) • (1 : Matrix (Fin n) (Fin n) K) = M * Nᵀ := by
    rw [← hscal, hc, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose]
  have h1 : M = (c : K) • Mᵀ := by
    calc M = M * (M * N)ᵀ := by rw [hMN, transpose_one, Matrix.mul_one]
      _ = (M * Nᵀ) * Mᵀ := by rw [transpose_mul, Matrix.mul_assoc]
      _ = (c : K) • Mᵀ := by rw [← hc', Matrix.smul_mul, Matrix.one_mul]
  have h2 : Mᵀ = (c : K) • M := by
    conv_lhs => rw [h1]
    rw [transpose_smul, transpose_transpose]
  have hM0 : M ≠ 0 := by
    intro h0
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    rw [h0, Matrix.zero_mul] at hMN
    exact zero_ne_one hMN
  have hcc : (c : K) * c = 1 := by
    have h3 : ((c : K) * c - 1) • M = 0 := by
      rw [sub_smul, one_smul, mul_smul, ← h2, ← h1, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hM0
  rcases mul_self_eq_one_iff.1 hcc with h | h
  · left
    rw [h2, h, one_smul]
  · right
    rw [h2, h, neg_one_smul]

theorem exists_fixed_four_group_projectiveSL [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (β : MulAut (projectiveSL n K))
    (hβ : β ^ 2 = 1) :
    ∃ V : Subgroup (projectiveSL n K), V ≤ fixedSubgroup β ∧ CFSG.IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  classical
  have hodd : Odd (Nat.card K) := by rw [hK]; exact (hp.odd_of_ne_two hp2).pow
  have hK2 : ringChar K ≠ 2 :=
    CFSG.ComponentClassification.CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hodd
  obtain ⟨V₀, hV₀ab, hV₀card, hV₀f, hV₀d⟩ := exists_sign_four_group (K := K) hK2 hn
  have hconj : ∀ (H : GL (Fin n) K) (γ : MulAut (projectiveSL n K)), (∀ v ∈ V₀, γ v = v) →
      β = conjAut n K H * γ * (conjAut n K H)⁻¹ →
      ∃ V : Subgroup (projectiveSL n K), V ≤ fixedSubgroup β ∧ CFSG.IsElementaryAbelian 2 V ∧
        Nat.card V = 4 := by
    intro H γ hγ hβH
    refine ⟨V₀.map (conjAut n K H).toMonoidHom, ?_, CFSG.IsElementaryAbelian.map _, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      change β (conjAut n K H v) = conjAut n K H v
      rw [hβH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
        hγ v hv]
    · rw [Subgroup.card_map_of_injective (f := (conjAut n K H).toMonoidHom)
        (MulEquiv.injective _), hV₀card]
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform β
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hβ ⊢
    by_cases hσ : σ = 1
    ·
      subst hσ
      have h1 : conjAut n K (A * A) * fieldAut n K 1 = 1 := by
        rw [map_one, mul_one, map_mul, ← pow_two]
        rw [map_one, mul_one] at hβ
        exact hβ
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (A * A) 1 h1
      have hscal : ((GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
        rw [smul_one_eq_diagonal]
        rfl
      have hAc : (A : Matrix (Fin n) (Fin n) K) * A = (c : K) • 1 := by
        rw [← hscal, hc, Units.val_mul]
      obtain ⟨W, hWle, hWab, hWcard⟩ :=
        CLSFourGroupScalarSquare.odd_scalar_square_linear_centralizer_projective_four_group hK2
          hn A c hAc
      refine ⟨W, fun x hx => ?_, hWab, hWcard⟩
      obtain ⟨g, hg, rfl⟩ := hWle hx
      change (conjAut n K A * fieldAut n K 1) (proj n K g) = proj n K g
      rw [map_one, mul_one, conjAut_proj]
      congr 1
      refine Subtype.ext ?_
      rw [coe_slConjugation, ← CLSFourGroupScalarSquare.mem_centralizerSL.1 hg, Matrix.mul_assoc,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    ·
      obtain ⟨H, hH⟩ := field_involution_conjugacy hp hp2 hf hK hn A σ hσ hβ
      exact hconj H (fieldAut n K σ) (hV₀f σ) hH
  ·
    rw [pow_one] at hβ ⊢
    by_cases hσ : σ = 1
    ·
      subst hσ
      set R : GL (Fin n) K := A⁻¹ with hRdef
      have hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R ∨ (R : Matrix (Fin n) (Fin n) K)ᵀ = -R := by
        have hRA : (R : Matrix (Fin n) (Fin n) K) * A = 1 := by
          rw [hRdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
        have hAR : (A : Matrix (Fin n) (Fin n) K) * R = 1 := by
          rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hRAt : (R : Matrix (Fin n) (Fin n) K)ᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
          rw [← transpose_mul, hAR, transpose_one]
        rcases transpose_eq_or_eq_neg_of_sq hn A hβ with h | h
        · left
          calc (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K)ᵀ * (A * R) := by
                rw [hAR, Matrix.mul_one]
            _ = ((R : Matrix (Fin n) (Fin n) K)ᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ) * R := by
                rw [h, Matrix.mul_assoc]
            _ = R := by rw [hRAt, Matrix.one_mul]
        · right
          calc (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K)ᵀ * (A * R) := by
                rw [hAR, Matrix.mul_one]
            _ = -(((R : Matrix (Fin n) (Fin n) K)ᵀ * (A : Matrix (Fin n) (Fin n) K)ᵀ) * R) := by
                rw [h, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_neg]
            _ = -R := by rw [hRAt, Matrix.one_mul]
      obtain ⟨V, hVle, hVab, hVcard⟩ := odd_bilinear_isometry_projective_four_group hK2 hn R hR
      refine ⟨V, fun x hx => ?_, hVab, hVcard⟩
      obtain ⟨g, hg, rfl⟩ := hVle hx
      change (conjAut n K A * fieldAut n K 1 * dualAut n K) (proj n K g) = proj n K g
      rw [map_one, mul_one, MulAut.mul_apply, dualAut_proj, conjAut_proj]
      congr 1
      refine Subtype.ext ?_
      rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
      have hgI : (g : Matrix (Fin n) (Fin n) K)ᵀ * R * g = R := mem_isometrySL.1 hg
      have hgg : (g : Matrix (Fin n) (Fin n) K) * ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
      have hAR : (A : Matrix (Fin n) (Fin n) K) * R = 1 := by
        rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc (A : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = A * (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
              ((g : Matrix (Fin n) (Fin n) K)ᵀ * R * g)) := by
            rw [hgI, Matrix.mul_assoc]
        _ = A * (((g : Matrix (Fin n) (Fin n) K) *
              ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))ᵀ * R * g) := by
            rw [transpose_mul]
            simp only [Matrix.mul_assoc]
        _ = (A * R) * g := by rw [hgg, transpose_one, Matrix.one_mul, Matrix.mul_assoc]
        _ = g := by rw [hAR, Matrix.one_mul]
    ·
      obtain ⟨-, -, H, hH⟩ := odd_linear_graph_field_involution_conjugacy hp hf hK hn A σ hσ hβ
      exact hconj H (fieldAut n K σ * dualAut n K)
        (fun v hv => by rw [MulAut.mul_apply, hV₀d v hv, hV₀f σ v hv]) hH

theorem odd_higher_linear_all_involution_fixed_four_group (L : Type) [Group L] {p f n : ℕ}
    (hp : p ≠ 2) (hn : 3 ≤ n) (hL : StatedClassicalModel L .PSL n p f) (α : MulAut L)
    (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 := by
  obtain ⟨⟨hprime, hf, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  set ψ : L ≃* projectiveSL n K :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)) with hψ
  set β : MulAut (projectiveSL n K) := MulAut.congr ψ α with hβdef
  have hβ : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hα, map_one]
  obtain ⟨V, hVfix, hVab, hVcard⟩ := exists_fixed_four_group_projectiveSL hprime hp hf hK hn β hβ
  refine ⟨V.map ψ.symm.toMonoidHom, ?_, CFSG.IsElementaryAbelian.map _, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    change α (ψ.symm y) = ψ.symm y
    have h1 : β y = y := hVfix hy
    rw [hβdef, MulAut.congr_apply] at h1
    have h2 := congrArg ψ.symm h1
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    exact h2
  · rw [Subgroup.card_map_of_injective ψ.symm.injective]
    exact hVcard

theorem odd_higher_linear_all_involution_fixed_four_group_of_classicalModel (L : Type)
    [Group L] {p f n : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hn : 3 ≤ n)
    (hL : CFSG.Assembly.ComponentType.ClassicalModel L .PSL n p f) (α : MulAut L)
    (hα : α ^ 2 = 1) :
    ∃ V : Subgroup L, V ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4 :=
  odd_higher_linear_all_involution_fixed_four_group L hp hn
    (CFSG.ComponentClassification.ClassicalModelStatedBridge.statedClassicalModel_of_classicalModel
      .PSL n p f hL) α hα

end CFSG.LocalAnalysis.ComponentInitial.OddHigherLinear
