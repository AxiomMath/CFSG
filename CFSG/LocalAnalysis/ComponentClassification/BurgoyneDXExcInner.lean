module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcT1
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneDXExcTrans
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenInner

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C (signGL_empty)
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K]

theorem oκ_sgnPair_eq_one {d : ℕ} (h2 : (2 : K) ≠ 0) {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (hJ : J = ∅ ∨ J = Finset.univ) : oκ _ (sgnPair h2 hw J) = 1 := by
  rw [← map_one (oκ (oQ (diagGL hw)))]
  rcases hJ with rfl | rfl
  · refine oκ_eq_of_left_eq (c := 1) rfl ?_
    rw [map_one, one_mul]
    exact signGL_empty
  · refine oκ_eq_of_left_eq (c := -1) rfl ?_
    apply Units.ext
    change signMat K Finset.univ = _
    ext i j
    simp [signMat, Matrix.diagonal_apply]

theorem false_of_exc_inner [Finite K] (hK : ringChar K ≠ 2) {R : GL (Fin 8) K}
    (hR : (R : Matrix (Fin 8) (Fin 8) K)ᵀ = R) (hker : OKer (oQ R))
    {M : Subgroup (GL (Fin 8) K)} (hd : ExcData R M) {gs : similarityPairs (oQ R)}
    (hσ : gs.val.right = 1) (hss : oκ _ (gs * gs) = 1) (hs1 : oκ _ gs ≠ 1)
    (hQs : (M.subgroupOf (matrixDerived (oQ R))).map (projH _) ≤ autFixed (oκ _ gs))
    (hQc : IsPComponent 2 (((M.subgroupOf (matrixDerived (oQ R))).map (projH _)).subgroupOf
      (autFixed (oκ _ gs))))
    {A : GL (Fin 8) K} {a₀ : K} (ha₀ : a₀ ≠ 0)
    (hA2 : (A : Matrix (Fin 8) (Fin 8) K) * A = a₀ • 1)
    (hAR : (A : Matrix (Fin 8) (Fin 8) K)ᵀ * R = -((R : Matrix (Fin 8) (Fin 8) K) * A))
    (hAM : ∀ X ∈ M, A⁻¹ * X * A ∈ M)
    (hAS : ∃ ζ : Kˣ, A * gs.val.left = GeneralLinearGroup.scalar (Fin 8) ζ * (gs.val.left * A)) :
    False := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set H := matrixDerived (oQ R) with hH
  set S := gs.val.left with hSdef
  set Sm := (S : Matrix (Fin 8) (Fin 8) K) with hSm
  set Rm := (R : Matrix (Fin 8) (Fin 8) K) with hRm
  obtain ⟨c, hc0, hS2, hε, -⟩ := inner_even_data h2 hR (by norm_num) hker hσ hss
  have hperfH : ⁅M.subgroupOf H, M.subgroupOf H⁆ = M.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hd.le, hd.perf]
  have hfixP : ∀ X ∈ M.subgroupOf H, oκ _ gs (projH H X) = projH H X :=
    fun X hX => hQs ⟨X, hX, rfl⟩
  have hSSi : Sm * ((S⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) = 1 := by
    rw [hSm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hSiS : ((S⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) * Sm = 1 := by
    rw [hSm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSM : ∀ X ∈ M, Sm * (X : Matrix (Fin 8) (Fin 8) K) = X * Sm := by
    intro X hX
    have e := kappa_eq_of_fix gs hperfH hfixP (X := ⟨X, hd.le hX⟩) (mem_subgroupOf.2 hX)
    rw [hσ] at e
    have e2 : ((X : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K).map ⇑(1 : K ≃+* K) = X := by
      ext
      rfl
    change Sm * ((X : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K).map ⇑(1 : K ≃+* K) *
      ((S⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) = X at e
    rw [e2] at e
    calc Sm * (X : Matrix (Fin 8) (Fin 8) K) =
        (Sm * X * ((S⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)) * Sm := by
          rw [Matrix.mul_assoc _ _ Sm, hSiS, Matrix.mul_one]
      _ = X * Sm := by rw [e]
  obtain ⟨u₁, hu₁, u₂, hu₂, e₁, e₂, n₁, n₂, n₁₂, c₁₂⟩ := hd.klein
  have hu₃ : u₁ * u₂ ∈ M := mul_mem hu₁ hu₂
  have e₃ : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [c₁₂]
      _ = 1 := by rw [← mul_assoc, e₁, one_mul, e₂]
  have n₃ : u₁ * u₂ ≠ 1 := fun h =>
    n₁₂ ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right e₁)).symm
  have hk₁ := hd.par u₁ hu₁ e₁ n₁
  have hk₂ := hd.par u₂ hu₂ e₂ n₂
  have hk₃ := hd.par _ hu₃ e₃ n₃
  rw [Units.val_mul] at hk₃
  have hm₁ : (u₁ : Matrix (Fin 8) (Fin 8) K) * u₁ = 1 := by
    rw [← Units.val_mul, e₁, Units.val_one]
  have hm₂ : (u₂ : Matrix (Fin 8) (Fin 8) K) * u₂ = 1 := by
    rw [← Units.val_mul, e₂, Units.val_one]
  have hm₁₂ : (u₁ : Matrix (Fin 8) (Fin 8) K) * u₂ = u₂ * u₁ := by
    rw [← Units.val_mul, c₁₂, Units.val_mul]
  have hiso : ∀ m ∈ M, (m : Matrix (Fin 8) (Fin 8) K)ᵀ * Rm * m = Rm := fun m hm =>
    (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 ((mem_matrixIsometries_oQ h2 R hR m).1
      (matrixDerived_le_isometries _ (hd.le hm)))
  have hRdet : Rm.det ≠ 0 := (Matrix.isUnits_det_units R).ne_zero
  rcases hε with hε | hε
  swap
  ·
    have hSR : Smᵀ * Rm * Sm = (-c) • Rm := by
      rw [hε, Matrix.smul_mul, Matrix.mul_assoc, hS2, Matrix.mul_smul, Matrix.mul_one, smul_smul,
        neg_one_mul]
    exact false_of_klein_similitude h2 hR hRdet hm₁ hm₂ hm₁₂ (hiso u₁ hu₁) (hiso u₂ hu₂) hk₁ hk₂
      hk₃ (hSM u₁ hu₁) (hSM u₂ hu₂) hc0 hS2 hSR (Or.inl rfl)
  have hSR : Smᵀ * Rm * Sm = c • Rm := by
    rw [hε, one_smul, Matrix.mul_assoc, hS2, Matrix.mul_smul, Matrix.mul_one]
  by_cases hsq : IsSquare c
  swap
  · exact false_of_klein_similitude h2 hR hRdet hm₁ hm₂ hm₁₂ (hiso u₁ hu₁) (hiso u₂ hu₂) hk₁ hk₂
      hk₃ (hSM u₁ hu₁) (hSM u₂ hu₂) hc0 hS2 hSR (Or.inr ⟨rfl, hsq⟩)
  obtain ⟨s₀, hs₀⟩ := hsq
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hs₀, mul_zero])
  obtain ⟨S', hS'def⟩ : ∃ S' : GL (Fin 8) K,
      S' = GeneralLinearGroup.scalar (Fin 8) (Units.mk0 s₀ hs₀0)⁻¹ * S := ⟨_, rfl⟩
  have hS'c : (S' : Matrix (Fin 8) (Fin 8) K) = s₀⁻¹ • Sm := by
    rw [hS'def, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul,
      Units.val_inv_eq_inv_val, Units.val_mk0]
  have hS'R : (S' : Matrix (Fin 8) (Fin 8) K)ᵀ * Rm * S' = Rm := by
    rw [hS'c, transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hSR,
      smul_smul, smul_smul, hs₀]
    rw [show s₀⁻¹ * s₀⁻¹ * (s₀ * s₀) = 1 by field_simp, one_smul]
  have hS'2 : (S' : Matrix (Fin 8) (Fin 8) K) * S' = 1 := by
    rw [hS'c, Matrix.smul_mul, Matrix.mul_smul, hS2, smul_smul, smul_smul, hs₀]
    rw [show s₀⁻¹ * s₀⁻¹ * (s₀ * s₀) = 1 by field_simp, one_smul]
  have hS' : S' ∈ matrixIsometries (oQ R) :=
    (mem_matrixIsometries_oQ h2 R hR S').2
      ((CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hS'R)
  have hκ : oκ _ gs = oκ _ (linPair S' hS') := by
    refine oκ_eq_of_left_eq (c := Units.mk0 s₀ hs₀0) (by rw [hσ, linPair_right]) ?_
    rw [linPair_left, hS'def, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [hκ] at hQs hQc hs1
  have hS'M : ∀ X ∈ M, X * S' = S' * X := by
    intro X hX
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hS'c, Matrix.mul_smul, Matrix.smul_mul, hSM X hX]
  obtain ⟨ζ, hζ⟩ := hAS
  have hζm : (A : Matrix (Fin 8) (Fin 8) K) * Sm = (ζ : K) • (Sm * A) := by
    have e := congrArg Units.val hζ
    rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul] at e
    exact e
  have hζ2 : (ζ : K) * ζ = 1 := by
    have e1 : (A : Matrix (Fin 8) (Fin 8) K) * (Sm * Sm) =
        ((ζ : K) * ζ) • ((Sm * Sm) * A) := by
      calc (A : Matrix (Fin 8) (Fin 8) K) * (Sm * Sm) =
          ((A : Matrix (Fin 8) (Fin 8) K) * Sm) * Sm := by rw [Matrix.mul_assoc]
        _ = ((ζ : K) • (Sm * A)) * Sm := by rw [hζm]
        _ = (ζ : K) • (Sm * ((A : Matrix (Fin 8) (Fin 8) K) * Sm)) := by
            rw [Matrix.smul_mul, Matrix.mul_assoc]
        _ = (ζ : K) • (Sm * ((ζ : K) • (Sm * A))) := by rw [hζm]
        _ = ((ζ : K) * ζ) • ((Sm * Sm) * A) := by
            rw [Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    rw [hS2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul] at e1
    have hA0 : (A : Matrix (Fin 8) (Fin 8) K) ≠ 0 := by
      intro h0
      have := (Matrix.isUnits_det_units A).ne_zero
      rw [h0, det_zero] at this
      exact this rfl
    obtain ⟨i, j, hij⟩ : ∃ i j, (A : Matrix (Fin 8) (Fin 8) K) i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hA0 (Matrix.ext h)
    have e2 := congrFun (congrFun e1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e2
    have e3 : c = (ζ : K) * ζ * c := mul_right_cancel₀ hij e2
    have e4 : ((ζ : K) * ζ - 1) * c = 0 := by linear_combination -e3
    exact sub_eq_zero.1 ((mul_eq_zero.1 e4).resolve_right hc0)
  have hζS' : (A : Matrix (Fin 8) (Fin 8) K) * S' = (ζ : K) • ((S' : Matrix (Fin 8) (Fin 8) K) *
      A) := by
    rw [hS'c, Matrix.mul_smul, hζm, Matrix.smul_mul, smul_comm]
  obtain ⟨hab, cfr, hcA, horth, hdiag, hNFM, hNFP⟩ := exists_split_nf hK hR hS'R hS'2
  obtain ⟨hw, Str, hStr, heq⟩ := exists_transport_of_family h2 hS' hab cfr hcA horth hdiag
  set w := famW Rm hab cfr with hwdef
  set J := famJ hab with hJdef
  have hd' := hd.transport Str 1 hStr
  obtain ⟨-, hQc'⟩ := transport_comp hd.le Str 1 hStr hQs hQc
  rw [heq] at hQc'
  have hSJ : signGL K J = Str * S' * Str⁻¹ := by
    have e := congrArg (fun g : similarityPairs (oQ (diagGL hw)) => g.val.left) heq
    simp only [transPair_left, linPair_left, linPair_right, map_one, MulAut.one_apply] at e
    exact e.symm
  have hfix' : ∀ X ∈ M.map (MulAut.conj Str).toMonoidHom, X * signGL K J = signGL K J * X := by
    rintro _ ⟨Y, hY, rfl⟩
    rw [hSJ]
    change Str * Y * Str⁻¹ * (Str * S' * Str⁻¹) = Str * S' * Str⁻¹ * (Str * Y * Str⁻¹)
    have e := hS'M Y hY
    calc Str * Y * Str⁻¹ * (Str * S' * Str⁻¹) = Str * (Y * S') * Str⁻¹ := by group
      _ = Str * (S' * Y) * Str⁻¹ := by rw [e]
      _ = Str * S' * Str⁻¹ * (Str * Y * Str⁻¹) := by group
  have hne : oκ _ (sgnPair h2 hw J) ≠ 1 := by
    rw [hJdef, ← heq, ← oTransport_kappa]
    intro h1
    apply hs1
    exact (MulAut.congr (oTransport Str 1 hStr)).injective (by rw [h1, map_one])
  have hJ : J.Nonempty :=
    Finset.nonempty_iff_ne_empty.2 fun h => hne (oκ_sgnPair_eq_one h2 hw (Or.inl h))
  have hJc : Jᶜ.Nonempty := Finset.nonempty_iff_ne_empty.2 fun h =>
    hne (oκ_sgnPair_eq_one h2 hw (Or.inr (Finset.compl_eq_empty_iff _ |>.1 h)))
  have hNF : ∀ I : Finset (Fin 8), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I := by
    rintro I (rfl | rfl) h3
    · exact hNFM (by rw [hJdef, card_famJ] at h3; exact h3)
    · apply hNFP
      rw [Finset.card_compl, Fintype.card_fin, hJdef, card_famJ] at h3
      omega
  set Sm' := (Str : Matrix (Fin 8) (Fin 8) K) with hSm'
  set Sim := ((Str⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) with hSim
  have hSS : Sm' * Sim = 1 := by rw [hSm', hSim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hSiS : Sim * Sm' = 1 := by
    rw [hSm', hSim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcancel : ∀ X : Matrix (Fin 8) (Fin 8) K, Sim * (Sm' * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hSiS, Matrix.one_mul]
  obtain ⟨A', hA'def⟩ : ∃ A' : GL (Fin 8) K, A' = Str * A * Str⁻¹ := ⟨_, rfl⟩
  have hA'v : (A' : Matrix (Fin 8) (Fin 8) K) = Sm' * A * Sim := by
    rw [hA'def, Units.val_mul, Units.val_mul]
  have hA2' : (A' : Matrix (Fin 8) (Fin 8) K) * A' = a₀ • 1 := by
    rw [hA'v]
    simp only [Matrix.mul_assoc]
    rw [hcancel, ← Matrix.mul_assoc (A : Matrix (Fin 8) (Fin 8) K), hA2, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_smul, hSS]
  have hG : Sm'ᵀ * diagonal w * Sm' = Rm := by
    refine eq_of_forall_dotProduct_mulVec h2 ?_ hR fun v => ?_
    · rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose,
        Matrix.mul_assoc]
    · rw [dotProduct_transpose_mul_mul, ← coe_diagGL hw, ← oQ_apply, ← oQ_apply, hStr,
        Units.val_one, one_mul]
  have hDS : diagonal w * Sm' = Simᵀ * Rm := by
    rw [← hG, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, hSS, transpose_one,
      Matrix.one_mul]
  have hSD : Sm'ᵀ * diagonal w = Rm * Sim := by
    rw [← hG, Matrix.mul_assoc, hSS, Matrix.mul_one]
  have hAR' : (A' : Matrix (Fin 8) (Fin 8) K)ᵀ * diagonal w =
      -(diagonal w * (A' : Matrix (Fin 8) (Fin 8) K)) := by
    rw [hA'v]
    have hR' : diagonal w * (Sm' * (A : Matrix (Fin 8) (Fin 8) K) * Sim) =
        Simᵀ * (Rm * A * Sim) := by
      rw [Matrix.mul_assoc Sm', ← Matrix.mul_assoc (diagonal w), hDS, Matrix.mul_assoc,
        Matrix.mul_assoc Rm]
    rw [hR']
    calc (Sm' * (A : Matrix (Fin 8) (Fin 8) K) * Sim)ᵀ * diagonal w =
        Simᵀ * ((A : Matrix (Fin 8) (Fin 8) K)ᵀ * (Sm'ᵀ * diagonal w)) := by
          rw [transpose_mul, transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Simᵀ * (((A : Matrix (Fin 8) (Fin 8) K)ᵀ * Rm) * Sim) := by
          rw [hSD, Matrix.mul_assoc]
      _ = -(Simᵀ * (Rm * A * Sim)) := by
          rw [hAR, Matrix.neg_mul, Matrix.mul_neg]
  have hAM' : ∀ X ∈ M.map (MulAut.conj Str).toMonoidHom, A'⁻¹ * X * A' ∈
      M.map (MulAut.conj Str).toMonoidHom := by
    rintro _ ⟨Y, hY, rfl⟩
    refine ⟨A⁻¹ * Y * A, hAM Y hY, ?_⟩
    rw [hA'def]
    change Str * (A⁻¹ * Y * A) * Str⁻¹ = (Str * A * Str⁻¹)⁻¹ * (Str * Y * Str⁻¹) *
      (Str * A * Str⁻¹)
    group
  have hSJm : signMat K J = Sm' * S' * Sim := by
    rw [← coe_signGL, hSJ, Units.val_mul, Units.val_mul]
  have hAS' : A' * signGL K J = signGL K J * A' ∨
      (A' : Matrix (Fin 8) (Fin 8) K) * signMat K J = -(signMat K J * A') := by
    have e1 : (A' : Matrix (Fin 8) (Fin 8) K) * signMat K J =
        Sm' * ((A : Matrix (Fin 8) (Fin 8) K) * S') * Sim := by
      rw [hA'v, hSJm]
      simp only [Matrix.mul_assoc]
      rw [hcancel]
    have e2 : signMat K J * (A' : Matrix (Fin 8) (Fin 8) K) =
        Sm' * ((S' : Matrix (Fin 8) (Fin 8) K) * A) * Sim := by
      rw [hA'v, hSJm]
      simp only [Matrix.mul_assoc]
      rw [hcancel]
    rcases mul_self_eq_one_iff.1 hζ2 with h1 | h1
    · left
      apply Units.ext
      rw [Units.val_mul A' (signGL K J), Units.val_mul (signGL K J) A', coe_signGL, e1, e2, hζS',
        h1, one_smul]
    · right
      rw [e1, e2, hζS', h1, neg_one_smul, Matrix.mul_neg, Matrix.neg_mul]
  exact false_of_sign hK hw hd' hJ hJc hNF hfix' hQc' ha₀ hA2' hAR' hAM' hAS'

end CFSG.ComponentClassification.Burgoyne.DX
