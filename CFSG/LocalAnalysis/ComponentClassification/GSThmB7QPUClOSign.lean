module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOInnerNF

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)

variable {K : Type} [Field K] {d : ℕ}

theorem exists_lift_sq (h2 : (2 : K) ≠ 0) (hd : 0 < d) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {t : StatedProj (matrixDerived (oQ R))}
    (ht2 : t * t = 1) :
    ∃ (T : GL (Fin d) K) (hT : T ∈ matrixDerived (oQ R)), t = projH _ ⟨T, hT⟩ ∧
      ((T : Matrix (Fin d) (Fin d) K) * T = 1 ∨ (T : Matrix (Fin d) (Fin d) K) * T = -1) := by
  obtain ⟨⟨T, hT⟩, rfl⟩ := projH_surjective t
  refine ⟨T, hT, rfl, ?_⟩
  have h1 : (⟨T, hT⟩ * ⟨T, hT⟩ : matrixDerived (oQ R)) ∈
      (StatedScalars (Fin d) K).subgroupOf (matrixDerived (oQ R)) := by
    rw [← map_mul] at ht2
    exact (QuotientGroup.eq_one_iff _).1 ht2
  rw [mem_subgroupOf] at h1
  obtain ⟨c, hc⟩ := h1
  have hTT : (T : Matrix (Fin d) (Fin d) K) * T = (c : K) • 1 := by
    have e := congrArg Units.val hc
    rw [GeneralLinearGroup.coe_scalar] at e
    change Matrix.scalar (Fin d) (c : K) = ((T * T : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) at e
    rw [← Units.val_mul, ← e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hTiso := (mem_matrixIsometries_oQ h2 R hR T).1 (matrixDerived_le_isometries _ hT)
  rw [CatalogueBGraphForm.mem_isometryGroup] at hTiso
  set Tm := (T : Matrix (Fin d) (Fin d) K) with hTm
  set Rm := (R : Matrix (Fin d) (Fin d) K) with hRm
  have e : (Tm * Tm)ᵀ * Rm * (Tm * Tm) = Rm := by
    rw [Matrix.transpose_mul]
    calc Tmᵀ * Tmᵀ * Rm * (Tm * Tm) = Tmᵀ * (Tmᵀ * Rm * Tm) * Tm := by
          simp only [Matrix.mul_assoc]
      _ = Rm := by rw [hTiso, hTiso]
  rw [hTT, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at e
  have hc2 : (c : K) * c = 1 := by
    have e' := congrArg (fun M => M * ((R⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) e
    simp only [hRm, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one] at e'
    have := congrFun (congrFun e' ⟨0, hd⟩) ⟨0, hd⟩
    simpa using this
  rcases mul_self_eq_one_iff.1 hc2 with h | h
  · left
    rw [hTT, h, one_smul]
  · right
    rw [hTT, h, neg_one_smul]

theorem projH_scalar_eq_one {Q : QuadraticForm K (Fin d → K)} (c : Kˣ)
    (h : GeneralLinearGroup.scalar (Fin d) c ∈ matrixDerived Q) :
    projH _ (⟨GeneralLinearGroup.scalar (Fin d) c, h⟩ : matrixDerived Q) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ⟨c, rfl⟩)

theorem exists_sign_model [Finite K] (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R)) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1) :
    ∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d))
      (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
      (θ : StatedProj (matrixDerived (oQ R)) ≃* StatedProj (matrixDerived (oQ (diagGL hw)))),
      OKer (oQ (diagGL hw)) ∧ J.Nonempty ∧ Jᶜ.Nonempty ∧
      (∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I) ∧
      θ (projH _ ⟨T, hT⟩) = projH _ ⟨signGL K J, hJ⟩ ∧
      ∀ g : similarityPairs (oQ R), ∃ g' : similarityPairs (oQ (diagGL hw)),
        MulAut.congr θ (oκ _ g) = oκ _ g' := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hTiso : T ∈ matrixIsometries (oQ R) := matrixDerived_le_isometries _ hT
  have hTR : (T : Matrix (Fin d) (Fin d) K)ᵀ * R * T = R :=
    (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1
      ((mem_matrixIsometries_oQ h2 R hR T).1 hTiso)
  obtain ⟨hab, cfr, hcA, horth, hdiag, hNF₁, hNF₂⟩ := exists_split_nf hK hR hTR hT2
  obtain ⟨hw, S, hS, heq⟩ := exists_transport_of_family h2 hTiso hab cfr hcA horth hdiag
  have hST : S * T * S⁻¹ = signGL K (famJ hab) := by
    have e := congrArg (fun g : similarityPairs (oQ (diagGL hw)) => g.val.left) heq
    simp only [transPair_left, linPair_left, linPair_right, map_one, MulAut.one_apply] at e
    rw [sgnPair, linPair_left] at e
    exact e
  have hXv : ((derivedTransport S 1 hS ⟨T, hT⟩ : matrixDerived (oQ (diagGL hw))) :
      GL (Fin d) K) = signGL K (famJ hab) := by
    rw [coe_derivedTransport]
    exact hST
  have hJ : signGL K (famJ hab) ∈ matrixDerived (oQ (diagGL hw)) :=
    hXv ▸ (derivedTransport S 1 hS ⟨T, hT⟩).2
  have hθt : oTransport S 1 hS (projH _ ⟨T, hT⟩) = projH _ ⟨signGL K (famJ hab), hJ⟩ := by
    rw [oTransport_proj]
    congr 1
    exact Subtype.ext hXv
  have hθ1 : oTransport S 1 hS (projH _ ⟨T, hT⟩) ≠ 1 := fun h1 =>
    hT1 ((oTransport S 1 hS).injective (by rw [h1, map_one]))
  refine ⟨_, hw, famJ hab, hJ, oTransport S 1 hS, hker.transport S 1 hS, ?_, ?_, ?_, hθt,
    fun g => ⟨transPair S 1 hS g, oTransport_kappa S 1 hS g⟩⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hJe
    apply hθ1
    rw [hθt]
    have e : (⟨signGL K (famJ hab), hJ⟩ : matrixDerived (oQ (diagGL hw))) = 1 := by
      apply Subtype.ext
      apply Units.ext
      change ((signGL K (famJ hab) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1
      rw [coe_signGL, hJe]
      ext i j
      simp [signMat, Matrix.diagonal_apply, Matrix.one_apply]
    rw [e, map_one]
  · rw [Finset.nonempty_iff_ne_empty]
    intro hJe
    apply hθ1
    rw [hθt]
    have hJu : famJ hab = Finset.univ := (Finset.compl_eq_empty_iff _).1 hJe
    have hsc : signGL K (famJ hab) = GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) := by
      apply Units.ext
      rw [coe_signGL, GeneralLinearGroup.coe_scalar, hJu]
      ext i j
      simp [signMat, Matrix.diagonal_apply, Matrix.scalar_apply]
    have hmem : GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ) ∈ matrixDerived (oQ (diagGL hw)) :=
      hsc ▸ hJ
    have e : (⟨signGL K (famJ hab), hJ⟩ : matrixDerived (oQ (diagGL hw))) =
        ⟨GeneralLinearGroup.scalar (Fin d) (-1 : Kˣ), hmem⟩ := Subtype.ext hsc
    rw [e]
    exact projH_scalar_eq_one (-1) hmem
  · rintro I (rfl | rfl) h3
    · exact hNF₁ (by rw [card_famJ] at h3; exact h3)
    · apply hNF₂
      rw [Finset.card_compl, Fintype.card_fin, card_famJ] at h3
      omega

end CFSG.ComponentClassification.GSThmB.QPUCl
