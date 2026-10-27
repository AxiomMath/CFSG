module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCOSign
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eComp

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e.Orth

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.C
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL signMat)
open CFSG.ComponentClassification.HarrisLit.T1.P51e.Comp (comp_map_mulEquiv)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem exists_sign_frame (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1) :
    ∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (J : Finset (Fin d))
      (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw)))
      (θ : StatedProj (matrixDerived (oQ R)) ≃* StatedProj (matrixDerived (oQ (diagGL hw)))),
      J.Nonempty ∧ Jᶜ.Nonempty ∧
      (∀ I : Finset (Fin d), (I = J ∨ I = Jᶜ) → 3 ≤ I.card → BlockNF w I) ∧
      θ (projH _ ⟨T, hT⟩) = projH _ ⟨signGL K J, hJ⟩ := by
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
  refine ⟨_, hw, famJ hab, hJ, oTransport S 1 hS, ?_, ?_, ?_, hθt⟩
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
    exact (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 ⟨-1, rfl⟩)
  · rintro I (rfl | rfl) h3
    · exact hNF₁ (by rw [card_famJ] at h3; exact h3)
    · apply hNF₂
      rw [Finset.card_compl, Fintype.card_fin, card_famJ] at h3
      omega

variable {w : Fin d → K} (hw : ∀ i, w i ≠ 0)

include hw in
theorem sign_comp_cases (hK : ringChar K ≠ 2) (J : Finset (Fin d))
    (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hJne : J.Nonempty) (hJcne : Jᶜ.Nonempty)
    {L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))}
    (hLH : L ≤ centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({projH _ ⟨signGL K J, hJ⟩} : Set _)))) :
    ∃ I : Finset (Fin d), (I = J ∨ I = Jᶜ) ∧ Iᶜ.Nonempty ∧ L ≤ blockP K hw I ∧
      ((L = blockP K hw I ∧ IsQuasisimple L ∧ 3 ≤ I.card) ∨
        (I.card = 4 ∧ Nat.card K ≠ 3 ∧ IsQuasisimple L ∧ Nonempty (L ≃* SL(2, K)))) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hsup := le_blockP_sup_of_perfect hw hK J hJ hLH (commutator_eq_of_isPComponent hLH hL)
  obtain ⟨I, hI, hLI⟩ : ∃ I, (I = J ∨ I = Jᶜ) ∧ L ≤ blockP K hw I := by
    rcases le_or_le_of_le_sup hLH hL (blockP_le_centralizer hw J J (Or.inl rfl) hJ)
      (blockP_le_centralizer hw J Jᶜ (Or.inr rfl) hJ)
      (isSubnormal_blockP hw hK J J (Or.inl rfl) hJ)
      (isSubnormal_blockP hw hK J Jᶜ (Or.inr rfl) hJ) hsup with h | h
    · exact ⟨J, Or.inl rfl, h⟩
    · exact ⟨Jᶜ, Or.inr rfl, h⟩
  have hIc : Iᶜ.Nonempty := by
    rcases hI with rfl | rfl
    · exact hJcne
    · rwa [compl_compl]
  refine ⟨I, hI, hIc, hLI, ?_⟩
  rcases comp_cases_of_le_blockP hw hK J I hI hJ hIc hLH hL hLI with ⟨hLe, hq⟩ | h
  · refine Or.inl ⟨hLe, by rw [hLe]; exact hq, three_le_card_of_isQuasisimple_blockP hw hIc h2 hq⟩
  · exact Or.inr h

omit [Finite K] in
include hw in
theorem even_card_of_mem_comp (hK : ringChar K ≠ 2) (J I : Finset (Fin d))
    (hI : I = J ∨ I = Jᶜ) (hJ : signGL K J ∈ matrixDerived (oQ (diagGL hw))) (hIc : Iᶜ.Nonempty)
    {L : Subgroup (StatedProj (matrixDerived (oQ (diagGL hw))))} (hLI : L ≤ blockP K hw I)
    (hzL : projH _ (⟨signGL K J, hJ⟩ : matrixDerived (oQ (diagGL hw))) ∈ L) : Even I.card :=
  even_card_of_sign_mem_oBlock hw hK (sign_mem_oBlock_of_mem_blockP hw J I hI hJ hIc (hLI hzL))

theorem sign_comp_cases_of_model (hK : ringChar K ≠ 2) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) {T : GL (Fin d) K}
    (hT : T ∈ matrixDerived (oQ R)) (hT2 : (T : Matrix (Fin d) (Fin d) K) * T = 1)
    (hT1 : projH _ (⟨T, hT⟩ : matrixDerived (oQ R)) ≠ 1)
    {L : Subgroup (StatedProj (matrixDerived (oQ R)))}
    (hLH : L ≤ centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))})
    (hL : IsPComponent 2 (L.subgroupOf (centralizer {projH _ (⟨T, hT⟩ : matrixDerived (oQ R))}))) :
    (∃ (w : Fin d → K) (hw : ∀ i, w i ≠ 0) (I : Finset (Fin d)), Iᶜ.Nonempty ∧ BlockNF w I ∧
        Nonempty (L ≃* blockP K hw I)) ∨ (Nat.card K ≠ 3 ∧ Nonempty (L ≃* SL(2, K))) := by
  obtain ⟨w, hw, J, hJ, θ, hJne, hJc, hNF, hθz⟩ := exists_sign_frame hK hR hT hT2 hT1
  obtain ⟨hLH', hL'⟩ := comp_map_mulEquiv θ hLH hL
  rw [hθz] at hLH' hL'
  let eL : L ≃* L.map θ.toMonoidHom := L.equivMapOfInjective θ.toMonoidHom θ.injective
  obtain ⟨I, hI, hIc, -, ⟨hLe, -, h3⟩ | ⟨-, hK3, -, ⟨e⟩⟩⟩ :=
    sign_comp_cases hw hK J hJ hJne hJc hLH' hL'
  · exact Or.inl ⟨w, hw, I, hIc, hNF I hI h3, ⟨eL.trans (MulEquiv.subgroupCongr hLe)⟩⟩
  · exact Or.inr ⟨hK3, ⟨eL.trans e⟩⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51e.Orth
