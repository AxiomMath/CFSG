module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenREnnola
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaPlusChart

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Matrix
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  matrixDerived matrixProjectiveProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus minusIndexEquiv plusIndexEquiv coordinateQuadMinus_apply)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl incl_mk inclHom inclHom_val glIncl_val)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.Quasithin (perfectCore)

section PlusMain

variable {K : Type} [Field K] [CharP K 2] [Finite K] {m' : ℕ} {F : Type} [Field F] [Finite F]
  [CharP F 2] (E : EnnolaParam K F)

theorem plus_chart_of_two_le (hm' : 2 ≤ m') (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0)
    {k₀ : Subfield F}
    [CharP k₀ 2] (φ : K ≃+* k₀) (hE : ∀ p, E.ι p = ((φ p : k₀) : F)) :
    ∃ ρ : matrixProjectiveDerived (coordinateQuadMinus (m' + 1 + 1) F (by omega)
        ((φ 1 : k₀) : F) ((φ 1 : k₀) : F)) ≃* StatedOmega (StatedQuadPlus (m' + 1 + 1) F),
      ∀ t : Fin (m' + 1 + 1) → Fˣ, t 0 = 1 →
        ∃ hD : (isEnnolaFrame_plus (m' := m') hirr).torus E t ∈
            plusAnisoPerp (K := K) (m' + 1) 1 1,
          ((ρ (incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ 1) (φ 1))
              (plusAnisoPerpModelFieldEquiv (by omega) hirr φ ⟨_, hD⟩)) :
              StatedOmega (StatedQuadPlus (m' + 1 + 1) F)) :
              GL (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) =
            minusNeighbourDiag (RingHom.id F) 0 t := by
  set hF := isEnnolaFrame_plus (m' := m') hirr with hFdef
  set D := plusPairData (m := m' + 1) E hirr φ hE with hDdef
  obtain ⟨P, hPcol, hPiso⟩ := exists_gl_of_hypBasis' _ D.w D.quad_w D.polar_w
  set S : GL (Fin (2 * (m' + 1 + 1))) F := (plusReindexGL F (m' + 1)).symm P⁻¹ with hSdef
  have hRS : plusReindexGL F (m' + 1) S = P⁻¹ := MulEquiv.apply_symm_apply _ _
  have hS : ∀ v, coordinateQuadPlus (m' + 1 + 1) F
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixLinearIso S v) =
      ((1 : Fˣ) : F) * coordinateQuadMinus (m' + 1 + 1) F (by omega) ((φ 1 : k₀) : F)
        ((φ 1 : k₀) : F) v := by
    intro v
    rw [Units.val_one, one_mul]
    change coordinateQuadPlus (m' + 1 + 1) F ((S : Matrix _ _ F) *ᵥ v) = _
    have h1 : coordinateQuadPlus (m' + 1 + 1) F ((S : Matrix _ _ F) *ᵥ v) =
        StatedQuadPlus (m' + 1 + 1) F
          (((S : Matrix _ _ F) *ᵥ v) ∘ plusIndexEquiv (m' + 1 + 1)) := by
      rw [CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus_apply]
      rfl
    rw [h1, ← plusReindexGL_mulVec, hRS]
    have h2 := hPiso ((P⁻¹ : GL _ F) *ᵥ (v ∘ plusIndexEquiv (m' + 1 + 1)))
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h2
    rw [← h2, plusQ₂_apply]
    congr 1
    funext c
    simp
  set ρ := (CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv _ _ S 1
    hS).trans (statedOmegaPlusEquiv F (m' + 1 + 1) (by omega)).symm with hρ
  refine ⟨ρ, ?_⟩
  have hmem : ∀ t : Fin (m' + 1 + 1) → Fˣ, t 0 = 1 →
      hF.torus E t ∈ plusAnisoPerp (K := K) (m' + 1) 1 1 := by
    intro t ht
    have h := hF.torus_mem_fixVecBar E ht
    rw [plusFrameA_zero, plusFrameA'_zero, ← pairPerpOf_eq_fixVecBar] at h
    exact h
  set Ch : plusAnisoPerp (K := K) (m' + 1) 1 1 →* GL (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F :=
    (StatedOmega (StatedQuadPlus (m' + 1 + 1) F)).subtype.comp
      (ρ.toMonoidHom.comp ((incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega)
        (φ 1) (φ 1))).comp (plusAnisoPerpModelFieldEquiv (by omega) hirr φ).toMonoidHom)) with hCh
  set T : (Fin (m' + 1) → Fˣ) →* plusAnisoPerp (K := K) (m' + 1) 1 1 :=
    ((hF.torus E).comp consOneHom).codRestrict _
      (fun u => hmem _ (by rw [consOneHom_apply, Fin.cons_zero])) with hTdef
  have key : Ch.comp T = (minusNeighbourDiag (RingHom.id F) 0).comp consOneHom := by
    refine MonoidHom.pi_ext fun k x => ?_
    have hT : T (Pi.mulSingle k x) = ⟨_, plus_rotOmega_mem_plusAnisoPerp E hirr k x⟩ := by
      apply Subtype.ext
      change hF.torus E (consOneHom (Pi.mulSingle k x)) = _
      rw [consOneHom_mulSingle, hF.torus_mulSingle]
    simp only [MonoidHom.comp_apply]
    rw [hT, consOneHom_mulSingle]
    set G := hF.rotOmega E k.succ x with hG
    obtain ⟨B, hBmk, hBent⟩ := plusChain_entry (m := m' + 1) (F := F) (by omega) hirr φ
      ⟨_, plus_rotOmega_mem_plusAnisoPerp E hirr k x⟩ G (plus_rotOmega_mem_stabSub E hirr k x) rfl
    obtain ⟨C, hC⟩ := CFSG.RankThree.PartOne.KCOrthogonalDescent.exists_conj_mem_matrixDerived _ _
      S 1 hS B
    have hChv : Ch ⟨_, plus_rotOmega_mem_plusAnisoPerp E hirr k x⟩ =
        (((statedDerivedPlusEquiv F (m' + 1 + 1)).symm C :
          StatedOmega (StatedQuadPlus (m' + 1 + 1) F)) :
          GL (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) := by
      rw [hCh]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      rw [hBmk, hρ, MulEquiv.trans_apply,
        CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv_mk _ _ S 1 hS B
          C hC]
      congr 1
      rw [MulEquiv.symm_apply_eq]
      simp only [statedOmegaPlusEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rfl
    rw [hChv]
    set M := plusReindexGL F (m' + 1) (B : GL (Fin (2 * (m' + 1 + 1))) F) with hM
    have hMv : (M : Matrix (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1))
        (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) =
        plusStated φ (G.1 : (Fin (2 * (m' + 1 + 2)) → K) ≃ₗ[K] (Fin (2 * (m' + 1 + 2)) → K)) := by
      ext i j
      rw [hM, plusReindexGL_apply, hBent]
      rfl
    have hpa : D.pa k.castSucc = plusFrameA m' k.succ := plusPairA_castSucc k
    have hpb : D.pb k.castSucc = plusFrameA' m' k.succ := plusPairB_castSucc k
    have heig : ∀ l, (M : Matrix (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1))
        (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) *ᵥ (fun s => (P : Matrix (Fin (m' + 1 + 1) ⊕
          Fin (m' + 1 + 1)) (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) s l) =
        SymplecticPilot.diagSpEntry (Pi.mulSingle k.castSucc x) l • fun s =>
          (P : Matrix (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F)
            s l := by
      intro l
      have hcol : (fun s => (P : Matrix (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1))
          (Fin (m' + 1 + 1) ⊕ Fin (m' + 1 + 1)) F) s l) = D.w l := funext fun s => hPcol s l
      rw [hcol, hMv]
      refine D.mulVec_w
        (G.1 : (Fin (2 * (m' + 1 + 2)) → K) ≃ₗ[K] (Fin (2 * (m' + 1 + 2)) → K)).toLinearMap
        k.castSucc (plusPairUnit_castSucc k) x ?_ ?_ ?_ _
        (fun v hv => plusStated_mulVec_plusJ E φ hE _ hv) l
      · simp only [LinearEquiv.coe_coe]
        rw [hpa, hpb, hG, IsEnnolaFrame.coe_rotOmega, E.rotHom_left]
      · simp only [LinearEquiv.coe_coe]
        rw [hpa, hpb, hG, IsEnnolaFrame.coe_rotOmega, E.rotHom_right]
      · intro k' hk'
        have ho := D.orth k' k.castSucc hk'
        rw [hpa, hpb] at ho
        simp only [LinearEquiv.coe_coe]
        rw [hG, IsEnnolaFrame.coe_rotOmega]
        exact ⟨E.rotHom_of_perp (hF.unit k.succ) x ho.1 ho.2.1,
          E.rotHom_of_perp (hF.unit k.succ) x ho.2.2.1 ho.2.2.2⟩
    have hconj := inv_mul_mul_eq_of_eigen P M _ _ (minusNeighbourDiag_mulSingle_succ k x) heig
    have hRC : plusReindexGL F (m' + 1) (C : GL (Fin (2 * (m' + 1 + 1))) F) = P⁻¹ * M * P := by
      have hC' : (C : GL (Fin (2 * (m' + 1 + 1))) F) = S * (B : GL _ F) * S⁻¹ := hC
      rw [hC', map_mul, map_mul, map_inv, hRS, inv_inv]
    apply Units.ext
    ext i j
    rw [statedDerivedPlusEquiv_symm_entry, ← plusReindexGL_apply, hRC, hconj]
  intro t ht
  refine ⟨hmem t ht, ?_⟩
  have h := DFunLike.congr_fun key (Fin.tail t)
  have hTt : T (Fin.tail t) = ⟨_, hmem t ht⟩ := by
    apply Subtype.ext
    change hF.torus E (consOneHom (Fin.tail t)) = _
    rw [consOneHom_tail ht]
  simp only [MonoidHom.comp_apply] at h
  rw [hTt, consOneHom_tail ht] at h
  exact h

theorem top_le_iSup_plusTorus_of_two_le (hm : 2 ≤ m') (hirr : ∀ s : K, s ^ 2 + 1 * s + 1 ≠ 0) :
    ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam (K := F) k).map
      ((isEnnolaFrame_plus (m' := m') hirr).torus E) :
        Set (matrixProjectiveDerived (plusAnisoQuad K (m' + 1) 1 1)))) := by
  have hS := isHypSystem_plus (K := K) (m := m' + 1) 1 1
  have hP := isHypCoord_plusAnisoQuad (K := K) (m := m' + 1) 1 1 (⟨2, by omega⟩ : Fin (m' + 1))
  have he : hP.hypPair.e = plusHypE (K := K) (m := m' + 1) 2 := by
    rw [hP.hypPair_e, plusHypE_of_lt (by omega)]
  have hf : hP.hypPair.f = plusHypF (K := K) (m := m' + 1) 2 := by
    rw [hP.hypPair_f, plusHypF_of_lt (by omega)]
  have hA0 := polar_aniso_plusHyp (isAnisoCoord_plusAnisoQuad (K := K) (m := m' + 1) hirr)
    (i := 0) (fun j => fin_succ_succ_ne_zero' j) 2
  have hA1 := polar_aniso_plusHyp (isAnisoCoord_plusAnisoQuad_one (K := K) (m := m' + 1) hirr)
    (i := 1) (fun j h => by
      have := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_succ, Fin.val_one] at this
      omega) 2
  have hB := hS.polar_blockVec_of_ne 0 (l := 2) (by omega) (by omega)
  have hplane : ∀ i : Fin (m' + 2), i.val < 3 →
      (polar (plusAnisoQuad K (m' + 1) 1 1) (plusFrameA m' i) (plusHypE 2) = 0 ∧
        polar (plusAnisoQuad K (m' + 1) 1 1) (plusFrameA' m' i) (plusHypE 2) = 0) ∧
      (polar (plusAnisoQuad K (m' + 1) 1 1) (plusFrameA m' i) (plusHypF 2) = 0 ∧
        polar (plusAnisoQuad K (m' + 1) 1 1) (plusFrameA' m' i) (plusHypF 2) = 0) := by
    intro i hi
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · rw [plusFrameA_zero, plusFrameA'_zero]
      exact ⟨⟨hA0.1.1, hA0.2.1⟩, ⟨hA0.1.2, hA0.2.2⟩⟩
    · rw [plusFrameA_succ, plusFrameA'_succ]
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [Fin.cons_zero, Fin.cons_zero]
        exact ⟨⟨hA1.1.1, hA1.2.1⟩, ⟨hA1.1.2, hA1.2.2⟩⟩
      · have hj' : j'.val = 0 := by
          rw [Fin.val_succ, Fin.val_succ] at hi
          omega
        rw [Fin.cons_succ, Fin.cons_succ, hj']
        exact ⟨⟨hB.1, hB.2.2.1⟩, ⟨hB.2.1, hB.2.2.2⟩⟩
  refine (isEnnolaFrame_plus (m' := m') hirr).top_le_iSup_perfectCore_of_hypPair E (by omega)
    hP.hypPair (fun i hi => by rw [he]; exact (hplane i hi).1)
    (fun i hi => by rw [hf]; exact (hplane i hi).2) ?_
  rw [plusFrameA_zero, plusFrameA'_zero, ← pairPerpOf_eq_fixVecBar]
  exact Subgroup.isPerfect_iff.mp (isQuasisimple_plusAnisoPerp (m := m' + 1) (by omega) hirr).1

end PlusMain

theorem omegaPlusTwoEnnolaModelInputAt_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    OmegaPlusTwoEnnolaModelInputAt m hm := by
  intro K _ _ _ b c hirr hK2 F _ _ _ hF σ hσ k₀ _ hσk φ
  have hone : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by
    have := Fintype.ofFinite K
    have h := FiniteField.pow_card x
    rw [Fintype.card_eq_nat_card, hK2, _root_.sq] at h
    exact mul_left_cancel₀ hx (by rw [h, mul_one])
  obtain rfl : b = 1 := hone b (coeff_ne_zero_of_irreducible' hirr)
  obtain rfl : c = 1 := hone c (fun h0 => hirr 0 (by rw [h0]; ring))
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨E, hE⟩ := exists_ennolaParam hK2 hF hσ hσk φ
  set hFr := isEnnolaFrame_plus (K := K) (m' := m') hirr
  refine ⟨hFr.torus E, map_rootParam_plusTorus E hirr,
    fun k => hFr.exists_weyl E (Fin.cycleRange k), ?_,
    top_le_iSup_plusTorus_of_two_le E (by omega) hirr⟩
  obtain ⟨ρ, hρ⟩ := plus_chart_of_two_le E (by omega : 2 ≤ m') hirr φ hE
  exact ⟨ρ, fun t ht => hρ t ht⟩

theorem omegaPlusTwoEnnolaModelInputAt_three : OmegaPlusTwoEnnolaModelInputAt 3 le_rfl :=
  omegaPlusTwoEnnolaModelInputAt_of_three_le le_rfl

end CFSG.SeitzReduction.OmegaPilot
