module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenRFrame
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenRNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl)

open CFSG.Quasithin (perfectCore) in
@[expose] def OmegaMinusTwoEnnolaModelInputAt (r : ℕ) (hr : 3 ≤ r) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 → ∀ σ : F ≃+* F,
    orderOf σ = 2 → ∀ (k₀ : Subfield F) [CharP k₀ 2], (∀ x, x ∈ k₀ ↔ σ x = x) →
    ∀ φ : K ≃+* k₀,
    ∃ τ : (Fin (r + 1) → Fˣ) →*
        matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c),
      (rootParam 0).map τ = anisoTorus (K := K) (by omega) b c ∧
      (∀ k : Fin (r + 1), ∃ w, ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) ∧
      (∃ g ∈ normalizer (StatedOmega (StatedQuadPlus (r + 1) F) :
          Set (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)),
        ∀ t : Fin (r + 1) → Fˣ, t 0 = 1 → ∃ hD : τ t ∈ anisoPerp (K := K) (by omega) b c,
          g * (((statedOmegaPlusEquiv F (r + 1) (by omega)).symm
            (incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (r + 1) k₀)
              (plusCongr φ (r + 1) (anisoPerpModelEquiv (n := r + 2) (by omega) hirr
                ⟨τ t, hD⟩))) : StatedOmega (StatedQuadPlus (r + 1) F)) :
              GL (Fin (r + 1) ⊕ Fin (r + 1)) F) * g⁻¹ =
            minusNeighbourDiag (RingHom.id F) 0 t) ∧
      ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam k).map τ :
        Set (matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))))

open CFSG.Quasithin (perfectCore) in
@[expose] def OmegaPlusTwoEnnolaModelInputAt (m : ℕ) (hm : 3 ≤ m) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 → ∀ σ : F ≃+* F,
    orderOf σ = 2 → ∀ (k₀ : Subfield F) [CharP k₀ 2], (∀ x, x ∈ k₀ ↔ σ x = x) →
    ∀ φ : K ≃+* k₀,
    ∃ τ : (Fin (m + 1) → Fˣ) →* matrixProjectiveDerived (plusAnisoQuad K m b c),
      (rootParam 0).map τ = plusAnisoTorus m hirr ∧
      (∀ k : Fin (m + 1), ∃ w, ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) ∧
      (∃ ρ : matrixProjectiveDerived (coordinateQuadMinus (m + 1) F (by omega)
          ((φ b : k₀) : F) ((φ c : k₀) : F)) ≃* StatedOmega (StatedQuadPlus (m + 1) F),
        ∀ t : Fin (m + 1) → Fˣ, t 0 = 1 → ∃ hD : τ t ∈ plusAnisoPerp (K := K) m b c,
          ((ρ (incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))
              (plusAnisoPerpModelFieldEquiv (by omega) hirr φ ⟨τ t, hD⟩)) :
              StatedOmega (StatedQuadPlus (m + 1) F)) : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) =
            minusNeighbourDiag (RingHom.id F) 0 t) ∧
      ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam k).map τ :
        Set (matrixProjectiveDerived (plusAnisoQuad K m b c))))

section Transport

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2] {k₀ : Subfield F} [CharP k₀ 2]

open CFSG.Quasithin (perfectCore) in
theorem perfectCore_modelToG_ten {P : Type*} [Group P] [Finite P] (e : L ≃* P)
    (B : Subgroup P) : perfectCore (modelToG e B) = modelToG e (perfectCore B) := by
  rw [modelToG, modelToG, ← CFSG.Quasithin.map_perfectCore, ← CFSG.Quasithin.map_perfectCore]

open CFSG.Quasithin (perfectCore) in
theorem q2FrameDataGen_of_minusModel {r : ℕ} (hr : 2 ≤ r) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))
    (φ : K ≃+* k₀)
    (τm : (Fin (r + 1) → Fˣ) →*
      matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))
    (hX : (rootParam 0).map τm = anisoTorus (K := K) (by omega) b c)
    (hW : ∀ k : Fin (r + 1), ∃ w, ∀ s, w * τm s * w⁻¹ = τm (s ∘ Fin.cycleRange k))
    {g : GL (Fin (r + 1) ⊕ Fin (r + 1)) F}
    (hg : g ∈ normalizer (StatedOmega (StatedQuadPlus (r + 1) F) :
      Set (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)))
    (hval : ∀ t : Fin (r + 1) → Fˣ, t 0 = 1 → ∃ hD : τm t ∈ anisoPerp (K := K) (by omega) b c,
      g * (((statedOmegaPlusEquiv F (r + 1) (by omega)).symm
        (incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (r + 1) k₀)
          (plusCongr φ (r + 1) (anisoPerpModelEquiv (n := r + 2) (by omega) hirr
            ⟨τm t, hD⟩))) : StatedOmega (StatedQuadPlus (r + 1) F)) :
          GL (Fin (r + 1) ⊕ Fin (r + 1)) F) * g⁻¹ =
        minusNeighbourDiag (RingHom.id F) 0 t)
    (hgen : ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam k).map τm :
      Set (matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c)))))
    (hDE : modelToG e (anisoPerp (K := K) (by omega) b c) ≤
      centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by omega) b c)))
    (πn : centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by omega) b c)) ≃*
      matrixProjectiveDerived (coordinateQuadPlus (r + 2 - 1) F))
    (hπn : ∀ d, πn (Subgroup.inclusion hDE d) =
      incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (r + 2 - 1) k₀)
        (anisoPerpFieldEquivN (by omega) hirr e φ d)) :
    Q2FrameDataGen L (modelToG e (anisoTorus (K := K) (by omega) b c)) r F := by
  set τ : (Fin (r + 1) → Fˣ) →* G := (L.subtype.comp e.symm.toMonoidHom).comp τm with hτ
  have hmapτ : ∀ P : Subgroup (Fin (r + 1) → Fˣ), P.map τ = modelToG e (P.map τm) := by
    intro P
    rw [modelToG, Subgroup.map_map, Subgroup.map_map]
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · rw [hmapτ, hX]
  · intro k
    obtain ⟨w, hw⟩ := hW k
    refine ⟨((e.symm w : L) : G), (e.symm w).2, fun s' => ?_⟩
    change ((e.symm w : L) : G) * ((e.symm (τm s') : L) : G) * ((e.symm w : L) : G)⁻¹ =
      ((e.symm (τm (s' ∘ Fin.cycleRange k)) : L) : G)
    rw [← hw, map_mul, map_mul, map_inv]
    rfl
  · let S := StatedOmega (StatedQuadPlus (r + 1) F)
    refine ⟨πn.trans ((statedOmegaPlusEquiv F (r + 1) (by omega)).symm.trans
      (S.normalizerMonoidHom ⟨g, hg⟩)), fun t' ht' => ?_⟩
    obtain ⟨hD, hv⟩ := hval t' ht'
    have hτD : τ t' ∈ modelToG e (anisoPerp (K := K) _ b c) := symm_mem_modelToG e hD
    refine ⟨hDE hτD, ?_⟩
    have h1 : (⟨τ t', hDE hτD⟩ : centralizerPerfectCore (modelToG e (anisoTorus (K := K) _ b c))) =
        Subgroup.inclusion hDE ⟨τ t', hτD⟩ := rfl
    have h2 : (modelToGEquiv e (anisoPerp (K := K) _ b c)).symm ⟨τ t', hτD⟩ = ⟨τm t', hD⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have h3 := hπn ⟨τ t', hτD⟩
    rw [anisoPerpFieldEquivN, MulEquiv.trans_apply, MulEquiv.trans_apply, h2] at h3
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, h3,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hv
  · have hgen' : modelToG e (⊤ : Subgroup (matrixProjectiveDerived
        (coordinateQuadMinus (r + 2) K (by omega) b c))) ≤
        modelToG e (⨆ k, CFSG.Quasithin.perfectCore (centralizer ((rootParam k).map τm :
          Set (matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))))) :=
      UnitaryPilot.modelToG_mono e hgen
    rw [UnitaryPilot.modelToG_top, UnitaryPilot.modelToG_iSup] at hgen'
    refine hgen'.trans (iSup_le fun k => le_iSup_of_le k ?_)
    rw [hmapτ, UnitaryPilot.inf_centralizer_modelToG, perfectCore_modelToG_ten]

open CFSG.Quasithin (perfectCore) in
theorem q2FrameDataGen_of_plusModel {m : ℕ} (hm : 3 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e' : L ≃* matrixProjectiveDerived (plusAnisoQuad K m b c)) (φ : K ≃+* k₀)
    (τm : (Fin (m + 1) → Fˣ) →* matrixProjectiveDerived (plusAnisoQuad K m b c))
    (hX : (rootParam 0).map τm = plusAnisoTorus m hirr)
    (hW : ∀ k : Fin (m + 1), ∃ w, ∀ s, w * τm s * w⁻¹ = τm (s ∘ Fin.cycleRange k))
    (ρ : matrixProjectiveDerived (coordinateQuadMinus (m + 1) F (by omega)
      ((φ b : k₀) : F) ((φ c : k₀) : F)) ≃* StatedOmega (StatedQuadPlus (m + 1) F))
    (hval : ∀ t : Fin (m + 1) → Fˣ, t 0 = 1 → ∃ hD : τm t ∈ plusAnisoPerp (K := K) m b c,
      ((ρ (incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))
          (plusAnisoPerpModelFieldEquiv (by omega) hirr φ ⟨τm t, hD⟩)) :
          StatedOmega (StatedQuadPlus (m + 1) F)) : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) =
        minusNeighbourDiag (RingHom.id F) 0 t)
    (hgen : ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam k).map τm :
      Set (matrixProjectiveDerived (plusAnisoQuad K m b c)))))
    (hDE : modelToG (e') (plusAnisoPerp (K := K) m b c) ≤
      centralizerPerfectCore (modelToG (e')
        (plusAnisoTorus m hirr)))
    (πn : centralizerPerfectCore (modelToG (e')
        (plusAnisoTorus m hirr)) ≃*
      matrixProjectiveDerived (coordinateQuadMinus (m + 1) F (by omega)
        ((φ b : k₀) : F) ((φ c : k₀) : F)))
    (hπn : ∀ d, πn (Subgroup.inclusion hDE d) =
      incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))
        (plusAnisoPerpFieldEquiv (by omega) hirr (e')
          φ d)) :
    Q2FrameDataGen L (modelToG (e')
      (plusAnisoTorus m hirr)) m F := by
  set τ : (Fin (m + 1) → Fˣ) →* G := (L.subtype.comp e'.symm.toMonoidHom).comp τm with hτ
  have hmapτ : ∀ P : Subgroup (Fin (m + 1) → Fˣ), P.map τ = modelToG e' (P.map τm) := by
    intro P
    rw [modelToG, Subgroup.map_map, Subgroup.map_map]
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · rw [hmapτ, hX]
  · intro k
    obtain ⟨w, hw⟩ := hW k
    refine ⟨((e'.symm w : L) : G), (e'.symm w).2, fun s' => ?_⟩
    change ((e'.symm w : L) : G) * ((e'.symm (τm s') : L) : G) * ((e'.symm w : L) : G)⁻¹ =
      ((e'.symm (τm (s' ∘ Fin.cycleRange k)) : L) : G)
    rw [← hw, map_mul, map_mul, map_inv]
    rfl
  · refine ⟨πn.trans ρ, fun t' ht' => ?_⟩
    obtain ⟨hD, hv⟩ := hval t' ht'
    have hτD : τ t' ∈ modelToG e' (plusAnisoPerp (K := K) m b c) := symm_mem_modelToG e' hD
    refine ⟨hDE hτD, ?_⟩
    have h1 : (⟨τ t', hDE hτD⟩ : centralizerPerfectCore (modelToG e' (plusAnisoTorus m hirr))) =
        Subgroup.inclusion hDE ⟨τ t', hτD⟩ := rfl
    have h2 : (modelToGEquiv e' (plusAnisoPerp (K := K) m b c)).symm ⟨τ t', hτD⟩ =
        ⟨τm t', hD⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have h3 := hπn ⟨τ t', hτD⟩
    rw [plusAnisoPerpFieldEquiv, MulEquiv.trans_apply, h2] at h3
    rw [MulEquiv.trans_apply, h1]
    exact (congrArg (fun x => ((ρ x : StatedOmega (StatedQuadPlus (m + 1) F)) :
      GL (Fin (m + 1) ⊕ Fin (m + 1)) F)) h3).trans hv
  · have hgen' : modelToG e' (⊤ : Subgroup (matrixProjectiveDerived (plusAnisoQuad K m b c))) ≤
        modelToG e' (⨆ k, CFSG.Quasithin.perfectCore (centralizer ((rootParam k).map τm :
          Set (matrixProjectiveDerived (plusAnisoQuad K m b c))))) :=
      UnitaryPilot.modelToG_mono e' hgen
    rw [UnitaryPilot.modelToG_top, UnitaryPilot.modelToG_iSup] at hgen'
    refine hgen'.trans (iSup_le fun k => le_iSup_of_le k ?_)
    rw [hmapτ, UnitaryPilot.inf_centralizer_modelToG, perfectCore_modelToG_ten]

end Transport

theorem omegaMinusTwoTenFieldFrameGenInput_of_model (h : OmegaMinusTwoEnnolaModelInputAt 3 le_rfl)
    (hnorm : OmegaMinusTwoTenNormalizedInput) : OmegaMinusTwoTenFieldFrameGenInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF : Nat.card F = 4 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι (f := 1) (by rw [hK2]; rfl) hσ hfix]
    norm_num
  have : CharP ι.fieldRange 2 := RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  obtain ⟨τm, hX, hW, ⟨g, hg, hval⟩, hgen⟩ :=
    h K b c hirr hK2 F hF σ hσ ι.fieldRange hσk ι.rangeRestrictFieldEquiv
  obtain ⟨hDE, πn, hπn⟩ := hnorm G L hset K b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
    F hF σ hσ ι.fieldRange hσk ι.rangeRestrictFieldEquiv
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    q2FrameDataGen_of_minusModel (r := 3) (by norm_num) hirr e ι.rangeRestrictFieldEquiv τm hX hW
      hg hval hgen hDE πn hπn⟩

section PlusTen

theorem omegaPlusTwoTenFieldFrameGenInput_of_model (h : OmegaPlusTwoEnnolaModelInputAt 3 le_rfl) :
    OmegaPlusTwoTenFieldFrameGenInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn htX Kc hKc hK hKt' hlie
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF : Nat.card F = 4 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι (f := 1) (by rw [hK2]; rfl) hσ hfix]
    norm_num
  have : CharP ι.fieldRange 2 := RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  obtain ⟨τm, hX, hW, ⟨ρ, hval⟩, hgen⟩ :=
    h K b c hirr hK2 F hF σ hσ ι.fieldRange hσk ι.rangeRestrictFieldEquiv
  obtain ⟨hDE, πn, hπn⟩ := exists_normalized_plusAnisoTorus_of_lieModel (m := 3) hset le_rfl hK2
    hirr e ht hKt rfl htX hKc hK hKt' hlie hF hσ hσk ι.rangeRestrictFieldEquiv
  exact ⟨F, inferInstance, inferInstance, inferInstance, hF,
    q2FrameDataGen_of_plusModel le_rfl hirr _ ι.rangeRestrictFieldEquiv τm hX hW ρ hval hgen hDE
      πn hπn⟩

end PlusTen

end CFSG.SeitzReduction.OmegaPilot
