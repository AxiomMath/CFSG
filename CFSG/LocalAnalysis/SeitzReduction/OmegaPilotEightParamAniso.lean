module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightParamMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitSmall

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG SUmCatalogueClausesAt)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

section Swap

variable {G : Type*} [Group G]

theorem swapParam_inl_mem_centralizerPerfectCore {t : G} {D Y T : Subgroup G} (P : SwapParam t D)
    (hYD : Y ≤ D) (hTD : T ≤ D) (hYT : Y ≤ centralizer (T : Set G)) (hYp : ⁅Y, Y⁆ = Y)
    (y : G) (hy : y ∈ Y) :
    P.Ψ (⟨y, hYD hy⟩, 1) ∈ centralizerPerfectCore T := by
  set j : Y →* G := P.Ψ.comp ((MonoidHom.inl D D).comp (Subgroup.inclusion hYD)) with hj
  have hjp : ⁅j.range, j.range⁆ = j.range := by
    have : Group.IsPerfect Y := Subgroup.isPerfect_iff.mpr hYp
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      Group.IsPerfect.commutator_eq_top]
  have hjc : j.range ≤ centralizer (T : Set G) := by
    rintro _ ⟨w, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    have hdd : P.Ψ (⟨d, hTD hd⟩, ⟨d, hTD hd⟩) = d := P.diag _
    have hwd : (w : G) * d = d * w := (mem_centralizer_iff.1 (hYT w.2) d hd).symm
    change d * P.Ψ (⟨w, hYD w.2⟩, 1) = P.Ψ (⟨w, hYD w.2⟩, 1) * d
    conv_lhs => rw [← hdd]
    conv_rhs => rw [← hdd]
    rw [← map_mul, ← map_mul]
    congr 1
    ext
    · change d * (w : G) = (w : G) * d
      exact hwd.symm
    · simp
  exact F4Pilot.le_centralizerPerfectCore hjp hjc ⟨⟨y, hy⟩, rfl⟩

theorem false_of_swapParam_of_isSimpleGroup {t : G} {D U Y : Subgroup G} (P : SwapParam t D)
    (hinj : Function.Injective P.Ψ) (hU : U ≤ P.Ψ.range) [IsSimpleGroup U]
    (htU : t ∈ normalizer (U : Set G)) (hYD : Y ≤ D)
    (hYU : ∀ y (hy : y ∈ Y), P.Ψ (⟨y, hYD hy⟩, 1) ∈ U) (hY : Y ≠ ⊥) : False := by
  set j₁ : D →* G := P.Ψ.comp (MonoidHom.inl D D) with hj₁
  set j₂ : D →* G := P.Ψ.comp (MonoidHom.inr D D) with hj₂
  have hconj : ∀ x : D, t * j₁ x * t⁻¹ = j₂ x := fun x => P.swap x 1
  have hdisj : ∀ x y : D, j₁ x = j₂ y → x = 1 := by
    intro x y h
    have h2 := hinj h
    exact congrArg Prod.fst h2
  have hnormal : ∀ u ∈ U, ∀ a ∈ j₁.range, u * a * u⁻¹ ∈ j₁.range := by
    rintro u hu _ ⟨x, rfl⟩
    obtain ⟨⟨p, q⟩, hpq⟩ := hU hu
    refine ⟨p * x * p⁻¹, ?_⟩
    rw [← hpq, hj₁, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    ext
    · simp
    · simp
  set N : Subgroup U := (j₁.range).subgroupOf U with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hnormal g g.2 n hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · apply hY
    rw [eq_bot_iff]
    intro y hy
    have hmem : (⟨P.Ψ (⟨y, hYD hy⟩, 1), hYU y hy⟩ : U) ∈ N := by
      rw [hN, mem_subgroupOf]
      exact ⟨⟨y, hYD hy⟩, rfl⟩
    rw [hbot, mem_bot] at hmem
    have h1 : P.Ψ (⟨y, hYD hy⟩, 1) = P.Ψ 1 := by
      rw [map_one]
      exact congrArg Subtype.val hmem
    have h2 := congrArg Prod.fst (hinj h1)
    exact (mem_bot).2 (congrArg Subtype.val h2)
  · have hUA : ∀ u ∈ U, u ∈ j₁.range := fun u hu => by
      have h : (⟨u, hu⟩ : U) ∈ N := htop ▸ mem_top _
      rw [hN, mem_subgroupOf] at h
      exact h
    obtain ⟨u, hu1⟩ := exists_ne (1 : U)
    have hv : t⁻¹ * (u : G) * t⁻¹⁻¹ ∈ U := (mem_normalizer_iff.1 (inv_mem htU) _).1 u.2
    rw [inv_inv] at hv
    obtain ⟨x, hx⟩ := hUA _ hv
    obtain ⟨y, hy⟩ := hUA _ u.2
    have hyx : j₁ y = j₂ x := by
      rw [hy, ← hconj, hx]
      group
    have hy1 := hdisj y x hyx
    apply hu1
    apply Subtype.ext
    rw [← hy, hy1, map_one]
    rfl

end Swap

section Pieces

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem frameLeviProj_le_anisoPerp (hn : 1 ≤ n) (b c : K) {p q : Fin (n - 1)} (hpq : p ≠ q) :
    frameLeviProj (coordinateQuadMinus n K hn b c) (minusFrameLeft hn) (minusFrameRight hn) p q ≤
      anisoPerp hn b c := by
  have h := isHypFrame_minus K hn b c
  have hroot : ∀ p' q' : Fin (n - 1), p' ≠ q' → ∀ x : K,
      frameRootElt (coordinateQuadMinus n K hn b c) (minusFrameLeft hn) (minusFrameRight hn) p'
        q' x ∈ stabSub (anisoCoordLeft hn) (anisoCoordRight hn) := by
    intro p' q' hpq' x
    refine ⟨?_, ?_⟩
    · rw [h.frameRootElt_apply hpq']
      have h1 : (Pi.single (anisoCoordLeft hn) (1 : K) : Fin (2 * n) → K)
          (minusFrameRight hn p') = 0 :=
        Pi.single_eq_of_ne (anisoCoordLeft_ne_minusFrameRight hn p').symm _
      have h2 : (Pi.single (anisoCoordLeft hn) (1 : K) : Fin (2 * n) → K)
          (minusFrameLeft hn q') = 0 :=
        Pi.single_eq_of_ne (anisoCoordLeft_ne_minusFrameLeft hn q').symm _
      simp [h1, h2]
    · rw [h.frameRootElt_apply hpq']
      have h1 : (Pi.single (anisoCoordRight hn) (1 : K) : Fin (2 * n) → K)
          (minusFrameRight hn p') = 0 :=
        Pi.single_eq_of_ne (anisoCoordRight_ne_minusFrameRight hn p').symm _
      have h2 : (Pi.single (anisoCoordRight hn) (1 : K) : Fin (2 * n) → K)
          (minusFrameLeft hn q') = 0 :=
        Pi.single_eq_of_ne (anisoCoordRight_ne_minusFrameLeft hn q').symm _
      simp [h1, h2]
  have hS : frameLeviSL (coordinateQuadMinus n K hn b c) (minusFrameLeft hn) (minusFrameRight hn)
      p q ≤ stabSub (anisoCoordLeft hn) (anisoCoordRight hn) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨μ, rfl⟩)
    · exact hroot q p (Ne.symm hpq) x
    · exact hroot p q hpq x
    · rw [frameLeviTorus_apply]
      exact minusFrameLin_mem_stabSub_aniso hn _
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, mem_subgroupOf.2 (hS (mem_subgroupOf.1 hy)), rfl⟩

theorem oddSchurTrivial_map_anisoPerp_four
    {G : Type} [Group G]
    {L : Subgroup G} {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) :
    OddSchurTrivial (((anisoPerp (K := K) (n := 4) (by omega) b c).map e.symm.toMonoidHom).map
      L.subtype) :=
  (SeitzQ2.oddSchurTrivial_specialLinearGroup 3 K).of_mulEquiv
    (((pslFourEquivSL K).symm.trans ((plusKleinEquiv K).trans
      (anisoPerpModelEquiv (n := 4) le_rfl hirr).symm)).trans
      (LinearPilot.mapSymmMulEquiv e _).symm)

theorem minusRootElt_one_ne_one (hn : 4 ≤ n) {β γ : K} (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    {i j : Fin (n - 1)} (hij : i ≠ j) : minusRootElt hn hirr i j 1 ≠ 1 := by
  intro h
  apply minusRootElt_mul_ne hn hirr hij
  rw [h, one_mul, mul_one]

theorem isSimpleGroup_of_minusRootFieldParam {G : Type} [Group G] {L : Subgroup G}
    (hn : 4 ≤ n) {β γ : K} {hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0}
    {e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ)} {t : G}
    {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K →+* F} {σ : F ≃+* F} {i j : Fin (n - 1)}
    (hij : i ≠ j) (hF : 4 ≤ Nat.card F) (P : MinusRootFieldParam hn hirr e t ι σ i j) :
    IsSimpleGroup (minusLevelCore e ({i, j} : Finset (Fin (n - 1)))) := by
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := F) hF
  have hinj : Function.Injective P.φ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P.φ.ker with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff _).1 hbot
    · exfalso
      have h1 : LinearPilot.upperUnit (1 : F) ∈ P.φ.ker := htop ▸ mem_top _
      rw [MonoidHom.mem_ker, P.upper] at h1
      have h2 : e.symm (minusRootElt hn hirr i j 1) = 1 := Subtype.ext h1
      exact minusRootElt_one_ne_one hn hirr hij ((MulEquiv.map_eq_one_iff e.symm).1 h2)
  exact ((MulEquiv.subgroupCongr P.range_eq).symm.trans
    (MonoidHom.ofInjective hinj).symm).isSimpleGroup

end Pieces

section Main


theorem omegaMinusFourAnisoRowInput_of_catalogue (hcatU : SUmCatalogueClausesAt 4)
    (hcatL : LinearPilot.SLmCatalogueClausesAt 4) : OmegaMinusFourAnisoRowInput := by
  intro G _ _ L hset f K _ _ _ b c hirr hKc hf2 e t ht hKt hrow
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf2
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set X := modelToG e (anisoTorus (K := K) (n := 4) (by norm_num) b c) with hXdef
  set D := modelToG e (anisoPerp (K := K) (n := 4) (by norm_num) b c) with hDdef
  obtain ⟨-, htX, -, -, -, hDC, -, hZD⟩ :=
    neighbour_data_anisoTorus (n := 4) le_rfl hirr e htC (X := X) rfl (D := D) rfl
  obtain ⟨Kc, hKcomp, hDKK, hcase⟩ := neighbour_overgroup_anisoTorus_four hset hcatL hKc hq hirr
    e htC ht (X := X) rfl htX (D := D) rfl
  rcases hcase with ⟨hKt', -⟩ | ⟨hKt', hcomm, hZK, hφ⟩
  · exact ⟨htX, Kc, hKcomp, hDKK, iff_of_true rfl hKt'⟩
  · exfalso
    obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_anisoTorus_of_seitzSetting hset hKc (n := 4)
      (by norm_num) hirr e htC ht (X := X) rfl (D := D) rfl
    obtain ⟨-, hsyl, -⟩ := neighbour_standard_anisoTorus_of_seitzSetting hset hKc le_rfl hirr e
      htC ht (X := X) rfl htX (D := D) rfl
    have hOutD : Group.IsSolvable (Outer D) :=
      isSolvable_outer_map_anisoPerp_of_four_le hKc hq le_rfl hirr e rfl
    obtain ⟨Ψ, hinj, hrange⟩ := exists_swapParam_of_swapCase htC ht hLt htX hD hDq hXo
      (hDC.trans inf_le_left) (map_subtype_le _) hZD hOutD
      (oddSchurTrivial_map_anisoPerp_four hirr e)
      hsyl (m := 3) (f := f) ⟨Kc, hKcomp, ⟨hDKK, .inr ⟨hKt', hcomm, hZK, hφ⟩⟩, hKt'⟩
    obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
    have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
    have hF : Nat.card F = 2 ^ (2 * f) :=
      SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
    have hF4 : 4 ≤ Nat.card F := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hσ
      omega
    have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
    obtain ⟨P⟩ := omegaMinusFourRootParamInput_of_catalogue hcatU G L hset f K b c hirr hKc hf2 e
      t ht hKt hrow F ι σ hσ hfix
    have h01 : (⟨0, by omega⟩ : Fin (2 + 2 - 1)) ≠ ⟨1, by omega⟩ := by simp
    have hUs := isSimpleGroup_of_minusRootFieldParam (n := 2 + 2) le_rfl h01 hF4 P
    have hUE := minusLevelCore_le_anisoNeighbourCore_of_param (n := 2 + 2) hset le_rfl hKc hq hirr
      e ht hKt h01 hσ1 hσσ hfix P
    have htU : t ∈ normalizer (minusLevelCore e
        ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1))) : Set G) :=
      UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _
    have hqK := hq
    obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus (2 + 2) K b c le_rfl hirr
    have hh := isHypFrame_minus K (n := 2 + 2) (by omega) b c
    set Y := modelToG e (frameLeviProj (coordinateQuadMinus (2 + 2) K (by omega) b c)
      (minusFrameLeft (by omega)) (minusFrameRight (by omega)) ⟨0, by omega⟩ ⟨1, by omega⟩)
      with hYdef
    have hYD : Y ≤ D := UnitaryPilot.modelToG_mono e (frameLeviProj_le_anisoPerp _ b c h01)
    have hTD : modelToG e (minusLevelTorus (K := K) (n := 2 + 2) (by omega) b c
        ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1)))) ≤ D :=
      UnitaryPilot.modelToG_mono e (minusFrameTorus_le_anisoPerp _ b c _)
    have hYT : Y ≤ centralizer (modelToG e (minusLevelTorus (K := K) (n := 2 + 2) (by omega) b c
        ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin (2 + 2 - 1)))) : Set G) :=
      UnitaryPilot.modelToG_le_centralizer e (hh.frameLeviProj_le_centralizer (by simp) (by simp))
    have hYp : ⁅Y, Y⁆ = Y :=
      UnitaryPilot.modelToG_perfect e (hh.commutator_frameLeviProj h01 hq hQ hT)
    have hY1 : Y ≠ ⊥ := by
      intro hY
      have hmem := symm_mem_modelToG e (minusRootElt_mem_frameLeviProj (n := 2 + 2) le_rfl hirr
        ⟨0, by omega⟩ ⟨1, by omega⟩ 1)
      rw [← hYdef, hY, mem_bot] at hmem
      have h2 : e.symm (minusRootElt (n := 2 + 2) le_rfl hirr ⟨0, by omega⟩ ⟨1, by omega⟩ 1) = 1 :=
        Subtype.ext hmem
      exact minusRootElt_one_ne_one (n := 2 + 2) le_rfl hirr h01
        ((MulEquiv.map_eq_one_iff e.symm).1 h2)
    exact false_of_swapParam_of_isSimpleGroup Ψ hinj (hrange ▸ hUE) htU hYD
      (swapParam_inl_mem_centralizerPerfectCore Ψ hYD hTD hYT hYp) hY1

theorem omegaMinusFourInput_of_catalogue_five (hswap : OmegaMinusFourSwapRowInput)
    (huniq : OmegaMinusFourUniqueInput) (hend : OmegaMinusFourEndInput)
    (hcatU : SUmCatalogueClausesAt 4) (hcatL : LinearPilot.SLmCatalogueClausesAt 4) :
    OmegaMinusFourInput :=
  omegaMinusFourInput_of_catalogue_six hswap huniq hend hcatU hcatL
    (omegaMinusFourAnisoRowInput_of_catalogue hcatU hcatL)

end Main

end CFSG.SeitzReduction.OmegaPilot
