module

public import CFSG.ClassicalInvolution.Q3.TL4StepDefs
public import CFSG.ClassicalInvolution.Q3.TL4SepRestr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwin

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3


theorem tightTwistStep_at {n : ℕ} (h : TightTwistAllTwin n) : TightTwistStep n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 htw
  by_cases hall : ∀ c ∈ Subgroup.center Y, orderOf c = 2 → ∃ y : Y, y * t * y⁻¹ = t * c
  · by_cases hE4 : TightE4 Y
    · exact Or.inl (Or.inr (Or.inr (Or.inr hE4)))
    refine Or.inr (h hA hb Y hn R S t hd hc hE2 htw hall ?_ hE4)
    obtain ⟨c, hcZ, hc2⟩ := htw.exists_central_involution hc.2.2
    obtain ⟨y, hy⟩ := hall c hcZ hc2
    have hc1 : c ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hc2
      exact absurd hc2 (by norm_num)
    exact hd.not_edgeless_of_twin hcZ hc1 hy
  push Not at hall
  obtain ⟨c, hcZ, hc2, hnt⟩ := hall
  exact tightExOrGood_of_central hb hn hd hc hE2 hcZ hc2 hnt

theorem tightCentTwinLift_at {n : ℕ} (h : PhilipHall.Frame.Thm1RTwinLiftSetEBelow n) :
    TightCentTwinLift n := by
  intro _ _ Y _ _ hn R S t hd hc hE2 hQ _ c hcZ hc1 hy hE4
  obtain ⟨y, hy⟩ := hy
  have B := PhilipHall.QuaternionBridge.q8Bridge_of_centTwin hd hc hE2 hQ hcZ hc1 hy
  have := B.simple
  have hlt : Nat.card (Y ⧸ TA3.fstarCenter Y) < n := hn ▸ B.quot.card_lt
  have hcN : c ∈ TA3.fstarCenter Y := by
    have hcC : c ∈ Subgroup.centralizer (genFittingFStar Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun g _ => Subgroup.mem_center_iff.mp hcZ g
    have hcF : c ∈ genFittingFStar Y := CFSG.Adapters.generalized_fitting_self_centralizing Y hcC
    refine ⟨⟨c, hcF⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcZ g)
  have hNbot : TA3.fstarCenter Y ≠ ⊥ := fun hb' => hc1 (by simpa [hb'] using hcN)
  have ht1 : QuotientGroup.mk' (TA3.fstarCenter Y) t ≠ 1 := by
    intro h1
    have := B.quot.datum.order
    rw [h1, orderOf_one] at this
    omega
  rcases h _ hlt _ _ _ B.quot.datum B.quot.cls.1 B.quot.cls.2.1
      (PhilipHall.Frame.oddCore_eq_bot_of_fstar B.nonab) B.quot.hyp B.aEmpty B.quot.twin with
    h1 | h2 | h3
  · exact absurd h1 (PhilipHall.Frame.not_tightInO2_of_fstar B.nonab ht1)
  · exact absurd (PhilipHall.QuaternionBridge.tightE4_of_exLie_quotient B.two hNbot
      (h2.exLie B.nonab)) hE4
  · exact PhilipHall.QuaternionBridge.good_of_hasLift_twin hd B.central B.two B.not_mem
      (h3.hasLift B.quot.twin)

theorem tightStep_at {n : ℕ} (htw : TightTwistAllTwin n) (h1 : TightSmallBase)
    (h2 : TightLargeEdgeS n) (h3 : TightLargeLiftS n) (h4 : TightCentTwinLift n) :
    TightStep n := by
  intro hA hb Y _ _ hn R S t hd hc
  by_cases hE2 : TightInO2 t
  · exact Or.inl (Or.inl hE2)
  rcases (tightDichotomy_holds n Y hn R S t hd hc).resolve_left hE2 with hQ | htw'
  swap
  · exact tightTwistStep_at htw hA hb Y hn R S t hd hc hE2 htw'
  by_cases hsmall : TwoSubgroupsFourGenerated (genFittingFStar Y)
  · exact h1 Y (by rw [hn]; exact hA) R S t hd hc hE2 hQ hsmall
  by_cases hZ : Subgroup.center Y = ⊥
  · have hZF : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
      have h := hd.center_genFittingFStar_le hc hE2
      rw [hZ, le_bot_iff,
        Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h
      exact h
    obtain ⟨hs, hnab⟩ := isSimpleGroup_of_quasisimple_of_center_eq_bot hQ hZF
    exact Or.inr (h3 hA hb Y hn R S t hd hc hE2 hQ hsmall
      (h2 hA hb Y hn hnab R S t hd hc hE2 hsmall) hZ)
  · obtain ⟨c, hcZ, hc2⟩ := exists_central_involution_of_center_ne_bot hc.2.2 hZ
    by_cases htwin : ∃ y : Y, y * t * y⁻¹ = t * c
    · have hc1 : c ≠ 1 := by
        intro h
        rw [h, orderOf_one] at hc2
        exact absurd hc2 (by norm_num)
      by_cases hE4 : TightE4 Y
      · exact Or.inl (Or.inr (Or.inr (Or.inr hE4)))
      · exact Or.inr (h4 hA hb Y hn R S t hd hc hE2 hQ hsmall c hcZ hc1 htwin hE4)
    · push Not at htwin
      exact tightExOrGood_of_central hb hn hd hc hE2 hcZ hc2 htwin

theorem tightEdgePairGoodS_at {n : ℕ} (hodd : TightOddLeaf n) (hconn : TightConnLeaf n)
    (hsep : TightSepLeaf n) (hthin : TightThinLeaf n) (hE3 : TightE3Leaf n) :
    TightEdgePairGoodS n := by
  intro hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge hZ
  have hL : TightLargeHyp n Y R S t := ⟨hA, hB, hn, hd, hc, hE2, hQ, hlarge, hedge, hZ⟩
  have hO : TightOddCent t := hodd Y R S t hL
  have hΩ := hd.hypOmegaGen
  have h2 := hd.isPGroup_member hO
  have hcn := hconn Y R S t hL hO
  have hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R)) := @hsep Y _ _ R S t hL hO
  have huniq := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g (tightCore R) = J :=
    fun J hJ => hJ
  have hgen : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hc.2.1
  have hF := TC.graphFam hΩ h2 hsp htr hgen hcn
  obtain ⟨J₀, hJ₀⟩ := hd.nonempty_omegaNbr_of_not_dEdgeless hedge
  obtain ⟨P, hP⟩ := exists_isMaxOrb (A := TC.nbrAdj (CoreAssembly.conjClass (tightCore R)))
    (⟨hK, hJ₀⟩ : TC.nbrAdj _ (tightCore R) J₀)
  obtain ⟨⟨J, hKJ, hJP⟩, -⟩ := id hP
  have hmax : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J :=
    ⟨hKJ, by rw [hJP]; exact hP⟩
  obtain ⟨g, hgJ'⟩ := hKJ.2.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hu : IsUniqueInvolution J (g * t * g⁻¹) := hgJ ▸ huniq.conj g
  obtain ⟨-, -, hut, htu, -⟩ := hd.edge_involution hKJ.2 hu
  refine ⟨g, hgJ ▸ hKJ.2, htu, hut, hL.good_section hodd hconn hsep hthin hE3 hmax hu htu, ?_⟩
  obtain ⟨SJ, hLJ⟩ := hL.conj g
  have hJcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hmax' : MaxAdj (TC.nbrAdj (CoreAssembly.conjClass (tightCore (conjSub g R))))
      (tightCore (conjSub g R)) (tightCore R) := by
    rw [hfam, hJcore]
    exact ⟨hF.graph.symm hmax.1, orbOf_mem_maxOrbs hF hmax.1 hmax.2⟩
  exact hLJ.good_section hodd hconn hsep hthin hE3 hmax' huniq hut

theorem sepLeafStep_of_thm4 {n : ℕ} (h4 : PlusLeaf Thm4RBelow n) : CIT3Below n → TightBelowRPlus 3 n → TightSepLeaf n :=
  
  fun hA hP => tightSepLeaf_of_R (tightSepLeafR_of_thm4R (h4 hA hP))

theorem indepLeafStep_holds (n : ℕ) : CIT3Below n → TightBelowRPlus 3 n → TightIndepLeaf n :=
  fun _ hP => tightIndepLeaf_of_thmD3Below
    (TC.Thin.tightThmD3Below_of_genBelow (thmDGenBelow_of_gen hP.thmD))

section Lift


theorem tightLargeLiftS_at {n : ℕ} (hodd : TightOddLeaf n) (hconn : TightConnLeaf n)
    (hsep : TightSepLeaf n) (hind : TightIndepLeaf n) (hE3 : TightE3Leaf n) :
    TightLargeLiftS n := by
  intro hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge hZ
  obtain ⟨g, hJ, htu, hut, hg1, hg2⟩ := tightEdgePairGoodS_at hodd hconn hsep
    (tightThinLeaf_of_indep hind) hE3 hA hB Y hn R S t hd hc hE2 hQ hlarge hedge hZ
  exact hd.good_of_edgePair hA hn hE2 hJ htu hut hg1 hg2

theorem tightLargeLiftS_of_steps {n : ℕ} (hodd : OddLeafStep n) (hconn : ConnLeafStep n)
    (hE3 : E3LeafStep n) (h4 : PlusLeaf Thm4RBelow n) (hA : CIT3Below n)
    (hP : TightBelowRPlus 3 n) : TightLargeLiftS n :=
  tightLargeLiftS_at (hodd hA hP) (hconn hA hP) (sepLeafStep_of_thm4 h4 hA hP)
    (indepLeafStep_holds n hA hP) (hE3 hA hP)

theorem tightStep_of_plus {n : ℕ} (htw : TightTwistAllTwin n) (hsmall : TightSmallBase)
    (hE : TightLargeEdgeS n) (hodd : OddLeafStep n) (hconn : ConnLeafStep n)
    (hE3 : E3LeafStep n) (h4 : PlusLeaf Thm4RBelow n) (hA : CIT3Below n)
    (hP : TightBelowRPlus 3 n) : TightStep n :=
  tightStep_at htw hsmall hE (tightLargeLiftS_of_steps hodd hconn hE3 h4 hA hP)
    (tightCentTwinLift_at (hP.twin rfl))

theorem tightPlusStep_of_parts {n : ℕ} (htw : TightTwistAllTwin n) (hsmall : TightSmallBase)
    (hE : TightLargeEdgeS n) (hodd : OddLeafStep n) (hconn : ConnLeafStep n)
    (hE3 : E3LeafStep n) (h4 : PlusLeaf Thm4RBelow n) (hD2 : ThmD2StepR 3 n)
    (hD1 : ThmD1StepR 3 n) (h6 : Thm6StepR 3 n) (h5 : Thm5StepR 3 n)
    (htwin : TwinStepR 3 n) : TightPlusStep 3 n := by
  intro hA hP
  exact
    { tbelow := tightBelowR_succ_of_tightStep
        (tightStep_of_plus htw hsmall hE hodd hconn hE3 h4 hA hP) hA hP
      thmD := thmD_step hD2 hD1 hA hP
      thm6 := h6 hA hP
      thm5 := h5 hA hP
      twin := htwin hA hP }

end Lift

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
