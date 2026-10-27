module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneReductions
public import CFSG.HardMathSupport.Lang.TwE6Step3.CubesV4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevInnerMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevTwoOuterGen
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.E8Phi5
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.F4Phi3
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd.Final
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LieType.SeitzGeneration (HyperGen)


section LieCrossCert


variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Seitz.TrialityOdd in
private theorem exists_hyperGen_of_cross (d : TauCeti.ValidLieTypeIndex) (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hpd : p ≠ d.1.characteristic) (hl : ¬ P1ThreeLieList p d)
    {E₀ : Subgroup (TauCeti.CFSGIndex.lie d).Group} (hE₀ : IsElemAbelian p E₀)
    (hc : Nat.card E₀ = p ^ 3) :
    ∃ E₁ : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian p E₁ ∧ Nat.card E₁ = p ^ 3 ∧
      HyperGen p ⊤ E₁ := by
  by_cases hcl : IsClassicalIndex d.1
  · exact hyperExFor_isClassical d p hp hp2 hpd hl ⟨E₀, hE₀, hc, hcl⟩
  have hW : ∀ r : ℕ, 5 ≤ r → Coordinator.Phi6CoreW r := fun r hr =>
    Inner.phi6CoreW_of_placementSome hr (Inner.phi6PlacementSome_holds r hr)
      (Inner.phi6PlacementSomeThree_holds r hr)
  have hX := CFSG.HardMathSupport.Lang.TwE6Step3.excCubeResidualsV4_of_phi6 fun r hr =>
    Coordinator.phiPlaneGenAt_neg_of_coreW hr (hW r hr)
  exact hyperExFor_exc_of_residuals hX.toV3.toV2.toResiduals d p hp hp2 hpd hl ⟨E₀, hE₀, hc, hcl⟩

open CFSG.HardMathSupport.Foote.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube in
private theorem kFactSeitzOuterCubeRankTwo' : KFactSeitzOuterCubeRankTwo :=
  Exc.kFactSeitzOuterCubeRankTwo_of_open
    ⟨SplitFrame.seitzExcAnisotropicF4Class_three, TwistedFrame.seitzExcAnisotropicF4Class_six⟩
    ⟨TwistedFrame.seitzExcAnisotropicE6Class_six, SplitFrame.seitzExcAnisotropicE8Class_five,
      TwistedFrame.seitzExcAnisotropicE8Class_ten, TwistedFrame.seitzExcAnisotropicE8Class_twelve⟩
    Exc.TOdd.trialityOuterCubesThreeOdd_holds

private theorem le_weakCore_of_hyperGen_equiv (hp : p.Prime) [K.Normal] {L : Type*} [Group L]
    (e : K ≃* L)
    {E₁ : Subgroup L} (hE₁ : IsElemAbelian p E₁) (hc : Nat.card E₁ = p ^ 3)
    (hgen : HyperGen p ⊤ E₁) : K ≤ GLBWeakCore p (P : Subgroup G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set E₂ : Subgroup G := (E₁.map e.symm.toMonoidHom).map K.subtype
  have hE₂ : IsElemAbelian p E₂ := (hE₁.map _).map _
  have hE₂c : Nat.card E₂ = p ^ 3 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hc]
  have hgen₂ : HyperGen p K E₂ :=
    hyperGen_map_subtype (CFSG.LieType.SeitzGeneration.hyperGen_map_symm e hgen)
  obtain ⟨g, hg⟩ := exists_conj_le_sylow P hE₂.2
  refine le_weakCore_of_hyperGen hp hg (hE₂.map _) ?_
    (CFSG.LieType.SeitzGeneration.hyperGen_conj g hgen₂)
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₂c]

theorem Hyp.p1ThreeLieList_of_lieCross (H : Hyp p K P E)
    (h3 : 3 ≤ Open.pRank p (P : Subgroup G)) (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G))
    (hC : Subgroup.centralizer (K : Set G) = ⊥) (d : TauCeti.ValidLieTypeIndex)
    (hpd : p ≠ d.1.characteristic) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    P1ThreeLieList p d := by
  by_contra hl
  apply hnot
  haveI := H.normal
  haveI : Fact p.Prime := ⟨H.prime⟩
  by_cases hex : ∃ E₃ : Subgroup G, E₃ ≤ K ∧ IsElemAbelian p E₃ ∧ Nat.card E₃ = p ^ 3
  · obtain ⟨E₃, hE₃K, hE₃, hE₃c⟩ := hex
    obtain ⟨E₁, hE₁, hE₁c, hgen⟩ := exists_hyperGen_of_cross d H.prime H.ne_two hpd hl
      (E₀ := (E₃.subgroupOf K).map e.toMonoidHom) ((hE₃.subgroupOf K).map _)
      (by
        rw [Subgroup.card_map_of_injective e.injective]
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₃K).toEquiv).trans hE₃c)
    exact le_weakCore_of_hyperGen_equiv H.prime e hE₁ hE₁c hgen
  · obtain ⟨E₃, hE₃P, hE₃, hE₃c⟩ :=
      CFSG.AGLEmbeddingD2.exists_isElemAbelian_card_pow_of_le_pRank H.prime h3
    exact le_weakCore_of_hyperGen H.prime hE₃P hE₃ hE₃c
      (kFactSeitzOuterCubeRankTwo' p H.ne_two G K H.normal hC d ⟨e⟩ hpd hl hex E₃ hE₃ hE₃c)

theorem Hyp.threeOne_lieCross (H : Hyp p K P E) (h3 : 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) (hC : Subgroup.centralizer (K : Set G) = ⊥)
    (d : TauCeti.ValidLieTypeIndex) (hpd : p ≠ d.1.characteristic)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : OnThreeOneList p K := by
  have hl := H.p1ThreeLieList_of_lieCross h3 hnot hC d hpd e
  have hZ := H.center_eq_bot_of_centralizer_eq_bot hC
  have eZ : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e
  have hon : IsNineThreeLieIndex p d → OnThreeOneList p K := fun h => ⟨.lie d, Or.inl h, ⟨e⟩⟩
  have hinner : p = 3 → IsChevTwoInnerIndex d → OnThreeOneList p K := by
    rintro rfl hd
    refine absurd (H.le_weakCore_of_sylow ?_) hnot
    refine kFactChevTwoInnerGen_of_certificates d hd K H.quasi ⟨eZ⟩ H.isPGroup_center ?_
    rw [hZ]
    infer_instance
  have houter : p = 3 → IsChevTwoOuterIndex d → OnThreeOneList p K := by
    rintro rfl hd
    refine absurd (kFactChevTwoOuterGen_of_certificates.2 d hd G K H.normal H.quasi ⟨eZ⟩
      (by rw [hC]; exact IsPGroup.of_bot) (fun c hc hco => ?_) P h3) hnot
    rw [hC, Subgroup.mem_bot] at hc
    subst hc
    simp at hco
  rcases hl with ⟨n, q, hd, hq, -⟩ | ⟨q, hq, hd⟩ | ⟨hp, m, hd⟩ | hsp | hd
  · simp [hd, hq] at hpd
  · simp [hd, hq] at hpd
  · simp [hd, hp] at hpd
  · obtain ⟨q, ⟨hq, -, hd⟩ | -⟩ := id hsp
    · simp [hd, hq] at hpd
    · exact hon (Or.inr (Or.inr (Or.inl hsp)))
  rcases hd with ⟨hp, q, hq, hq1, h | h | h | h | h | h | h | h⟩ |
    ⟨hp, q, hq, hq3, h | h | h | h⟩ | ⟨hp, h⟩
  · exact hon (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp, Or.inr (Or.inr (Or.inl ⟨q, hq, hq1, h⟩))⟩))))))
  · exact hinner hp ⟨q, hq, hq1, Or.inl h⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inl h)⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inl h))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
  · exact houter hp (Or.inl ⟨q, hq, hq1, h⟩)
  · exact hon (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp, Or.inl ⟨q, hq, hq3, Or.inr (Or.inr h)⟩⟩))))))
  · exact hon (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hp, Or.inl ⟨q, hq, hq3, Or.inr (Or.inl h)⟩⟩))))))
  · exact houter hp (Or.inr ⟨q, hq, hq3, Or.inl h⟩)
  · exact houter hp (Or.inr ⟨q, hq, hq3, Or.inr h⟩)
  · exact hon (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, Or.inr (Or.inr h)⟩))))))

end LieCrossCert

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
