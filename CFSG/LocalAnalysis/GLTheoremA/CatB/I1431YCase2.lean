module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Reduce
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I1431YD4Two : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (σ : MulAut Q) (A I T : Subgroup Q),
    CFSG.Open.IsQuasisimple Q → IsPGroup 3 (Subgroup.center Q) →
    catalogIs (Q ⧸ Subgroup.center Q) (S8.isD4of 2) →
    σ ^ 3 = 1 → A ≤ I2016.fixSub σ → I2016.HasA6Quot A →
    CFSG.Open.IsSubnormal I (I2016.fixSub σ) → S8.IsTypeWithCenter 3 I S8.isPSp43 1 →
    T ≠ ⊥ → IsPGroup 2 T → T.map σ.toMonoidHom = T →
    A ≤ Subgroup.normalizer (T : Set Q) → False

@[expose] def I1431YU5Two : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (σ : MulAut Q) (A I T : Subgroup Q),
    CFSG.Open.IsQuasisimple Q → IsPGroup 3 (Subgroup.center Q) →
    catalogIs (Q ⧸ Subgroup.center Q) S8.L89.isU5of2 →
    σ ^ 3 = 1 → A ≤ I2016.fixSub σ → I2016.HasA6Quot A →
    CFSG.Open.IsSubnormal I (I2016.fixSub σ) → S8.IsTypeWithCenter 3 I S8.isPSp43 1 →
    T ≠ ⊥ → IsPGroup 2 T → T.map σ.toMonoidHom = T →
    A ≤ Subgroup.normalizer (T : Set Q) → False

@[expose] def I1431YU4Eight : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (σ : MulAut Q) (A I T : Subgroup Q),
    CFSG.Open.IsQuasisimple Q → IsPGroup 3 (Subgroup.center Q) →
    catalogIs (Q ⧸ Subgroup.center Q) (S8.isU4of 8) →
    σ ^ 3 = 1 → A ≤ I2016.fixSub σ → I2016.HasA6Quot A →
    CFSG.Open.IsSubnormal I (I2016.fixSub σ) → S8.IsTypeWithCenter 3 I S8.isPSp43 1 →
    T ≠ ⊥ → IsPGroup 2 T → T.map σ.toMonoidHom = T →
    A ≤ Subgroup.normalizer (T : Set Q) → False

theorem isU4two_of_isPSp43 {i : TauCeti.CFSGIndex} (h : S8.isPSp43 i) :
    CFSG.LocalAnalysis.GLTheoremA.S9.isU4two i := by
  rcases h with h | h
  · exact h
  · exfalso
    cases i with
    | cyclic p hp => simp [onLie] at h
    | alternating n hn => simp [onLie] at h
    | sporadic s => simp [onLie] at h
    | lie idx =>
      obtain ⟨d, hd⟩ := idx
      cases d
      all_goals try (simp [onLie] at h; done)
      rename_i r q
      by_cases hr : r = 2
      · subst hr
        have hd' := (TauCeti.LieTypeIndex.valid_iff _).1 hd
        rw [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hd'
        exact hd'.2 (show 2 = 2 ∧ q.card = 3 from ⟨rfl, h⟩)
      · simp [onLie, hr] at h

theorem i1431List_bridge {j : TauCeti.CFSGIndex}
    (h : CFSG.LocalAnalysis.GLTheoremA.S9.i1431List j) : S8.L89.i1431List j := by
  unfold CFSG.LocalAnalysis.GLTheoremA.S9.i1431List at h
  unfold S8.L89.i1431List
  rcases h with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem conj1_of_clat {G : Type} [Group G] [Finite G]
    (hC : CFSG.LocalAnalysis.GLTheoremA.I1431ClAt G)
    (a y : G) (J I : Subgroup G) (hctx : S8.L89.Case2Ctx a y J I) :
    catalogIs (PSimple 3 J) S8.L89.i1431List := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hctx.hIt.1
  obtain ⟨j, hj, ⟨f⟩⟩ := hC a y J I hctx.ha hctx.hK hctx.hya hctx.hy hctx.hyn hctx.hJ hctx.hyJ
    hctx.hI ⟨i, isU4two_of_isPSp43 hi, ⟨e⟩⟩ hctx.hJI hctx.hrank
  exact ⟨j, i1431List_bridge hj, ⟨f⟩⟩

theorem conj2_of_facts {G : Type} [Group G] [Finite G] (hD4 : I1431YD4Two) (hU5 : I1431YU5Two)
    (hU4 : I1431YU4Eight) {a y : G} {J I K T : Subgroup G}
    (hctx : S8.L89.Case2Ctx a y J I) (hloc : S8.L89.Case2Local y J K T)
    (hcat : catalogIs (PSimple 3 J) S8.L89.i1431List) :
    catalogIs (PSimple 3 J) S8.L89.i1431List2 := by
  have hy3 : y ^ 3 = 1 := by
    rw [← hctx.hy]
    exact pow_orderOf_eq_one y
  obtain ⟨R, hR1, hR2, hAR, hRσ⟩ := I2016.config_R hctx hloc
  obtain ⟨hA, hA6⟩ := I2016.config_A hctx hloc
  have hQ : CFSG.Open.IsQuasisimple (I2016.PQ 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hctx.hJ
  have hZ : IsPGroup 3 (Subgroup.center (I2016.PQ 3 J)) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three J
  have hσ := I2016.sigma_pow_three_eq_one hctx.hyJ hy3
  have hIs := I2016.isSubnormal_image_fixSub hctx.hyJ hy3 hctx.hI.2.1
  have hIt := I2016.config_TC hctx
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h | h | h | h | h | h
  · exact ⟨i, Or.inl h, ⟨e⟩⟩
  · exact ⟨i, Or.inr (Or.inl h), ⟨e⟩⟩
  · exact (hD4 (I2016.PQ 3 J) (I2016.sigmaHom 3 J ⟨y, hctx.hyJ⟩) (I2016.KphiQ J K).range
      ((I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))) R hQ hZ
      ⟨i, h, ⟨e⟩⟩ hσ hA hA6 hIs hIt hR1 hR2 hRσ hAR).elim
  · exact (hU5 (I2016.PQ 3 J) (I2016.sigmaHom 3 J ⟨y, hctx.hyJ⟩) (I2016.KphiQ J K).range
      ((I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))) R hQ hZ
      ⟨i, h, ⟨e⟩⟩ hσ hA hA6 hIs hIt hR1 hR2 hRσ hAR).elim
  · exact ⟨i, Or.inr (Or.inr h), ⟨e⟩⟩
  · exact (hU4 (I2016.PQ 3 J) (I2016.sigmaHom 3 J ⟨y, hctx.hyJ⟩) (I2016.KphiQ J K).range
      ((I.comap J.subtype).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥J))) R hQ hZ
      ⟨i, h, ⟨e⟩⟩ hσ hA hA6 hIs hIt hR1 hR2 hRσ hAR).elim

end CFSG.LocalAnalysis.GLTheoremA.I1431Y

end
