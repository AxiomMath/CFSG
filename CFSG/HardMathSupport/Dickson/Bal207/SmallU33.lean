module

public import CFSG.HardMathSupport.Dickson.Bal207.SmallBridge
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ChevStrongD4

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Small

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Dickson.I271

theorem IsU33Idx.exists {d : TauCeti.LieTypeIndex} (h : IsU33Idx d) :
    ∃ q, d = .twistedA 2 q ∧ q.p = 3 ∧ q.exponent = 1 := by
  cases d with
  | twistedA r q => exact ⟨q, by rw [h.1], h.2⟩
  | _ => simp only [IsU33Idx] at h

theorem card_u33 {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (hq3 : q.p = 3) (hq1 : q.exponent = 1) :
    Nat.card (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) = 6048 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
  rw [hq3, hq1] at hK
  rw [Nat.card_congr e.toEquiv, hq3, hq1,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
      (by norm_num)]
  decide


theorem isSimpleGroup_u33 {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) :
    IsSimpleGroup (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) := by
  have hm : CFSG.Blueprint.LieModel (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩)
      .PSU 3 q.p q.exponent :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)⟩
  exact (CFSG.LieType.Catalog.lieModel_finite_simple _ _ _ _ _ hm).2.2

theorem bal207PlusSmallU33 (G : ∀ (S : Type) [Group S], MulAut S → Prop) :
    Bal207PlusSmallU33 G := by
  intro X _ _ hX K B A ctx hIH a haA ha1 J hJ hS hBJ
  obtain ⟨hsn, hJC, hH⟩ := small_data ctx haA hJ hBJ
  obtain ⟨⟨d, hv⟩, hd, ⟨eJ⟩⟩ := hS
  have hd' : IsU33Idx d := hd
  obtain ⟨q, rfl, hq3, hq1⟩ := IsU33Idx.exists hd'
  haveI := isSimpleGroup_u33 hv
  obtain ⟨⟨e₃⟩, -⟩ := barX_centralQuotient hJC eJ.isSimpleGroup
  let eT := e₃.symm.trans eJ
  have hcard : Nat.card (↥(barX 3 (Subgroup.centralizer ({a} : Set X)) J) ⧸
      Subgroup.center ↥(barX 3 (Subgroup.centralizer ({a} : Set X)) J)) = 6048 := by
    rw [Nat.card_congr eT.toEquiv]
    exact card_u33 hv hq3 hq1
  refine stronglyLocallyOneBalanced_of_bar ctx.prime hsn hBJ ?_
  refine strong_leaf (chevStrong_holds 3) hH (Or.inl ⟨?_, ?_, ?_⟩)
  · refine Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩, ?_, ⟨eT⟩⟩
    show (TauCeti.LieTypeIndex.twistedA 2 q).characteristic = 3
    rw [TauCeti.LieTypeIndex.characteristic_twistedA]
    exact hq3
  · intro hL
    have h9828 := CFSG.HardMathSupport.Dickson.DefCharOuter.Export.excCard_isLTwoTwentySeven hL
    rw [hcard] at h9828
    norm_num at h9828
  · rintro ⟨f⟩
    have h360 := Nat.card_congr f.toEquiv
    rw [hcard, nat_card_alternatingGroup, Nat.card_fin] at h360
    norm_num [Nat.factorial] at h360

end CFSG.HardMathSupport.Dickson.Bal207.Small

end
