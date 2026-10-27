module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcPlumbFam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.HardMathSupport.Dickson.Sec6 (FamG2 FamF4 FamE6 FamE7 FamE8 FamTwE6 FamTriD4 FamReeF4
  FamSz FamTits)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.Blueprint.Chevalley

@[expose] def ExcOrderRes : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (catalogIs S (ambiguousChev 2) ∨ ∃ d : ValidLieTypeIndex, (FamSz d.1 ∨ FamTits d.1) ∧
      Nonempty (S ≃* (CFSGIndex.lie d).Group)) →
    ∀ β : MulAut S, ¬ L3U3Pumpup S β

@[expose] def ExcRankRes : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : ValidLieTypeIndex),
    (FamG2 d.1 ∨ FamTriD4 d.1 ∨ FamReeF4 d.1) →
      CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d.1 →
    (S ≃* (CFSGIndex.lie d).Group) → ∀ β : MulAut S, β ∈ innAutDerived S → ¬ L3U3Pumpup S β

@[expose] def Char2L3U3All : Prop :=
  ∀ τ : Tag, (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → ∀ k, Char2L3U3 τ k

section Dispatch


theorem mem_innAutDerived_of_exc {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {d : ValidLieTypeIndex} (hd : ExcIdx d.1)
    (hc : d.1.characteristic = 2) (e : S ≃* (CFSGIndex.lie d).Group) {labK : GLALabel}
    {β : MulAut S} (hinn : CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind S labK β) :
    β ∈ innAutDerived S := by
  have hcen : Subgroup.center S = ⊥ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm hs hnab
  have hK : HasLabel S (· = labK) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hinn
  obtain ⟨hnd, hne⟩ := not_derived_not_excl_of_excGLATag
    (tag_of_hasLabel_exc CFSG.StandardType.ggLabelRigidInput_holds hs hnab hd hc e hK)
  exact mem_innAutDerived_of_innDiagKind_nd hcen hnd hne hinn

theorem i1419ExcS_of_res (hO : ExcOrderRes) (hR : ExcRankRes) (hres : Char2L3U3All) :
    I1419ExcS := by
  intro S _ _ hs hnab hch hncl labK β hinn hP
  rcases hch with ⟨i, hi, ⟨e⟩⟩ | hamb
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie dl =>
      obtain ⟨d, hv⟩ := dl
      have hc : d.characteristic = 2 := hi
      have hcl : ∀ _ : CFSG.LocalAnalysis.GLTheoremA.K1419.I1419ClassLie d, False := fun hcl =>
        hncl ⟨.lie ⟨d, hv⟩, ⟨hc, hcl⟩, ⟨e⟩⟩
      cases d with
      | A r q => exact hcl trivial
      | twistedA r q => exact hcl trivial
      | B r q => exact hcl trivial
      | C r q => exact hcl trivial
      | D r q => exact hcl trivial
      | twistedD r q => exact hcl trivial
      | G2 q =>
        exact hR S ⟨_, hv⟩ (Or.inl trivial) ((LieTypeIndex.characteristic_G2 q).symm.trans hc) e β
          (mem_innAutDerived_of_exc hs hnab (d := ⟨_, hv⟩) (Or.inl trivial) hc e hinn) hP
      | trialityD4 q =>
        exact hR S ⟨_, hv⟩ (Or.inr (Or.inl trivial))
          ((LieTypeIndex.characteristic_trialityD4 q).symm.trans hc) e β
          (mem_innAutDerived_of_exc hs hnab (d := ⟨_, hv⟩)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))) hc e hinn) hP
      | reeF4 m =>
        exact hR S ⟨_, hv⟩ (Or.inr (Or.inr trivial)) trivial e β
          (mem_innAutDerived_of_exc hs hnab (d := ⟨_, hv⟩)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr trivial))))))) hc e hinn) hP
      | F4 q =>
        exact not_l3u3Pumpup_exc hres ⟨_, hv⟩ (Or.inl trivial)
          ((LieTypeIndex.characteristic_F4 q).symm.trans hc) e β
          (mem_innAutDerived_of_exc hs hnab (d := ⟨_, hv⟩) (Or.inr (Or.inl trivial)) hc e hinn) hP
      | E6 q =>
        exact not_l3u3Pumpup_exc hres ⟨_, hv⟩ (Or.inr (Or.inl trivial))
          ((LieTypeIndex.characteristic_E6 q).symm.trans hc) e β
          (mem_innAutDerived_of_exc hs hnab (d := ⟨_, hv⟩) (Or.inr (Or.inr (Or.inl trivial)))
            hc e hinn) hP
      | twistedE6 q =>
        exact not_l3u3Pumpup_exc hres ⟨_, hv⟩ (Or.inr (Or.inr (Or.inl trivial)))
          ((LieTypeIndex.characteristic_twistedE6 q).symm.trans hc) e β
          (mem_innAutDerived_of_exc hs hnab (d := ⟨_, hv⟩)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial)))))) hc e hinn) hP
      | E7 q =>
        exact not_l3u3Pumpup_exc hres ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inl trivial))))
          ((LieTypeIndex.characteristic_E7 q).symm.trans hc) e β
          (mem_innAutDerived_of_exc hs hnab (d := ⟨_, hv⟩)
            (Or.inr (Or.inr (Or.inr (Or.inl trivial)))) hc e hinn) hP
      | E8 q =>
        exact not_l3u3Pumpup_exc hres ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr trivial))))
          ((LieTypeIndex.characteristic_E8 q).symm.trans hc) e β
          (mem_innAutDerived_of_exc hs hnab (d := ⟨_, hv⟩)
            (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))) hc e hinn) hP
      | suzuki m => exact hO S hs hnab (Or.inr ⟨⟨_, hv⟩, Or.inl trivial, ⟨e⟩⟩) β hP
      | tits => exact hO S hs hnab (Or.inr ⟨⟨_, hv⟩, Or.inr trivial, ⟨e⟩⟩) β hP
      | reeG2 m =>
        exfalso
        have h3 : (LieTypeIndex.reeG2 m).characteristic = 3 := LieTypeIndex.characteristic_reeG2 m
        omega
  · exact hO S hs hnab (Or.inl hamb) β hP

theorem i1419ExcFact_of_res (hO : ExcOrderRes) (hR : ExcRankRes) (hres : Char2L3U3All) :
    CFSG.LocalAnalysis.GLTheoremA.K1419.I1419ExcFact :=
  i1419ExcFact_of_S (i1419ExcS_of_res hO hR hres)

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
