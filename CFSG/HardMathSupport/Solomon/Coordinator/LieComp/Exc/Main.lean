module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyExc
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.NotA6
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md42047359a2a

set_option linter.unusedSectionVars false

@[expose] def ExcChar3Export : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = .exceptional →
      lieIndexChar idx.1 = 3 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → LieCompExport 3 β ∨ NoThreeComponents β

theorem lieCompOn_exceptional (hres : ExcRationalLieTypes) (hout : TrialityOuterExport)
    (hchar3 : ExcChar3Export) : LieCompOn .exceptional := by
  refine lieCompOn_of_exports fun S _ _ hs hna idx hF he β hβ => ?_
  classical
  have hnotree : ∀ m, idx.1 ≠ .reeG2 m := fun m h => by simp [lieFamily, h] at hF
  by_cases hβ1 : β = 1
  · subst hβ1
    obtain ⟨e⟩ := he
    haveI := hs
    exact Or.inl (lieCompExport_one hna idx ⟨e⟩
      ⟨fun f => (isEmpty_cat_alt6 idx (Or.inl hF)).false (e.symm.trans f)⟩)
  by_cases h3 : lieIndexChar idx.1 = 3
  · rw [h3]
    exact hchar3 S hs hna idx hF h3 he β hβ hβ1
  left
  obtain ⟨e⟩ := he
  have hlayer : PerfectInLayer β :=
    lieSemisimpleCentExceptional S hs hna idx hF ⟨e⟩ 3 Nat.prime_three (by norm_num)
      (fun h => h3 (by rw [← characteristic_eq_lieIndexChar]; exact h.symm)) β hβ hβ1
  have hmon : ∀ {τ : Tag}, (τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      MonomialToralAt τ 3 := fun hτ =>
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ Nat.prime_three
      (by norm_num)
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | E6 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .E6) (Or.inr (Or.inr (Or.inl rfl)))
      (c := TauCeti.LieTypeIndex.E6) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
      (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
      (fun q _ => TauCeti.LieTypeIndex.valid_E6 q) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E6 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | E7 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (c := TauCeti.LieTypeIndex.E7) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
      (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E7 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | E8 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (c := TauCeti.LieTypeIndex.E8) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E8 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | F4 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .F4) (Or.inr (Or.inl rfl))
      (c := TauCeti.LieTypeIndex.F4) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.F4 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | G2 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_untw hres (τ := .G2) (Or.inl rfl)
      (c := TauCeti.LieTypeIndex.G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
      (fun q => TauCeti.LieTypeIndex.characteristic_G2 q)
      (fun q hq => by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hq rfl, by simp⟩)
      (fun q hv _ => (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)
      (fun q hv => isEmpty_cat_alt6 ⟨.G2 q, hv⟩ (Or.inl rfl)) q hv hq3 e β hβ hβ1 hlayer
  | twistedE6 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_twE6 hres
      (fun q hv => isEmpty_cat_alt6 ⟨.twistedE6 q, hv⟩ (Or.inl rfl))
      (hmon (by simp)) q hv hq3 e β hβ hβ1 hlayer
  | trialityD4 q =>
    have hq3 : 3 ≠ q.p := fun h => h3 (by simp [lieIndexChar]; exact h.symm)
    exact lieCompExport_triD4 hres hout (hmon (by simp)) q hv hq3 e β hβ hβ1 hlayer
  | _ => simp [lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
