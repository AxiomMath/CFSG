module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPFamilies
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsInterface
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyExc
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.NotA6

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Yardstones.Md42047359a2a

set_option linter.unusedSectionVars false


theorem lieCompsOn_exceptional {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hres : ExcRationalLieTypesP p) (hD4 : TrialityFieldExportP p) :
    LieCompsOn p .exceptional := by
  intro S _ _ hs hna idx hF he β hβ hβ1 hq
  classical
  obtain ⟨e⟩ := he
  have hp2 : p ≠ 2 := by omega
  have hmon : ∀ {τ : Tag}, (τ = .G2 ∨ τ = .F4 ∨ τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      MonomialToralAt τ p := fun hτ =>
    monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ hp hp2
  have hlayer : lieIndexChar idx.1 ≠ p → PerfectInLayer β := fun hc =>
    lieSemisimpleCentExceptional S hs hna idx hF ⟨e⟩ p hp hp2
      (fun h => hc (by rw [← characteristic_eq_lieIndexChar]; exact h.symm)) β hβ hβ1
  obtain ⟨d, hv⟩ := idx
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  cases d with
  | E6 q =>
    exact lieCompsExport_untwP hp hp5 hres (τ := .E6) (Or.inr (Or.inr (Or.inl rfl)))
      (c := TauCeti.LieTypeIndex.E6) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6
      (fun q => TauCeti.LieTypeIndex.characteristic_E6 q)
      (fun q _ => TauCeti.LieTypeIndex.valid_E6 q) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E6 q, hv⟩ (Or.inl rfl)) q hv e β hβ hβ1 hq hlayer
  | E7 q =>
    exact lieCompsExport_untwP hp hp5 hres (τ := .E7) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (c := TauCeti.LieTypeIndex.E7) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7
      (fun q => TauCeti.LieTypeIndex.characteristic_E7 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E7 q, hv⟩ (Or.inl rfl)) q hv e β hβ hβ1 hq hlayer
  | E8 q =>
    exact lieCompsExport_untwP hp hp5 hres (τ := .E8) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (c := TauCeti.LieTypeIndex.E8) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8
      (fun q => TauCeti.LieTypeIndex.characteristic_E8 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.E8 q, hv⟩ (Or.inl rfl)) q hv e β hβ hβ1 hq hlayer
  | F4 q =>
    exact lieCompsExport_untwP hp hp5 hres (τ := .F4) (Or.inr (Or.inl rfl))
      (c := TauCeti.LieTypeIndex.F4) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4
      (fun q => TauCeti.LieTypeIndex.characteristic_F4 q)
      (fun q _ => by simp) (fun q _ h => absurd h (by decide))
      (fun q hv => isEmpty_cat_alt6 ⟨.F4 q, hv⟩ (Or.inl rfl)) q hv e β hβ hβ1 hq hlayer
  | G2 q =>
    exact lieCompsExport_untwP hp hp5 hres (τ := .G2) (Or.inl rfl)
      (c := TauCeti.LieTypeIndex.G2) CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2
      (fun q => TauCeti.LieTypeIndex.characteristic_G2 q)
      (fun q hq => by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨hq rfl, by simp⟩)
      (fun q hv _ => (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1)
      (fun q hv => isEmpty_cat_alt6 ⟨.G2 q, hv⟩ (Or.inl rfl)) q hv e β hβ hβ1 hq hlayer
  | twistedE6 q =>
    exact lieCompsExport_twE6P hp hp5 hres
      (fun q hv => isEmpty_cat_alt6 ⟨.twistedE6 q, hv⟩ (Or.inl rfl))
      (hmon (by simp)) q hv e β hβ hβ1 hq hlayer
  | trialityD4 q =>
    exact lieCompsExport_triD4P hp hp5 hres hD4 (hmon (by simp)) q hv e β hβ hβ1 hq hlayer
  | _ => simp [lieFamily] at hF

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
