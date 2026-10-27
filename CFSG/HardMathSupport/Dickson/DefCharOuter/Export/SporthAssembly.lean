module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4Def
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthSymp
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthOrth
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Yardstones.Md42047359a2a (LieFamily lieFamily)
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth

theorem carrierOn_symplecticOrthogonal : CarrierOn .symplecticOrthogonal := by
  intro d hfam _
  obtain ⟨d, hv⟩ := d
  cases d with
  | B r q =>
    rcases CFSG.Models.lieModel_B (G := (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) r q hv
        (MulEquiv.refl _) with h | h
    · exact finite_simple_nonab_of_model (statedClassicalModel_of_lieModel h (Or.inl rfl))
        (Or.inl ⟨rfl, h.1.2.2.1⟩)
    · exact finite_simple_nonab_of_model
        (statedClassicalModel_of_lieModel h (Or.inr (Or.inl rfl)))
        (Or.inr (Or.inl ⟨rfl, h.1.2.2.1⟩))
  | C r q =>
    have h := CFSG.Models.lieModel_C (G := (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group) r q hv
      (MulEquiv.refl _)
    exact finite_simple_nonab_of_model (statedClassicalModel_of_lieModel h (Or.inl rfl))
      (Or.inl ⟨rfl, h.1.2.2.1⟩)
  | D r q =>
    have h := CFSG.Models.lieModel_D (G := (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) r q hv
      (MulEquiv.refl _)
    exact finite_simple_nonab_of_model
      (statedClassicalModel_of_lieModel h (Or.inr (Or.inr (Or.inl rfl))))
      (Or.inr (Or.inr (Or.inl ⟨rfl, h.1.2.2⟩)))
  | twistedD r q =>
    have h := CFSG.Models.lieModel_twistedD
      (G := (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) r q hv (MulEquiv.refl _)
    exact finite_simple_nonab_of_model
      (statedClassicalModel_of_lieModel h (Or.inr (Or.inr (Or.inr rfl))))
      (Or.inr (Or.inr (Or.inr ⟨rfl, h.1.2.2⟩)))
  | _ => simp [lieFamily] at hfam

theorem outerCentOn_symplecticOrthogonal_of_D4 (hD4 : D4ThreeOuterCent) :
    OuterCentOn .symplecticOrthogonal := by
  intro S _ _ hS hnc idx hfam he p hp hp2 hpc β hβ hout
  haveI := hS
  obtain ⟨e⟩ := he
  have hβp : β ^ p = 1 := hβ ▸ pow_orderOf_eq_one β
  obtain ⟨d, hv⟩ := idx
  cases d with
  | B r q =>
    have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_B r q)
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · rcases CFSG.Models.lieModel_B 2 q hv e with h | h
      · subst hpq
        exact outerCentData_psp hp hp2 (statedClassicalModel_of_lieModel h (Or.inl rfl)) hβ hout
      · exact absurd h.1.2.2.1 (by norm_num)
    · exact outerCentData_pomegaOdd
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv (hpq ▸ hp2) hr3 e)
        hp hpq hβp hout
  | C r q =>
    have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_C r q)
    subst hpq
    exact outerCentData_psp hp hp2
      (statedClassicalModel_of_lieModel (CFSG.Models.lieModel_C r q hv e) (Or.inl rfl)) hβ hout
  | D r q =>
    have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_D r q)
    by_cases h43 : r = 4 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := h43
      exact hD4 S q hv ⟨e⟩ hpq.symm β hβp hout
    · exact outerCentData_pomegaPlus
        (statedClassicalModel_of_lieModel (CFSG.Models.lieModel_D r q hv e)
          (Or.inr (Or.inr (Or.inl rfl)))) hp hp2 hpq (fun h4 h3 => h43 ⟨h4, h3⟩) hβp hout
  | twistedD r q =>
    have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_twistedD r q)
    exact outerCentData_pomegaMinus
      (statedClassicalModel_of_lieModel (CFSG.Models.lieModel_twistedD r q hv e)
        (Or.inr (Or.inr (Or.inr rfl)))) hp hp2 hpq hβp hout
  | _ => simp [lieFamily] at hfam

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
