module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType


theorem innAutDerivedInnDiag_unitary :
    InnAutDerivedInnDiag fun i =>
      ∃ (n : ℕ) (q : TauCeti.PrimePower), i = .twistedA n q ∧ q.p = 2 := by
  intro Γ _ _ p J a haJ hp hq hcat hmem
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ hp' => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    obtain ⟨n, q, hd, hq2⟩ := hi
    subst hd
    have hLM : CFSG.Blueprint.LieModel (PSimple p J) .PSU (n + 1) 2 q.exponent := by
      have h := CFSG.Models.lieModel_twistedA n q hv e
      have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n q, hv⟩ = q.p :=
        TauCeti.LieTypeIndex.characteristic_twistedA n q
      have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n q, hv⟩ = q.exponent :=
        TauCeti.LieTypeIndex.fieldExponent_twistedA n q
      rw [hc, hf, hq2] at h
      exact CFSG.Models.LieModel.toBlueprint (by decide) h
    exact innDiagOn_of_lieModel haJ hq hLM (by simp) (by decide) hmem

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
