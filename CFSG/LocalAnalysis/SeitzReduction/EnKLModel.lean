module

public import CFSG.LocalAnalysis.SeitzReduction.EnKLConfig
public import CFSG.LocalAnalysis.SeitzReduction.EnKLFusion
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviModel
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
import CFSG.RankThree.GF2n.Stroth80.Sec117ConfigBasic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SeitzReduction

theorem false_of_isKLConfig_of_lieModel_E6
    {X : Type} [Group X] [Finite X] {m x a : ℕ}
    (hX : CFSG.Blueprint.LieModel X .E6 m 2 x) {t : X} {N A : Subgroup X}
    (h : IsKLConfig t a N A) : False := by
  have hU : UntwistedChevalleyModel X .E6 (2 ^ x) := (hX.chevalleyExceptionalModel (by decide)).2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hU
  have : CharP K 2 := CFSG.RankThree.Chevalley.charP_two_of_natCard hK
  obtain ⟨g, hg⟩ := EPilot.exists_conj_eq_pinnedElt_highRoot_E6 (h.map e.symm).involution
  have h' := (h.map e.symm).map (MulAut.conj g)
  rw [MulAut.conj_apply, hg] at h'
  exact EPilot.false_of_isKLConfig_pinnedElt_highRoot (Or.inl rfl) E6Pilot.isQuasisimple_a5Levi
    E6Pilot.center_a5Levi_eq_bot h'

theorem false_of_isKLConfig_of_lieModel_E7
    {X : Type} [Group X] [Finite X] {m x a : ℕ}
    (hX : CFSG.Blueprint.LieModel X .E7 m 2 x) {t : X} {N A : Subgroup X}
    (h : IsKLConfig t a N A) : False := by
  have hU : UntwistedChevalleyModel X .E7 (2 ^ x) := (hX.chevalleyExceptionalModel (by decide)).2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hU
  have : CharP K 2 := CFSG.RankThree.Chevalley.charP_two_of_natCard hK
  obtain ⟨g, hg⟩ := EPilot.exists_conj_eq_pinnedElt_highRoot_E7 (h.map e.symm).involution
  have h' := (h.map e.symm).map (MulAut.conj g)
  rw [MulAut.conj_apply, hg] at h'
  exact EPilot.false_of_isKLConfig_pinnedElt_highRoot (Or.inr (Or.inl rfl))
    E7Pilot.isQuasisimple_perpLevi_E7 E7Pilot.center_perpLevi_E7_eq_bot h'

theorem false_of_isKLConfig_of_lieModel_E8
    {X : Type} [Group X] [Finite X] {m x a : ℕ}
    (hX : CFSG.Blueprint.LieModel X .E8 m 2 x) {t : X} {N A : Subgroup X}
    (h : IsKLConfig t a N A) : False := by
  have hU : UntwistedChevalleyModel X .E8 (2 ^ x) := (hX.chevalleyExceptionalModel (by decide)).2
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hU
  have : CharP K 2 := CFSG.RankThree.Chevalley.charP_two_of_natCard hK
  obtain ⟨g, hg⟩ := EPilot.exists_conj_eq_pinnedElt_highRoot_E8 (h.map e.symm).involution
  have h' := (h.map e.symm).map (MulAut.conj g)
  rw [MulAut.conj_apply, hg] at h'
  exact EPilot.false_of_isKLConfig_pinnedElt_highRoot (Or.inr (Or.inr rfl))
    E8Pilot.isQuasisimple_e7Levi E8Pilot.center_e7Levi_eq_bot h'

end CFSG.RankThree.GF2n.Stroth80
