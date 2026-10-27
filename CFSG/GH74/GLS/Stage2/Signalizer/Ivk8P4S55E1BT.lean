module

public import CFSG.Milestones.CL_LIT_Borel_Tits_local_parabolic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG

theorem holds_of_lieModel {Y : Type} [Group Y] {t : Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (hmodel : Blueprint.LieModel Y t n p f) (ht : t ≠ .Tits) :
    LieType.BorelTits.Holds Y p := by
  intro U hU hUp
  obtain ⟨S, P, hP, hN, hcore, hUP, hS, -⟩ :=
    Milestones.cl_lit_borel_tits_local_parabolic_all_models Y t n p f hmodel U hU hUp
  exact ⟨S, P, hP, hN, hcore, hUP, hS ht⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
