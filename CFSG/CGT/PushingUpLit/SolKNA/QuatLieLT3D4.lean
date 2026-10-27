module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLT0Basic
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegTD4

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution.Generic


theorem lie3At_trialityD4 (n : ℕ) : Lie3At .trialityD4 n := by
  intro hf hadm X _ _ ψ hψ hker R hR K hK R₀ hq hPR
  exfalso
  have hn : n = 0 := hadm.2.2
  subst hn
  have : IsSimpleGroup X := hK.simple
  obtain ⟨hqs, hmodel⟩ := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .trialityD4 0 3 1
    Nat.prime_three hf hadm
  have : Group.IsPerfect (modelUniv .trialityD4 0 3 1 Nat.prime_three).K := ⟨hqs.1⟩
  have hZ : Subgroup.center X = (Subgroup.center _).map ψ :=
    (CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel ψ hψ hker).symm
  have hmodelX : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .trialityD4 0 3 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective ψ hψ hker hZ) hmodel
  have hZX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hK.nonab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hLie : CFSG.Blueprint.LieModel X .trialityD4 0 3 1 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot) hmodelX
  exact negModel_TD4 X hLie K hK R₀ hq

end CFSG.CGT.PushingUpLit.SolKNA
