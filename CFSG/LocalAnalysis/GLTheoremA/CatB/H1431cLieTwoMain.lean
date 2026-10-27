module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoLin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoUni
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoSp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoExc
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoRest

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem lieSTwoAt_of_families
    (hA : LieSTwoAt fun d => ∃ n q, d = .A n q)
    (htA : LieSTwoAt fun d => ∃ n q, d = .twistedA n q)
    (hB : LieSTwoAt fun d => ∃ n q, d = .B n q)
    (hD : LieSTwoAt fun d => ∃ n q, d = .D n q)
    (htD : LieSTwoAt fun d => ∃ n q, d = .twistedD n q)
    (hE : LieSTwoAt fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q)
    (hF4 : LieSTwoAt fun d => ∃ q, d = .F4 q)
    (htE6 : LieSTwoAt fun d => ∃ q, d = .twistedE6 q)
    (hO : LieSTwoAt LieSTwoOther) : LieSTwoAt fun _ => True := by
  rintro Y _ _ hY hcore hRk ⟨d, hv⟩ - hc hf he α hα h3 h1
  cases d with
  | A n q => exact hA Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he α hα h3 h1
  | twistedA n q => exact htA Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he α hα h3 h1
  | B n q => exact hB Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he α hα h3 h1
  | D n q => exact hD Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he α hα h3 h1
  | twistedD n q => exact htD Y hY hcore hRk ⟨_, hv⟩ ⟨n, q, rfl⟩ hc hf he α hα h3 h1
  | E6 q => exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inl rfl⟩ hc hf he α hα h3 h1
  | E7 q => exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inr (Or.inl rfl)⟩ hc hf he α hα h3 h1
  | E8 q => exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inr (Or.inr rfl)⟩ hc hf he α hα h3 h1
  | F4 q => exact hF4 Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he α hα h3 h1
  | twistedE6 q => exact htE6 Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he α hα h3 h1
  | C n q => exact hO Y hY hcore hRk ⟨_, hv⟩ (Or.inl ⟨n, q, rfl⟩) hc hf he α hα h3 h1
  | G2 q => exact hO Y hY hcore hRk ⟨_, hv⟩ (Or.inr (Or.inl ⟨q, rfl⟩)) hc hf he α hα h3 h1
  | trialityD4 q =>
    exact hO Y hY hcore hRk ⟨_, hv⟩ (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))) hc hf he α hα h3 h1
  | suzuki m =>
    exact hO Y hY hcore hRk ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))) hc hf he α hα h3
      h1
  | reeG2 m =>
    exact hO Y hY hcore hRk ⟨_, hv⟩ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))) hc hf he
      α hα h3 h1
  | reeF4 m =>
    exact hO Y hY hcore hRk ⟨_, hv⟩
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))))) hc hf he α hα h3 h1
  | tits =>
    exact hO Y hY hcore hRk ⟨_, hv⟩
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hc hf he α hα h3 h1

theorem lieSTwo_holds :
    LieSTwo := by
  have hGA := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hLO := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
  exact lieSTwo_of_at (lieSTwoAt_of_families (lieSTwoAt_linear hGA hLO)
    (lieSTwoAt_twistedA hGA hLO) (lieSTwoAt_B hGA hLO) (lieSTwoAt_D hGA hLO d4TwoShape_holds)
    (lieSTwoAt_twistedD hGA hLO) lieSTwoAt_E (lieSTwoAt_F4 hLO) lieSTwoAt_twistedE6
    (lieSTwoAt_other hLO))

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
