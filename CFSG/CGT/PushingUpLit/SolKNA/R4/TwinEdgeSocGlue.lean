module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeGH
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocCyc4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocL3U3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.TA3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem socleFactsR_l3 {F : Type} [Group F] [Finite F] (h : SmallL3Ne3 F) : SocleFactsR F :=
  SocleFactsR.of_parts (socleInvConj_l3 h) (socleCyc4_l3 h) (socleOutAbelian_l3 h)

theorem socleFactsR_u3 {F : Type} [Group F] [Finite F] (h : SmallU3Ne3 F) : SocleFactsR F :=
  SocleFactsR.of_parts (socleInvConj_u3 h) (socleCyc4_u3 h) (socleOutAbelian_u3 h)

theorem edgelessClassUniqueR_of_socleFacts {r : ℕ} {P : ∀ (F : Type) [Group F], Prop}
    (hP : ∀ (F : Type) [Group F] [Finite F], P F → SocleFactsR F) : EdgelessClassUniqueR r P := by
  intro hr G _ _ J L L₀ hc hPT ⟨WJ, hJ⟩ ⟨WL, hL⟩
  exact (hc.false_of_socleFacts hr (hP _ hPT) hJ hL.soc_twinFree).elim

theorem edgelessClassUniqueR_L2 (r : ℕ) : EdgelessClassUniqueR r SmallL2 :=
  edgelessClassUniqueR_of_socleFacts fun _ _ _ h => socleFactsR_l2 h

theorem edgelessClassUniqueR_L3 (r : ℕ) : EdgelessClassUniqueR r SmallL3Ne3 :=
  edgelessClassUniqueR_of_socleFacts fun _ _ _ h => socleFactsR_l3 h

theorem edgelessClassUniqueR_U3 (r : ℕ) : EdgelessClassUniqueR r SmallU3Ne3 :=
  edgelessClassUniqueR_of_socleFacts fun _ _ _ h => socleFactsR_u3 h

theorem edgelessClassUniqueR_edgelessFamily (r : ℕ) : EdgelessClassUniqueR r EdgelessFamily :=
  edgelessClassUniqueR_edgelessFamily_iff.mpr
    ⟨edgelessClassUniqueR_L2 r, edgelessClassUniqueR_L3 r, edgelessClassUniqueR_U3 r⟩

section Cert


theorem thm4TwinSupplyR_all_of_gh74' (hGH : GH74SectionalModels) :
    ∀ r : ℕ, 4 ≤ r → ∀ n, Thm4TwinSupplyR r n :=
  thm4TwinSupplyR_all_of_gh74 hGH noQ16E4_holds fun r _ => edgelessClassUniqueR_edgelessFamily r

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4
