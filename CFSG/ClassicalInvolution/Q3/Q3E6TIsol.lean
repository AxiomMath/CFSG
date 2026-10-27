module

public import CFSG.ClassicalInvolution.Q3.Q3E6TCtx
public import CFSG.ClassicalInvolution.Q3.Q3E6TNoCC
public import CFSG.ClassicalInvolution.Q3.Q3E6TIso

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.NonClassical (mem_centralizingMembers_pair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem te6PartnerIsolated3_of_productP1 (hP : Q3TC.ProductP1Input3) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) {β : Subgroup G}
    (hβ : IsPartnerU3 c nd β) (hn3 : ¬ Commutes β (nd.j 3)) : TE6PartnerIsolated3 c nd := by
  classical
  obtain ⟨X, hNR, hvisR⟩ := te6_context3 hP hnab hR c nd hβ hn3
  have hadm : StatedLieAdmissible .POmegaMinus 5 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hfin : Finite (modelUniv .POmegaMinus 5 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  have h0 : 0 < 5 := by norm_num
  have hKx : K ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} :=
    UNodes3.K_mem_centralizingMembers_mul3 c nd h0
  intro N hN pKN _ L hL hLK hNL
  have hLpair := mem_centralizingMembers_pair.mp hL
  have hLx : L ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} := hLpair.1
  have hLz : L ∈ centralizingMembers (conjClass3 K) {z} := ⟨hLx.1, hLpair.2⟩
  have hKL : Commutes K L :=
    commutes_K_of_neU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hLz hLK
  have hnKN : ¬ Commutes K N := by
    obtain ⟨W, hW⟩ := pKN
    exact not_commutes_of_linearBlockStandardPair hW
  obtain ⟨R_K, hR_K, hKimg⟩ := hNR K hKx (not_commutes_self3 c.hz)
  obtain ⟨R_N, hR_N, hNimg⟩ := hNR N hN hnKN
  obtain ⟨R_L, hR_L, hLimg⟩ := hvisR L hL
  have hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R_K R_N :=
    X.stdPair_model hKx hN hR_K hR_N hKimg hNimg pKN
  have hcKL : Commutes R_K R_L := (X.commutes_iff_fund hKx hLx hR_K hKimg hLimg).mp hKL
  have hcNL : Commutes R_N R_L := (X.commutes_iff_fund hN hLx hR_N hNimg hLimg).mp hNL
  exact noCommonCommutant3_pOmegaMinus_five hR_K hR_N hR_L hlin (Gaps.commutes_symm hcKL)
    (Gaps.commutes_symm hcNL)

end CFSG.ClassicalInvolution.Q3.Q3E6T
