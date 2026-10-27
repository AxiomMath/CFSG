module

public import CFSG.ClassicalInvolution.Q3.Q3E6TCtx
public import CFSG.ClassicalInvolution.Q3.Q3E6TTwin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Q3.Q3W
open CFSG.ClassicalInvolution.RouteD.NonClassical (mem_centralizingMembers_pair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem exists_linearPartnerAtX3 (hP : Q3TC.ProductP1Input3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) {β : Subgroup G}
    (hβ : IsPartnerU3 c nd β) (hn3 : ¬ Commutes β (nd.j 3)) : LinearPartnerAtX3 c nd := by
  classical
  obtain ⟨X, -, hvisR⟩ := te6_context3 hP hnab hR c nd hβ hn3
  have h0 : 0 < 5 := by norm_num
  have hadm : StatedLieAdmissible .POmegaMinus 5 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have hKx : K ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} :=
    UNodes3.K_mem_centralizingMembers_mul3 c nd h0
  have hj0x : nd.j 0 ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} :=
    UNodes3.mem_centralizingMembers_mul3 c nd h0 (Or.inl rfl)
  have hKvis : K ∈ centralizingMembers (conjClass3 K) {z * nd.w 0, z} :=
    mem_centralizingMembers_pair.mpr ⟨hKx, isSubnormal_le c.hz.subnormal⟩
  have hj0vis : nd.j 0 ∈ centralizingMembers (conjClass3 K) {z * nd.w 0, z} :=
    mem_centralizingMembers_pair.mpr ⟨hj0x, (nd.mem 0 h0).2⟩
  obtain ⟨R₀, hR₀, hKR₀⟩ := hvisR K hKvis
  obtain ⟨R₃, hR₃, hJR⟩ := hvisR (nd.j 0) hj0vis
  have hcf := (Q3W.yData3_minus (by norm_num : 4 ≤ 5) hadm).central
  obtain ⟨β', hβ'x, hW₁, hW₂⟩ := exists_partner_of_xctx_e6
    twinPartnerFactTwin_pOmegaMinus_five3 X hcf c.hz (nd.isCl 0 h0) rfl hKx hj0x
    (nd.commK 0 h0) (nd.ne_K 0 h0).symm hR₀ hR₃ hKR₀ hJR
  exact ⟨β', hβ'x, hW₁, hW₂⟩

theorem endPartnerAtX3_of_productP1 (hP : Q3TC.ProductP1Input3) : EndPartnerAtX3 := by
  intro G _ _ _ hnab K z hR _ c nd β hβ hn3
  exact exists_linearPartnerAtX3 hP hnab hR c nd hβ hn3

end CFSG.ClassicalInvolution.Q3.Q3E6T
