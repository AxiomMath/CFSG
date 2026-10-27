module

public import CFSG.ClassicalInvolution.Q3.Q3E6TEnd

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TW CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

set_option linter.unusedSectionVars false


section Statements

variable {G : Type} [Group G] [Finite G]

structure IsPartnerU3 {K : Subgroup G} {z : G} (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c)
    (β : Subgroup G) : Prop where
  mem : β ∈ conjClass3 K
  cl : ∃ wβ : G, IsClassicalMember3 β wβ
  nK : ¬ Commutes K β
  pK : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β
  n0 : ¬ Commutes β (nd.j 0)
  p0 : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W β (nd.j 0)
  last : Commutes β (nd.j 4)
  mid : ∀ a, 1 ≤ a → a ≤ 2 → Commutes β (nd.j a)

@[expose] def LinearPartnerAtX3 {K : Subgroup G} {z : G} (c : UCtx3 5 (conjClass3 K) K z)
    (nd : UNodes3 c) : Prop :=
  ∃ N ∈ centralizingMembers (conjClass3 K) {z * nd.w 0},
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N) ∧
      ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N (nd.j 0)

@[expose] def TE6Adaptation3 {K : Subgroup G} {z : G} (c : UCtx3 5 (conjClass3 K) K z)
    (nd : UNodes3 c) : Prop :=
  ∀ N : Subgroup G, N ∈ centralizingMembers (conjClass3 K) {z * nd.w 0} →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W K N) →
    (∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W N (nd.j 0)) →
    ∃ V : Fin 3 → Subgroup G, IsTE6Base 3 1 le_rfl (conjClass3 K) K z V ∧ V 0 = nd.j 0 ∧
      Commutes N (V 1) ∧ Commutes N (V 2)

end Statements

@[expose] def EndPartnerAtX3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z →
      ∀ (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) (β : Subgroup G),
        IsPartnerU3 c nd β → ¬ Commutes β (nd.j 3) → LinearPartnerAtX3 c nd

@[expose] def EndAdaptation3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 1 (CompData.model .PSU 6) (conjClass3 K) z →
      ∀ (c : UCtx3 5 (conjClass3 K) K z) (nd : UNodes3 c) (β : Subgroup G),
        IsPartnerU3 c nd β → ¬ Commutes β (nd.j 3) → TE6Adaptation3 c nd

theorem endObstructionData3_of_split (hpartner : EndPartnerAtX3) (hadapt : EndAdaptation3) :
    EndObstructionData3 := by
  intro G _ _ _ hnab K z hR hshape hobs
  obtain ⟨c, nd, β, hβΩ, hβcl, hnK, hpK, hn0, hp0, hlast, hmid, hnot⟩ := hobs
  have hβ : IsPartnerU3 c nd β := ⟨hβΩ, hβcl, hnK, hpK, hn0, hp0, hlast, hmid⟩
  obtain ⟨N, hN, pKN, pNj⟩ := hpartner G hnab K z hR hshape c nd β hβ hnot
  obtain ⟨V, hV, hV0, hc1, hc2⟩ := hadapt G hnab K z hR hshape c nd β hβ hnot N hN pKN pNj
  refine ⟨V, hV, N, hN.1, ?_, hc1, hc2⟩
  rw [hV0]
  exact pNj

end CFSG.ClassicalInvolution.Q3.Q3E6T
