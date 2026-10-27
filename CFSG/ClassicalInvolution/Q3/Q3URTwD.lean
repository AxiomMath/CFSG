module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3PBranch
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.RouteD.SmallTwinChainX

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups

section Data

variable {G : Type} [Group G] [Finite G]

structure UChain2 (K : Subgroup G) (z : G) where
  j0 : Subgroup G
  j1 : Subgroup G
  β : Subgroup G
  w0 : G
  w1 : G
  t : G
  hj0 : j0 ∈ conjClass3 K
  hj1 : j1 ∈ conjClass3 K
  hβ : β ∈ conjClass3 K
  cl0 : IsClassicalMember3 j0 w0
  cl1 : IsClassicalMember3 j1 w1
  clβ : IsClassicalMember3 β t
  c0 : Commutes K j0
  c1 : Commutes K j1
  cβ1 : Commutes β j1
  nKβ : ¬ Commutes K β
  nβ0 : ¬ Commutes β j0
  n01 : ¬ Commutes j0 j1
  pKβ : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K β
  pβ0 : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W β j0
  p01 : ∃ W : Subgroup G, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W j0 j1
  neKβ : K ≠ β
  neK0 : K ≠ j0
  neK1 : K ≠ j1
  neβ0 : β ≠ j0
  ne01 : j0 ≠ j1
  neβ1 : β ≠ j1
  ztEq : z * t = t * z
  t0Eq : t * w0 = w0 * t
  w01Eq : w0 * w1 = w1 * w0
  z0Eq : z * w0 = w0 * z
  z1Eq : z * w1 = w1 * z
  t1Eq : t * w1 = w1 * t
  Kx : K ∈ centralizingMembers (conjClass3 K) {z * w0}
  j0x : j0 ∈ centralizingMembers (conjClass3 K) {z * w0}
  βx : β ∈ centralizingMembers (conjClass3 K) {z * w0}
  zne0 : z ≠ w0
  xc : ¬ ({z * w0} : Set G) ⊆ Subgroup.center G
  twin : ∀ N ∈ centralizingMembers (conjClass3 K) {z * w0},
    (N = K ∨ Commutes N K) ↔ (N = j0 ∨ Commutes N j0)
  vK : conjSub t K = K
  P1x : LocalOddCentral (conjClass3 K) {z * w0}
  O3x : LocalOddThreeFree3 (conjClass3 K) (z * w0)
  j1x' : j1 ∈ centralizingMembers (conjClass3 K) {w1 * t}
  j0x' : j0 ∈ centralizingMembers (conjClass3 K) {w1 * t}
  βx' : β ∈ centralizingMembers (conjClass3 K) {w1 * t}
  w1net : w1 ≠ t
  xc' : ¬ ({w1 * t} : Set G) ⊆ Subgroup.center G
  twin' : ∀ N ∈ centralizingMembers (conjClass3 K) {w1 * t},
    (N = j1 ∨ Commutes N j1) ↔ (N = β ∨ Commutes N β)
  vj1 : conjSub w0 j1 = j1
  P1x' : LocalOddCentral (conjClass3 K) {w1 * t}
  O3x' : LocalOddThreeFree3 (conjClass3 K) (w1 * t)

end Data

section NonCentral

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem not_subset_center_of_commuting_involutions3 (hnab : ∃ a b : G, a * b ≠ b * a) {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b) :
    ¬ ({a * b} : Set G) ⊆ Subgroup.center G := by
  intro hsub
  have hx2 : orderOf (a * b) = 2 := orderOf_mul_of_commute_involutions ha hb hab hne
  have h' : a * b ∈ Subgroup.center G := hsub (Set.mem_singleton _)
  rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at h'
  rw [h', orderOf_one] at hx2
  omega

end NonCentral

end CFSG.ClassicalInvolution.Q3.Q3W
