module

public import CFSG.ClassicalInvolution.RouteD.TypeDChain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakChain
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic (Commutes conjSub InClass IsClassicalMember LocalOddCentral
  ExactMembers LieSystemData)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem routeD_typeD_of_partner_pattern [Finite G] (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 6 ≤ n) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaPlus (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternD p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = n := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  exact routeD_typeD_of_pattern_n hp2 hq hMFZ hS3 hn hΩ hex hK hsingle hconn hz hshape hP1 hpat

theorem routeD_typeB_of_partner_pattern [Finite G] (hMFZ : Gaps.FundNoncentral p) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 5 ≤ n) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaOdd (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternB p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = n := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  exact routeD_typeB_of_pattern_n hp2 hq hMFZ hS3 hn hΩ hex hK hsingle hconn hz hshape hP1 hpat

theorem routeD_typeB_pair_of_partner_pattern [Finite G] (hMFZ : Gaps.FundNoncentral p)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 5 ≤ n) {Ω : Set (Subgroup G)}
    (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaOdd (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpat : ∀ β ∈ Ω, ∀ t : G, IsClassicalMember p f β t →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) → HasFixedMember Ω K β z →
      PartnerPatternBPair p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = n := by
  have hf : f ≠ 0 := by rintro rfl; simp at hq
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField hp2 hq
  exact routeD_typeB_pair_of_pattern_n hp2 hq hMFZ hS3 hn hΩ hex hK hsingle hconn hz hshape hP1 hpat

end CFSG.ClassicalInvolution.RouteD
