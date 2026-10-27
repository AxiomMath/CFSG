module

public import CFSG.ClassicalInvolution.RouteD.GapsFrBSmallFinal
public import CFSG.ClassicalInvolution.RouteD.GapsFrBFinal
public import CFSG.ClassicalInvolution.RouteD.SmallBWired
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakChain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBLocal
public import CFSG.ClassicalInvolution.RouteD.GapsEnd4Final
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => CoreAssembly.conjClass

@[expose] def TwinBExistsOn (p f : ℕ) [Fact p.Prime] (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, P m →
      LocalShapeT p f 2 .POmegaOdd m (𝒞 K) z →
      ∃ β ∈ 𝒞 K, ∃ t : G, IsClassicalMember p f β t ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
        PartnerPatternBPair p f m (𝒞 K) K β t

@[expose] def TwinBExistsCase (p f m : ℕ) [Fact p.Prime] : Prop :=
  TwinBExistsOn p f fun k => k = m

@[expose] def TwinBExistsSmallRest (p f : ℕ) [Fact p.Prime] : Prop :=
  TwinBExistsOn p f fun m => m = 3 ∨ m = 4 ∨ m = 6

theorem twinBExistsSmallRest_of_small (h : TwinBSmallRest p f) : TwinBExistsSmallRest p f := by
  intro G _ _ _ hnab K z S m hm hshape
  have hm3 : 3 ≤ m := by omega
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf, hm3, S.odd⟩
  obtain ⟨c⟩ := TCtx.nonempty_odd hm3 S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_odd hm3 hadm (single_class K) hshape
  exact ⟨β, hβ, t, ht, hKβ, h G hnab K z S m hm hshape β hβ t ht hKβ hfix⟩

theorem routeD_typeB_pair_of_exists_pattern_n {G : Type} [Group G] [Finite G] (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {n : ℕ} (hn : 5 ≤ n)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaOdd (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpat : ∃ β ∈ Ω, ∃ t : G, IsClassicalMember p f β t ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
      PartnerPatternBPair p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : m + 2 - 2 = m := by omega
  rw [hm] at hshape hpat
  obtain ⟨β, hβ, t, ht, hKβ, hpat'⟩ := hpat
  exact routeD_typeB_pair hp2 hq hMFZ hS3 (by omega) hΩ hK hsingle hconn hz hshape hP1 hβ ht hKβ
    hpat'

theorem rowTwinB_of_exists (hMFZ : Gaps.FundNoncentral p)
    (h : TwinBExistsOn p f fun m => 3 ≤ m) : RowPiece p f ShapeTwinB := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeT p f 2 .POmegaOdd (n + 2 - 2) (𝒞 K) z := by rw [hn']; exact hS
  have hf : f ≠ 0 := by
    rintro rfl
    simpa using S.five
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField S.odd S.five
  obtain ⟨β, hβ, t, ht, hKβ, hpat⟩ := h G hnab K z S n hn hS
  obtain ⟨D, -, -⟩ := routeD_typeB_pair_of_exists_pattern_n S.odd S.five hMFZ hS3 (n := n + 2)
    (by omega) S.inClass (mem_conjClass_self K) (single_class K) S.conn S.cls hS' S.p1
    ⟨β, hβ, t, ht, hKβ, by rwa [hn']⟩
  exact ⟨D⟩

theorem twinBExistsOn_proved (hMFZ : Gaps.FundNoncentral p) :
    TwinBExistsOn p f fun m => 3 ≤ m ∧ m ≠ 3 ∧ m ≠ 4 ∧ m ≠ 6 := by
  intro G _ _ _ hnab K z S m hm hshape
  obtain ⟨hm3, hm3', hm4, hm6⟩ := hm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaOdd m p f := ⟨Fact.out, hf, hm3, S.odd⟩
  obtain ⟨c⟩ := TCtx.nonempty_odd hm3 S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_odd hm3 hadm (single_class K) hshape
  refine ⟨β, hβ, t, ht, hKβ, ?_⟩
  by_cases h5 : m = 5
  · subst h5
    exact Gaps.PartnerPatternBPair.of_fixed_member_five_last hMFZ c (single_class K) hshape hβ ht
      hKβ hfix
  by_cases h7 : m = 7
  · subst h7
    exact Gaps.PartnerPatternBPair.of_fixed_member_seven_last hMFZ c (single_class K) hshape hβ
      ht hKβ hfix
  · exact Gaps.PartnerPatternBPair.of_fixed_member_last (by omega) hMFZ c (single_class K) hshape
      hβ ht hKβ hfix

theorem twinBExistsOn_of_small (hMFZ : Gaps.FundNoncentral p) (hR : TwinBExistsSmallRest p f) :
    TwinBExistsOn p f fun m => 3 ≤ m := by
  intro G _ _ _ hnab K z S m hm hshape
  by_cases hsmall : m = 3 ∨ m = 4 ∨ m = 6
  · exact hR G hnab K z S m hsmall hshape
  · exact twinBExistsOn_proved hMFZ G hnab K z S m ⟨hm, by omega, by omega, by omega⟩ hshape

theorem twinBExistsOn_of_cases (hMFZ : Gaps.FundNoncentral p) (h3 : TwinBExistsCase p f 3)
    (h4 : TwinBExistsCase p f 4) (h6 : TwinBExistsCase p f 6) :
    TwinBExistsOn p f fun m => 3 ≤ m :=
  twinBExistsOn_of_small hMFZ fun G _ _ _ hnab K z S m hm hshape => by
    rcases hm with rfl | rfl | rfl
    · exact h3 G hnab K z S 3 rfl hshape
    · exact h4 G hnab K z S 4 rfl hshape
    · exact h6 G hnab K z S 6 rfl hshape

theorem rowTwinB_of_exists_small (hMFZ : Gaps.FundNoncentral p) (hR : TwinBExistsSmallRest p f) :
    RowPiece p f ShapeTwinB :=
  rowTwinB_of_exists hMFZ (twinBExistsOn_of_small hMFZ hR)

end CFSG.ClassicalInvolution.RouteD.TwinY
