module

public import CFSG.ClassicalInvolution.MilestoneAssemblyWired5
public import CFSG.ClassicalInvolution.RouteD.TypeDChain
public import CFSG.ClassicalInvolution.RouteD.GapsFrPattern
public import CFSG.ClassicalInvolution.RouteD.GapsFrFive
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

@[expose] def TwinDExistsOn (p f : ℕ) [Fact p.Prime] (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, P m →
      LocalShapeT p f 2 .POmegaPlus m (𝒞 K) z →
      ∃ β ∈ 𝒞 K, ∃ t : G, IsClassicalMember p f β t ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
        PartnerPatternD p f m (𝒞 K) K β t

@[expose] def TwinDExistsCase (p f m : ℕ) [Fact p.Prime] : Prop :=
  TwinDExistsOn p f fun k => k = m

@[expose] def TwinDExistsSmall₄₆ (p f : ℕ) [Fact p.Prime] : Prop :=
  TwinDExistsOn p f fun m => m = 4 ∨ m = 6

theorem twinDExistsSmall₄₆_of_small (h : MilestoneAssembly.TwinDSmall₄₆ p f) :
    TwinDExistsSmall₄₆ p f := by
  intro G _ _ _ hnab K z S m hm hshape
  have hm4 : 4 ≤ m := by omega
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf, by show 4 ≤ m; omega⟩
  obtain ⟨c⟩ := TCtx.nonempty_plus hm4 S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_plus hm4 hadm (single_class K) hshape
  exact ⟨β, hβ, t, ht, hKβ, h G hnab K z S m hm hshape β hβ t ht hKβ hfix⟩

theorem routeD_typeD_of_exists_pattern_n {G : Type} [Group G] [Finite G] (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hMFZ : Gaps.FundNoncentral p)
    (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {n : ℕ} (hn : 6 ≤ n)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaPlus (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpat : ∃ β ∈ Ω, ∃ t : G, IsClassicalMember p f β t ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
      PartnerPatternD p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : m + 2 - 2 = m := by omega
  rw [hm] at hshape hpat
  obtain ⟨β, hβ, t, ht, hKβ, hpat'⟩ := hpat
  exact routeD_typeD hp2 hq hMFZ hS3 (by omega) hΩ hK hsingle hconn hz hshape hP1 hβ ht hKβ hpat'

theorem rowTwinD_of_exists (hMFZ : Gaps.FundNoncentral p)
    (h : TwinDExistsOn p f fun m => 4 ≤ m) : RowPiece p f ShapeTwinD := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeT p f 2 .POmegaPlus (n + 2 - 2) (𝒞 K) z := by rw [hn']; exact hS
  have hf : f ≠ 0 := by
    rintro rfl
    simpa using S.five
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField S.odd S.five
  obtain ⟨β, hβ, t, ht, hKβ, hpat⟩ := h G hnab K z S n hn hS
  obtain ⟨D, -, -⟩ := routeD_typeD_of_exists_pattern_n S.odd S.five hMFZ hS3 (n := n + 2)
    (by omega) S.inClass (mem_conjClass_self K) (single_class K) S.conn S.cls hS' S.p1
    ⟨β, hβ, t, ht, hKβ, by rwa [hn']⟩
  exact ⟨D⟩

theorem twinDExistsOn_proved (hMFZ : Gaps.FundNoncentral p) :
    TwinDExistsOn p f fun m => 4 ≤ m ∧ m ≠ 4 ∧ m ≠ 6 := by
  intro G _ _ _ hnab K z S m hm hshape
  obtain ⟨hm4, hm4', hm6⟩ := hm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaPlus m p f := ⟨Fact.out, hf, by show 4 ≤ m; omega⟩
  obtain ⟨c⟩ := TCtx.nonempty_plus hm4 S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_plus hm4 hadm (single_class K) hshape
  refine ⟨β, hβ, t, ht, hKβ, ?_⟩
  by_cases h7 : 7 ≤ m
  · exact Gaps.PartnerPatternD.of_fixed_member h7 hMFZ c (single_class K) hshape hβ ht hKβ hfix
  · obtain rfl : m = 5 := by omega
    exact Gaps.PartnerPatternD.of_fixed_member_five hMFZ c (single_class K) hshape hβ ht hKβ hfix

theorem twinDExistsOn_of_small (hMFZ : Gaps.FundNoncentral p) (hS : TwinDExistsSmall₄₆ p f) :
    TwinDExistsOn p f fun m => 4 ≤ m := by
  intro G _ _ _ hnab K z S m hm hshape
  by_cases h46 : m = 4 ∨ m = 6
  · exact hS G hnab K z S m h46 hshape
  · exact twinDExistsOn_proved hMFZ G hnab K z S m ⟨hm, by omega, by omega⟩ hshape

theorem twinDExistsOn_of_cases (hMFZ : Gaps.FundNoncentral p) (h4 : TwinDExistsCase p f 4)
    (h6 : TwinDExistsCase p f 6) : TwinDExistsOn p f fun m => 4 ≤ m :=
  twinDExistsOn_of_small hMFZ fun G _ _ _ hnab K z S m hm hshape => by
    rcases hm with rfl | rfl
    · exact h4 G hnab K z S 4 rfl hshape
    · exact h6 G hnab K z S 6 rfl hshape

theorem rowTwinD_of_exists_small (hMFZ : Gaps.FundNoncentral p) (hS : TwinDExistsSmall₄₆ p f) :
    RowPiece p f ShapeTwinD :=
  rowTwinD_of_exists hMFZ (twinDExistsOn_of_small hMFZ hS)

end CFSG.ClassicalInvolution.RouteD.TwinY
