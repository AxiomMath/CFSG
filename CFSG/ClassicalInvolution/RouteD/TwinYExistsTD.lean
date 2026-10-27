module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallMinusSix
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDChain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge
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
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal CFSG.LieType.Universal.Spin.Twisted

variable {p f : ℕ} [Fact p.Prime]

local notation "𝒞" => CoreAssembly.conjClass

@[expose] def TwinTDExistsOn (p f : ℕ) [Fact p.Prime] (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ∀ m : ℕ, P m →
      LocalShapeT p f 2 .POmegaMinus m (𝒞 K) z →
      ∃ β ∈ 𝒞 K, ∃ t : G, IsClassicalMember p f β t ∧
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
        PartnerPatternMinus p f m (𝒞 K) K β t

@[expose] def TwinTDExistsCase (p f m : ℕ) [Fact p.Prime] : Prop :=
  TwinTDExistsOn p f fun k => k = m

theorem TwinTDExistsOn.of_patternOn {P : ℕ → Prop} (hP : ∀ m, P m → 4 ≤ m)
    (h : Gaps.TwinTDPatternOn p f P) : TwinTDExistsOn p f P := by
  intro G _ _ _ hnab K z S m hm hshape
  have hm4 := hP m hm
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simpa using S.five
    · exact h
  have hadm : StatedLieAdmissible .POmegaMinus m p f := ⟨Fact.out, hf, by show 4 ≤ m; omega⟩
  obtain ⟨c⟩ := TCtx.nonempty_minus hm4 S.odd S.five S.inClass S.exact (mem_conjClass_self K)
    S.cls S.p1 hshape
  obtain ⟨β, hβ, ⟨t, ht⟩, hKβ, hfix⟩ := c.exists_partner_minus hm4 S.odd hadm (single_class K)
    hshape
  exact ⟨β, hβ, t, ht, hKβ, h G hnab K z S m hm hshape β hβ t ht hKβ hfix⟩

theorem twinTDExistsCase_of_case {m : ℕ} (hm : 4 ≤ m) (h : TwinTDCase p f m) :
    TwinTDExistsCase p f m :=
  TwinTDExistsOn.of_patternOn (fun k hk => by omega) h

theorem routeD_typeTwistedD_of_exists_pattern {G : Type} [Group G] [Finite G] (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hg6 : SpinMinus6Generated (minusCoeffs_irr p f))
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f)) {n : ℕ}
    (hn : 6 ≤ n) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeT p f 2 .POmegaMinus (n - 2) Ω z)
    (hP1 : LocalOddCentral Ω {z})
    (hpat : ∃ β ∈ Ω, ∃ t : G, IsClassicalMember p f β t ∧
      (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) ∧
      PartnerPatternMinus p f (n - 2) Ω K β t) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaMinus ∧ D.rank i = n := by
  obtain ⟨β, hβ, t, ht, hKβ, j, hjK, hjperf, -, hjt, hjc, hjp, hjtw, hβj⟩ := hpat
  exact routeD_typeTwistedD hp2 hq hn hg6 hMFZ hS3 hΩ hK hsingle hconn hz hshape hP1 hβ ht hKβ j
    hjK (fun a _ => hjperf a) hjt hjc hjp hjtw (hβj ⟨0, by omega⟩ rfl)

theorem rowTwinTD_of_exists (hMFZ : Gaps.FundNoncentral p)
    (h : TwinTDExistsOn p f fun m => 4 ≤ m) : RowPiece p f ShapeTwinTD := by
  intro a t n hshape G _ _ _ hnab K z S hS
  obtain ⟨rfl, rfl, hn⟩ := hshape
  have hn' : n + 2 - 2 = n := by omega
  have hS' : LocalShapeT p f 2 .POmegaMinus (n + 2 - 2) (𝒞 K) z := by rw [hn']; exact hS
  have hf : f ≠ 0 := by
    rintro rfl
    simpa using S.five
  have : NeZero f := ⟨hf⟩
  have hS3 : Gaps.StandardPairAutAbelian (GaloisField p f) :=
    Gaps.standardPairAutAbelian_galoisField S.odd S.five
  obtain ⟨β, hβ, t, ht, hKβ, hpat⟩ := h G hnab K z S n hn hS
  obtain ⟨D, -, -⟩ := routeD_typeTwistedD_of_exists_pattern S.odd S.five
    (spinMinus6Generated_galois S.odd) hMFZ hS3 (n := n + 2) (by omega) S.inClass
    (mem_conjClass_self K) (single_class K) S.conn S.cls hS' S.p1
    ⟨β, hβ, t, ht, hKβ, by rwa [hn']⟩
  exact ⟨D⟩

theorem twinTDPatternOn_six_up (hMFZ : Gaps.FundNoncentral p) :
    Gaps.TwinTDPatternOn p f fun m => 6 ≤ m := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  by_cases h8 : 8 ≤ m
  · obtain ⟨u, rfl⟩ : ∃ u, m = u + 3 + 5 := ⟨m - 8, by omega⟩
    obtain ⟨c⟩ := TCtx.nonempty_minus (by omega) S.odd S.five S.inClass S.exact
      (mem_conjClass_self K) S.cls S.p1 hshape
    exact Gaps.PartnerPatternMinus.of_fixed_member_ge3 hMFZ c (single_class K) hshape hβ ht hKβ
      hfix
  · rcases (by omega : m = 6 ∨ m = 7) with rfl | rfl
    · exact twinTDCase_six G hnab K z S 6 rfl hshape β hβ t ht hKβ hfix
    · exact twinTDCase_seven G hnab K z S 7 rfl hshape β hβ t ht hKβ hfix

theorem twinTDExistsOn_of_cases (hMFZ : Gaps.FundNoncentral p) (h4 : TwinTDExistsCase p f 4)
    (h5 : TwinTDExistsCase p f 5) : TwinTDExistsOn p f fun m => 4 ≤ m := by
  have h6 : TwinTDExistsOn p f fun m => 6 ≤ m :=
    TwinTDExistsOn.of_patternOn (fun m hm => by omega) (twinTDPatternOn_six_up hMFZ)
  intro G _ _ _ hnab K z S m hm hshape
  by_cases h : 6 ≤ m
  · exact h6 G hnab K z S m h hshape
  · rcases (by omega : m = 4 ∨ m = 5) with rfl | rfl
    · exact h4 G hnab K z S 4 rfl hshape
    · exact h5 G hnab K z S 5 rfl hshape

theorem rowTwinTD_of_exists_cases (hMFZ : Gaps.FundNoncentral p) (h4 : TwinTDExistsCase p f 4)
    (h5 : TwinTDExistsCase p f 5) : RowPiece p f ShapeTwinTD :=
  rowTwinTD_of_exists hMFZ (twinTDExistsOn_of_cases hMFZ h4 h5)

end CFSG.ClassicalInvolution.RouteD.TwinY
