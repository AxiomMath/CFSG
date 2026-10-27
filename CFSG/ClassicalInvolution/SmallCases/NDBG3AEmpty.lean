module

public import CFSG.ClassicalInvolution.SmallCases.NDBG3Nine
public import CFSG.ClassicalInvolution.SmallCases.NDBG2
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.ClassicalInvolution.Asc77.AscAETWeak
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7c
public import CFSG.ClassicalInvolution.AschTight.Sec7L713E

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.AS76b (Asc75Theorem4)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]


theorem NDBG3.aEmpty_of_exact (h4 : Asc75Theorem4) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hex : ExactMembers (𝒞 K))
    (hL : (omegaOfSet (𝒞 K) (twinSet (𝒞 K) K)).Nonempty) : ∀ M ∈ 𝒞 K, AEmpty (𝒞 K) M := by
  have hΩ : HypOmegaMod p f (𝒞 K) := Cover.hypOmegaMod hnab hp2 hq hz hBelow
  have hK : K ∈ 𝒞 K := mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have htrans : ∀ J ∈ 𝒞 K, ∃ g : G, conjSub g K = J := by
    rintro J ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hA : AEmpty (𝒞 K) K := by
    by_contra hn
    obtain ⟨J, zK, zJ, hv⟩ := T3.not_aEmpty_iff.mp hn
    have hzK : zK = z := hv.hzK.eq hKz
    subst hzK
    obtain ⟨L, hLs⟩ := hL
    obtain ⟨l, hl⟩ := hΩ.classical L hLs.1
    have hlU : IsUniqueInvolution L l :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hl
    have hne : T3.aStar (𝒞 K) K ≠ 𝒞 K :=
      NDBG.aStar_ne_of_mem_omegaOfSet hp2 hq hΩ hK
        (fun M hM _ _ _ hvM => NDBG3.omegaOfSet_subset_of_exact hp2 hq hΩ hex hM hvM) hLs hlU
    exact T3Core.caseI_false hp2 hq h4 hnab hΩ hK hv htrans hBelow hne
  exact T3.aEmpty_forall_of_transitive' hΩ.conjInvariant htrans hA

theorem NDBG3.false_of_g2_of_exact (h4 : Asc75Theorem4) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hex : ExactMembers (𝒞 K))
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z) {b : Fin D.card} (hG2 : D.tag b = .G2)
    (hcard : 3 ≤ D.card) : False := by
  let C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have hb : ¬ (C.D.tag b = .PSL ∧ C.D.rank b = 2) := by
    rw [show C.D.tag b = .G2 from hG2]
    exact fun h => absurd h.1 (by decide)
  obtain ⟨N, hN, n, hn, hnz⟩ := NDBG.exists_far_member (C := C) hno hb
  have hNs : N ∈ omegaOfSet (𝒞 K) (twinSet (𝒞 K) K) :=
    NDBG.mem_omegaOfSet_of_tq hp2 hq C.hΩ (mem_conjClass_self K) C.hKz hN hn hnz
  have hA := NDBG3.aEmpty_of_exact h4 hnab hp2 hq hz hBelow hex ⟨N, hNs⟩
  exact BSC.BSE.false_of_g2_of_aEmpty (C := C) hno (b := b) hG2 hcard hA

end CFSG.ClassicalInvolution.NDB
