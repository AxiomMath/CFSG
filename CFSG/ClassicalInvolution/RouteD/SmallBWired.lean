module

public import CFSG.ClassicalInvolution.RouteD.SmallBFive
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
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
public import CFSG.ClassicalInvolution.Generic.InductionMain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Generic.CoreAssembly (conjClass single_class)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinBLastLongGe5 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z → ∀ (m : ℕ) (_ : 5 ≤ m)
      (_ : m ≠ 6), LocalShapeT p f 2 .POmegaOdd m (conjClass K) z →
      ∃ c : TCtx p f .POmegaOdd m (conjClass K) K z, ∀ β ∈ conjClass K, ∀ t : G,
        ∀ ht : IsClassicalMember p f β t,
          ∀ hKβ : (∃ W, LinearBlockStandardPair (GaloisField p f) W K β),
            HasFixedMember (conjClass K) K β z →
              ∀ (k₀ : (modelUniv .POmegaOdd m p f Fact.out).K)
                (v : Fin (modelUniv .POmegaOdd m p f Fact.out).D.rank → ZMod 2),
                Gaps.ToralPropB c (partner_involution_commutes c.hp2 c.hz ht hKβ) k₀ v →
                  Gaps.LastLongExcluded (p := p) (f := f) m v

@[expose] def TwinBSmallRest (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z → ∀ m : ℕ,
      (m = 3 ∨ m = 4 ∨ m = 6) → LocalShapeT p f 2 .POmegaOdd m (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (conjClass K) K β z → PartnerPatternBPair p f m (conjClass K) K β t

theorem twinBPattern_of_parts (hMFZ : Gaps.FundNoncentral p) (hL : TwinBLastLongGe5 p f)
    (hR : TwinBSmallRest p f) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z → ∀ m : ℕ, 3 ≤ m →
        LocalShapeT p f 2 .POmegaOdd m (conjClass K) z → ∀ β ∈ conjClass K, ∀ t : G,
          IsClassicalMember p f β t →
          (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
          HasFixedMember (conjClass K) K β z → PartnerPatternBPair p f m (conjClass K) K β t := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  by_cases hsmall : m = 3 ∨ m = 4 ∨ m = 6
  · exact hR G hnab K z S m hsmall hshape β hβ t ht hKβ hfix
  have h5 : 5 ≤ m := by omega
  have h6 : m ≠ 6 := fun h => hsmall (Or.inr (Or.inr h))
  obtain ⟨c, hc⟩ := hL G hnab K z S m h5 h6 hshape
  by_cases hm5 : m = 5
  · subst hm5
    exact Gaps.PartnerPatternBPair.of_fixed_member_five hMFZ c (single_class K) hshape hβ ht hKβ
      hfix (fun k₀ v hv => hc β hβ t ht hKβ hfix k₀ v hv)
  · exact Gaps.PartnerPatternBPair.of_fixed_member_seven (by omega) hMFZ c (single_class K) hshape
      hβ ht hKβ hfix (fun k₀ v hv => hc β hβ t ht hKβ hfix k₀ v hv)

end CFSG.ClassicalInvolution.RouteD
