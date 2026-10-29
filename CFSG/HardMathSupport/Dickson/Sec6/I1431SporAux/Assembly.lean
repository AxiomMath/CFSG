module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Spor
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Final
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.RuNo65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.SuzNo65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi22No65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThNo65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi23No65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi24No65
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.ThNo186
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.LyNo186
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Co1
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsCert
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders
public import CFSG.Open.MonsterY443Finiteness
public import CFSG.Sporadic.Bridge.Converse
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem exists_not_comm_of_simple_not_prime {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  letI : CommGroup G := { ‹Group G› with mul_comm := fun a b => hcomm a b }
  exact h IsSimpleGroup.prime_card

theorem center_eq_bot_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
  · exact h0
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have ha : a ∈ Subgroup.center G := by rw [h0]; trivial
    exact ((Subgroup.mem_center_iff.1 ha) b).symm

theorem exists_conj_of_pow_three {G : Type*} [Group G] [Finite G] (hO : Nat.card (Outer G) ≤ 2)
    {ψ : MulAut G} (h3 : ψ ^ 3 = 1) : ∃ x : G, MulAut.conj x = ψ := by
  have hfin : Finite (MulAut G) := MulEquiv.finite_left
  have hpos : 0 < Nat.card (Outer G) := Nat.card_pos
  have h1 : (QuotientGroup.mk ψ : Outer G) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
  have h3' : orderOf (QuotientGroup.mk ψ : Outer G) ∣ 3 := orderOf_dvd_of_pow_eq_one h1
  have hle : orderOf (QuotientGroup.mk ψ : Outer G) ≤ 2 :=
    (Nat.le_of_dvd hpos (orderOf_dvd_natCard _)).trans hO
  have h1' : orderOf (QuotientGroup.mk ψ : Outer G) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h3' with h | h
    · exact h
    · omega
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1'
  exact MonoidHom.mem_range.1 h1'

theorem sporL2Pair_four_cases {s : TauCeti.SporadicName} (h : SporL2Pair s 4) :
    s = .Ru ∨ s = .Suz ∨ s = .Co1 ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .Th ∨ s = .B ∨
      s = .M := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · omega

theorem sporL2Pair_five_cases {s : TauCeti.SporadicName} (h : SporL2Pair s 5) :
    s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M := by
  rcases h with ⟨h, -⟩ | ⟨-, h⟩
  · omega
  · exact h

theorem center_inner_of_pairFive {s : TauCeti.SporadicName} (hs : SporL2Pair s 5)
    (hOrd : Nat.card (NativeSporadic.Carrier s) = CFSG.AGLEmbedding.sporOrd s)
    (hFin : Finite (NativeSporadic.Carrier s)) (hSimple : IsSimpleGroup (NativeSporadic.Carrier s))
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) :
    Subgroup.center (NativeSporadic.Carrier s) = ⊥ ∧
      ∀ ψ : MulAut (NativeSporadic.Carrier s), ψ ^ 3 = 1 →
        ∃ x : NativeSporadic.Carrier s, MulAut.conj x = ψ := by
  have hcases := sporL2Pair_five_cases hs
  have hnp : ¬ (CFSG.AGLEmbedding.sporOrd s).Prime := by
    intro hp
    have h2 : 2 ∣ CFSG.AGLEmbedding.sporOrd s := by
      rcases hcases with rfl | rfl | rfl | rfl <;> decide +kernel
    have h3 : CFSG.AGLEmbedding.sporOrd s ≠ 2 := by
      rcases hcases with rfl | rfl | rfl | rfl <;> decide +kernel
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · omega
    · exact h3 h.symm
  have hnab : ∃ a b : NativeSporadic.Carrier s, a * b ≠ b * a :=
    exists_not_comm_of_simple_not_prime (by rw [hOrd]; exact hnp)
  refine ⟨center_eq_bot_of_simple_nonabelian hnab, fun ψ h3 => ?_⟩
  have h7 : s = .Co1 ∨ s = .Co2 ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M := by
    rcases hcases with h | h | h | h <;> simp [h]
  have hO := hOut s h7 (NativeSporadic.Carrier s) hnab ⟨MulEquiv.refl _⟩
  exact exists_conj_of_pow_three hO h3

section Core


theorem i1431SporRest_of_monster
    (hMcard : Nat.card CFSG.Open.MonsterY443Derived = CFSG.Open.monsterOrder)
    (hMsimple : IsSimpleGroup CFSG.Open.MonsterY443Derived)
    (hB65 : NoOrder 65 NativeSporadic.B) (hM65 : NoOrder 65 NativeSporadic.M)
    (hB186 : NoOrder 186 NativeSporadic.B) (hM186 : NoOrder 186 NativeSporadic.M) :
    I1431SporRest := by
  have hOrd := CFSG.AGLEmbedding.card_carrier_eq_sporOrd hMcard
  have hTits : ∀ (G : Type) [Group G] (p f : ℕ), ReeTitsModel G .Tits p f →
      Nat.card G = 17971200 := by
    intro G _ p f h
    obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv G p f h
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  have hFS := CFSG.Sporadic.Bridge.carrier_finite_simple hMcard hMsimple
  have hOut := CFSG.RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds
  refine i1431SporRest_of_surv hOrd hTits (i1431SporSurv_of_noOrders ?_ ?_ ?_ ?_)
  · intro s hs
    exact (center_inner_of_pairFive hs (hOrd s) (hFS s).1 (hFS s).2 hOut).1
  · intro s hs
    exact (center_inner_of_pairFive hs (hOrd s) (hFS s).1 (hFS s).2 hOut).2
  · intro s hs
    rcases sporL2Pair_four_cases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact noOrder65_Ru
    · exact noOrder65_Suz
    · exact noOrderSixtyFive_Co1
    · exact noOrder65_Fi22
    · exact noOrder65_Fi23
    · exact noOrder65_Fi24prime
    · exact noOrder65_Th
    · exact hB65
    · exact hM65
  · intro s hs
    rcases sporL2Pair_five_cases hs with rfl | rfl | rfl | rfl
    · exact noOrder186_Ly
    · exact noOrder186_Th
    · exact hB186
    · exact hM186

section Monster


theorem i1431SporRest_of_open
    (hB65 : NoOrder 65 NativeSporadic.B) (hM65 : NoOrder 65 NativeSporadic.M)
    (hB186 : NoOrder 186 NativeSporadic.B) (hM186 : NoOrder 186 NativeSporadic.M) :
    I1431SporRest :=
  i1431SporRest_of_monster CFSG.Open.Open.monster_y443_derived_card
    CFSG.Open.Open.monster_y443_derived_simple hB65 hM65 hB186 hM186

end Monster

end Core

end CFSG.HardMathSupport.Dickson.Sec6.I1431
