module

public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.LocalAnalysis.AGLEmbedding.RankTools
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherRigidity
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LieType.OutStructure

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem pRank_add_one_le_pRank_of_centralizes {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E) {x : X}
    (hxord : orderOf x = p) (hdisj : E ⊓ Subgroup.zpowers x = ⊥)
    (hc : ∀ a ∈ E, a * x = x * a) {H : Subgroup X}
    (hEH : E ≤ H) (hxH : Subgroup.zpowers x ≤ H) :
    CFSG.Open.pRank p E + 1 ≤ CFSG.Open.pRank p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (hc a ha) n).eq
  have hAB : Nat.Coprime p (Nat.card (E ⊓ Subgroup.zpowers x : Subgroup X)) := by
    rw [hdisj]
    simp
  have hsum := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime hp hcomm hAB
  have hz : CFSG.Open.pRank p (Subgroup.zpowers x) = 1 := by
    have hzE : IsElemAbelian p (Subgroup.zpowers x) :=
      isElemAbelian_zpowers (by rw [← hxord]; exact pow_orderOf_eq_one x)
    have hcard := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hzE
    rw [Nat.card_zpowers, hxord] at hcard
    have hcard' : p ^ 1 = p ^ CFSG.Open.pRank p (Subgroup.zpowers x) := by
      rw [pow_one]
      exact hcard
    exact (Nat.pow_right_injective hp.two_le hcard').symm
  have hmono : CFSG.Open.pRank p (E ⊔ Subgroup.zpowers x) ≤ CFSG.Open.pRank p H :=
    CFSG.SectionRank.pRank_mono hp.one_lt (sup_le hEH hxH)
  omega

theorem pRank_lt_sup_zpowers_of_centralizes_maximal {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L : Subgroup X} {x : X} (hxord : orderOf x = p) (hxL : x ∉ L)
    {E : Subgroup X} (hEL : E ≤ L) (hE : IsElemAbelian p E)
    (hEmax : Nat.card E = p ^ CFSG.Open.pRank p L)
    (hc : ∀ a ∈ E, a * x = x * a) :
    CFSG.Open.pRank p L < CFSG.Open.pRank p (L ⊔ Subgroup.zpowers x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdisjL : Disjoint L (Subgroup.zpowers x) :=
    CFSG.RankThree.PartTwo.disjoint_zpowers_of_not_mem (q := p) hxL
      (by rw [← hxord]; exact pow_orderOf_eq_one x)
  have hdisj : E ⊓ Subgroup.zpowers x = ⊥ :=
    disjoint_iff.mp (hdisjL.mono_left hEL)
  have hErk : CFSG.Open.pRank p E = CFSG.Open.pRank p L := by
    have hcard := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hE
    rw [hEmax] at hcard
    exact (Nat.pow_right_injective hp.two_le hcard).symm
  have hEH : E ≤ L ⊔ Subgroup.zpowers x := hEL.trans le_sup_left
  have hxH : Subgroup.zpowers x ≤ L ⊔ Subgroup.zpowers x := le_sup_right
  have h1 := pRank_add_one_le_pRank_of_centralizes hp hE hxord hdisj hc hEH hxH
  rw [hErk] at h1
  omega

theorem three_le_pRank_of_centralizes_rank_two {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L : Subgroup X} {x : X} (hxord : orderOf x = p) (hxL : x ∉ L)
    {E : Subgroup X} (hEL : E ≤ L) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2)
    (hc : ∀ a ∈ E, a * x = x * a) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdisjL : Disjoint L (Subgroup.zpowers x) :=
    CFSG.RankThree.PartTwo.disjoint_zpowers_of_not_mem (q := p) hxL
      (by rw [← hxord]; exact pow_orderOf_eq_one x)
  have hdisj : E ⊓ Subgroup.zpowers x = ⊥ :=
    disjoint_iff.mp (hdisjL.mono_left hEL)
  have hErk : CFSG.Open.pRank p E = 2 := by
    have hcard := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hp hE
    rw [hEcard] at hcard
    exact (Nat.pow_right_injective hp.two_le hcard).symm
  have hle := pRank_add_one_le_pRank_of_centralizes (H := (⊤ : Subgroup X))
    hp hE hxord hdisj hc le_top le_top
  omega

theorem three_le_pRank_of_field_action_centralizes_maximal {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {L : Subgroup X} {x : X} (hxord : orderOf x = p) (hxL : x ∉ L)
    {E : Subgroup X} (hEL : E ≤ L) (hE : IsElemAbelian p E)
    (hEmax : Nat.card E = p ^ CFSG.Open.pRank p L)
    (hc : ∀ a ∈ E, a * x = x * a)
    (hL2 : 2 ≤ CFSG.Open.pRank p L) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hlt := pRank_lt_sup_zpowers_of_centralizes_maximal hp hxord hxL hEL hE hEmax hc
  have hmono := CFSG.SectionRank.pRank_mono hp.one_lt
    (le_top : L ⊔ Subgroup.zpowers x ≤ (⊤ : Subgroup X))
  omega

theorem three_le_pRank_of_centralizer_pElement {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L : Subgroup X} {c : X}
    (hc : c ∈ Subgroup.centralizer (L : Set X))
    (hcord : orderOf c = p) (hcL : c ∉ L)
    {E : Subgroup X} (hEL : E ≤ L) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  refine three_le_pRank_of_centralizes_rank_two hp hcord hcL hEL hE hEcard ?_
  intro a ha
  exact Subgroup.mem_centralizer_iff.mp hc a (hEL ha)

theorem three_le_pRank_of_linear_dichotomy {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) {L E : Subgroup X} (hEL : E ≤ L) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2)
    (h : (∃ c : X, c ∈ Subgroup.centralizer (L : Set X) ∧ orderOf c = p ∧ c ∉ L) ∨
      (∃ x : X, orderOf x = p ∧ x ∉ L ∧ ∀ a ∈ E, a * x = x * a)) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  rcases h with ⟨c, hc, hcord, hcL⟩ | ⟨x, hxord, hxL, hc⟩
  · exact three_le_pRank_of_centralizer_pElement hp hc hcord hcL hEL hE hEcard
  · exact three_le_pRank_of_centralizes_rank_two hp hxord hxL hEL hE hEcard hc

end CFSG.LieType.OutStructure
