module

public import CFSG.LocalAnalysis.EvenSporadicStandard.LyStd.Ly
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fours
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Assembly.OddCoreBalance
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.EvenSporadicStandard.LyStd

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.EvenSporadicStandard.HypOne

theorem noNormalFour_of_isQuasisimple_center_two {C : Type} [Group C] [Finite C]
    (hq : IsQuasisimple C) (hc : Nat.card (center C) = 2) :
    CFSG.ComponentClassification.M12Cover.NoNormalFour C := by
  intro N hN
  have key : ∀ (A : Type) [CommGroup A], N ≃* A → 2 < Nat.card A → False := by
    intro A _ e hA
    rcases LocalCores.quasisimple_normal_subgroups hq hN with hN1 | hN1
    · obtain ⟨a, b, hab⟩ := hq.2.2
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have hx : x ∈ N := by rw [hN1]; exact mem_top x
      have hy : y ∈ N := by rw [hN1]; exact mem_top y
      have hcomm : x * y = y * x := by
        have := e.injective (show e (⟨x, hx⟩ * ⟨y, hy⟩) = e (⟨y, hy⟩ * ⟨x, hx⟩) by
          rw [map_mul, map_mul, mul_comm])
        exact congrArg Subtype.val this
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
    · have h1 := Subgroup.card_le_of_le hN1
      rw [hc, Nat.card_congr e.toEquiv] at h1
      omega
  refine ⟨⟨fun e => key (Multiplicative (ZMod 4)) e ?_⟩, ⟨fun e => key _ e ?_⟩⟩
  · simp [Nat.card_eq_fintype_card]
  · simp [Nat.card_eq_fintype_card]

theorem smallNormalFree_of_isDoubleCoverOfAlt {C : Type} [Group C] [Finite C] {n : ℕ}
    (h : IsDoubleCoverOfAlt C n) : SmallNormalFree C := by
  have hO : CFSG.Assembly.oddCore C = ⊥ := by
    rw [CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
    exact CFSG.OddStandard.Solomon75.pPrimeCore_eq_bot_of_doubleCover h
  exact SmallNormalFree.of_noNormalFour hO (noNormalFour_of_isQuasisimple_center_two h.1 h.2.1)

theorem center_eq_bot_ly : center NativeSporadic.Ly = ⊥ := by
  obtain ⟨hfin, -, hsimple⟩ := CFSG.Sporadic.Ly.fam_ly_simplicity
  refine center_eq_bot_of_isSimpleGroup fun hp => ?_
  have h2 := hp.eq_one_or_self_of_dvd 2 (by rw [CFSG.Sporadic.Ly.card_Ly]; norm_num)
  rw [CFSG.Sporadic.Ly.card_Ly] at h2
  omega

theorem hypothesisOne_native :
    HypothesisOne NativeSporadic.Ly := by
  have hc := center_eq_bot_ly
  have : Finite NativeSporadic.Ly := (CFSG.Sporadic.Ly.fam_ly_simplicity).1
  have htop := ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput
  refine hypothesisOne_of_inner (conj_injective_of_center_eq_bot hc) (fun α => ?_) fun y hy => ?_
  · have : α ∈ ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Ly := by
      rw [htop]; trivial
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg.symm⟩
  · exact smallNormalFree_of_isDoubleCoverOfAlt (isDoubleCoverOfAlt_ly ⟨MulEquiv.refl _⟩ hy)

theorem allInner_of_isSporadic_ly
    {Y : Type} [Group Y]
    (h : IsSporadic Y .Ly) : ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.Ly := e₀
  have htop := ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput
  have key : ∀ α : MulAut NativeSporadic.Ly, ∃ g : NativeSporadic.Ly, α = MulAut.conj g := by
    intro α
    have : α ∈ ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Ly := by
      rw [htop]; trivial
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg.symm⟩
  exact forall_eq_conj_of_mulEquiv (X := NativeSporadic.Ly) (Y := Y) e.symm key

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem center_eq_bot_of_isSporadic_ly {Y : Type} [Group Y]
    (h : IsSporadic Y .Ly) : center Y = ⊥ := by
  obtain ⟨e₀⟩ := h
  have e : Y ≃* NativeSporadic.Ly := e₀
  have hc := center_eq_bot_ly
  refine eq_bot_iff.2 fun z hz => ?_
  have hz' : e z ∈ center NativeSporadic.Ly := by
    rw [mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, mem_center_iff.1 hz g]
  rw [hc, mem_bot] at hz'
  exact mem_bot.2 (e.injective (by rw [hz', map_one]))

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.card_sylow_eq_two_ly
    (h : StdHyp G L) (hL : IsSporadic L .Ly)
    (S : Sylow 2 (centralizer (L : Set G))) : Nat.card S = 2 := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_ly hL
  have hLq : IsSporadic (L ⧸ center L) .Ly := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hI : HypothesisOne (L ⧸ center L) := by
    obtain ⟨φ⟩ := hLq
    exact CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv φ.symm hypothesisOne_native
  exact h.card_sylow_eq_two_of_inner hI (allInner_of_isSporadic_ly hLq) S

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.centralizer_eq_prod_ly
    (h : StdHyp G L) (hL : IsSporadic L .Ly) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) = L ⊔ zpowers t ∧ Disjoint L (zpowers t) ∧
      zpowers t ≤ centralizer (L : Set G) := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_ly hL
  have hLq : IsSporadic (L ⧸ center L) .Ly := by
    obtain ⟨e⟩ := hL
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  exact h.centralizer_eq_prod_of_center_eq_bot (h.card_sylow_eq_two_ly hL) ht ht2
    (h.centralizer_le_sup_centralizer_of_inner ht ht2 (allInner_of_isSporadic_ly hLq)) hZ

end CFSG.EvenSporadicStandard.LyStd
