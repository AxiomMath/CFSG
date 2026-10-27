module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSpMult
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.GH74.Generic.GKFSporadic
public import CFSG.Sporadic.Recognition.HeMultiplierCert
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerCase

public section

namespace CFSG.ComponentClassification.GSThmB.Cov

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.CatFactsL4U4

variable {H : Type} [Group H] [Finite H]

theorem eq_bot_of_isPGroup_two_of_odd {G : Type*} [Group G] [Finite G] {Z : Subgroup G}
    (hZ2 : IsPGroup 2 Z) (hodd : Odd (Nat.card Z)) : Z = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  rcases n with _ | n
  · rw [pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  · rw [hn, pow_succ] at hodd
    exact absurd (even_two.mul_left _) (Nat.not_even_iff_odd.mpr hodd)

theorem isPGroup_two_center_oddBar (K : Subgroup H) : IsPGroup 2 (center (OddBar K)) :=
  isPGroup_two_center_of_pPrimeCore_eq_bot (pPrimeCore_quotient_pPrimeCore_eq_bot 2)

theorem center_eq_bot_of_noTwoCover (h : Hyp52 H)
    (hN : GH74.Generic.NoTwoCover (ZStarBar h.K)) : center (OddBar h.K) = ⊥ := by
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  exact hN (OddBar h.K) h.isQuasisimple_K (isPGroup_two_center_oddBar h.K) ⟨eZ⟩

theorem center_eq_bot_of_odd_table (hGA : TBLit.GriessMultipliersAllModels) (h : Hyp52 H)
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (hn : n ≠ 0)
    (hm : Blueprint.LieModel (ZStarBar h.K) t n p f)
    (h1 : Odd (Blueprint.Multiplier.genericOrders t n p f).1)
    (h2 : Odd (Blueprint.Multiplier.genericOrders t n p f).2)
    (h3 : Odd (Blueprint.Multiplier.exceptionalOrders t n p f).1)
    (h4 : Odd (Blueprint.Multiplier.exceptionalOrders t n p f).2) :
    center (OddBar h.K) = ⊥ :=
  center_eq_bot_of_noTwoCover h (GH74.Generic.noTwoCover_of_griess hGA
    (GH74.Generic.models_of_blueprint_of_ne_zero hn hm) h1 h2 h3 h4)

theorem center_eq_bot_of_psl_three (hGKF : GH74.Generic.GenericKnownFacts) (h : Hyp52 H)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : Blueprint.LieModel (ZStarBar h.K) .PSL 3 p f) :
    center (OddBar h.K) = ⊥ :=
  center_eq_bot_of_noTwoCover h (hGKF.noTwoCover_psl3 p f hp hp2 _ hm)

theorem center_eq_bot_of_psu_three (hGKF : GH74.Generic.GenericKnownFacts) (h : Hyp52 H)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : Blueprint.LieModel (ZStarBar h.K) .PSU 3 p f) :
    center (OddBar h.K) = ⊥ :=
  center_eq_bot_of_noTwoCover h (hGKF.noTwoCover_psu3 p f hp hp2 _ hm)

theorem center_eq_bot_of_ree (hGKF : GH74.Generic.GenericKnownFacts) (h : Hyp52 H) {f : ℕ}
    (hm : Blueprint.LieModel (ZStarBar h.K) .twistedG2 0 3 f) : center (OddBar h.K) = ⊥ :=
  center_eq_bot_of_noTwoCover h (hGKF.noTwoCover_ree f _ hm)

theorem center_eq_bot_of_j1 (h : Hyp52 H)
    (hS : Blueprint.NativeSporadic.IsSporadic (ZStarBar h.K) .J1) : center (OddBar h.K) = ⊥ :=
  center_eq_bot_of_noTwoCover h (GH74.Generic.noTwoCover_J1_of_walter _ hS)

theorem center_eq_bot_of_he
    (h : Hyp52 H) (hS : Blueprint.NativeSporadic.IsSporadic (ZStarBar h.K) .He) :
    center (OddBar h.K) = ⊥ := by
  obtain ⟨e⟩ := hS
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  exact Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate (OddBar h.K)
    h.isQuasisimple_K ⟨eZ.trans e⟩

theorem center_eq_bot_of_j3 (hSM : SporadicMultTwoPartInput) (h : Hyp52 H)
    (hS : Blueprint.NativeSporadic.IsSporadic (ZStarBar h.K) .J3) : center (OddBar h.K) = ⊥ := by
  obtain ⟨e⟩ := hS
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  exact eq_bot_of_isPGroup_two_of_odd (isPGroup_two_center_oddBar h.K)
    (hSM.1 (OddBar h.K) h.isQuasisimple_K ⟨eZ.trans e⟩)

theorem center_eq_bot_of_on (hSM : SporadicMultTwoPartInput) (h : Hyp52 H)
    (hS : Blueprint.NativeSporadic.IsSporadic (ZStarBar h.K) .ONan) :
    center (OddBar h.K) = ⊥ := by
  obtain ⟨e⟩ := hS
  obtain ⟨eZ⟩ := nonempty_quotient_center_equiv_zStarBar h.K
  exact eq_bot_of_isPGroup_two_of_odd (isPGroup_two_center_oddBar h.K)
    (hSM.2 (OddBar h.K) h.isQuasisimple_K ⟨eZ.trans e⟩)

end CFSG.ComponentClassification.GSThmB.Cov
