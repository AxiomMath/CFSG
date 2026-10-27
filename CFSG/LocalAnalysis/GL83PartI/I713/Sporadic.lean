module

public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
import CFSG.Sporadic.Schreier.PairMcLOut
import CFSG.Sporadic.Schreier.RuAutInner
import CFSG.Sporadic.Schreier.Co1CatalogSchreier
import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
import CFSG.Sporadic.Co2Schreier.Model
import CFSG.Sporadic.FischerOddCore.Fi23Aut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
import CFSG.RankThree.PartOne.KP.Co3Aut
import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.RuDefs

public section

namespace GL83.I713

open CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem outClauseFor_of_card_outer_le_six {K : Type*} [Group K] [Finite K]
    (h : Nat.card (Outer K) ≤ 6) : OutClauseFor K := by
  intro p hp hp2 _
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  refine pRank_top_le_one_of_card_lt hp (lt_of_le_of_lt h ?_)
  nlinarith

theorem not_dvd_card_outer_of_isPGroup_two {K : Type*} [Group K] [Finite K]
    (h : IsPGroup 2 (Outer K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h
  rw [hk]
  intro hpO
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hpO))

theorem outClauseFor_sporadic_M11
    [Finite (NativeSporadic.Carrier .M11)] :
    OutClauseFor (NativeSporadic.Carrier .M11) :=
  outClauseFor_of_card_outer_le_four (Sporadic.Schreier.at_m11_schreier.1.trans (by norm_num))

theorem outClauseFor_sporadic_M12
    [Finite (NativeSporadic.Carrier .M12)] :
    OutClauseFor (NativeSporadic.Carrier .M12) :=
  outClauseFor_of_card_outer_le_four Sporadic.Schreier.at_m12_schreier.1

theorem outClauseFor_sporadic_M22
    [Finite (NativeSporadic.Carrier .M22)] :
    OutClauseFor (NativeSporadic.Carrier .M22) :=
  outClauseFor_of_card_outer_le_four Sporadic.Schreier.at_m22_schreier.1

theorem outClauseFor_sporadic_M23
    [Finite (NativeSporadic.Carrier .M23)] :
    OutClauseFor (NativeSporadic.Carrier .M23) :=
  outClauseFor_of_card_outer_le_four (Sporadic.Schreier.at_m23_schreier.1.trans (by norm_num))

theorem outClauseFor_sporadic_M24
    [Finite (NativeSporadic.Carrier .M24)] :
    OutClauseFor (NativeSporadic.Carrier .M24) :=
  outClauseFor_of_card_outer_le_four Sporadic.Schreier.at_m24_schreier.1

theorem outClauseFor_sporadic_J1
    [Finite (NativeSporadic.Carrier .J1)] :
    OutClauseFor (NativeSporadic.Carrier .J1) :=
  outClauseFor_of_card_outer_le_four
    (Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num))

theorem outClauseFor_sporadic_J2
    [Finite (NativeSporadic.Carrier .J2)] :
    OutClauseFor (NativeSporadic.Carrier .J2) :=
  outClauseFor_of_card_outer_le_four
    (Sporadic.Schreier.AT_J2_Schreier.1.trans (by norm_num))

theorem outClauseFor_sporadic_J3
    [Finite (NativeSporadic.Carrier .J3)] :
    OutClauseFor (NativeSporadic.Carrier .J3) :=
  outClauseFor_of_card_outer_le_six Sporadic.Schreier.AT_J3_Schreier.1

theorem outClauseFor_sporadic_HS
    [Finite (NativeSporadic.Carrier .HS)] :
    OutClauseFor (NativeSporadic.Carrier .HS) :=
  outClauseFor_of_card_outer_le_four
    (CFSG.RankThree.PartOne.SPOR.sporadicHS_outer_le_two.trans (by norm_num))

theorem outClauseFor_sporadic_McL
    [Finite (NativeSporadic.Carrier .McL)] :
    OutClauseFor (NativeSporadic.Carrier .McL) :=
  outClauseFor_of_card_outer_le_four
    (Sporadic.Schreier.McL_outer_card_le_two.1.trans (by norm_num))

theorem outClauseFor_sporadic_He
    [Finite (NativeSporadic.Carrier .He)] :
    OutClauseFor (NativeSporadic.Carrier .He) :=
  outClauseFor_of_card_outer_le_four
    (Sporadic.Schreier.AT_He_Schreier.1.trans (by norm_num))

theorem outClauseFor_sporadic_Ru
    [Finite (NativeSporadic.Carrier .Ru)] :
    OutClauseFor (NativeSporadic.Carrier .Ru) := by
  have h : Nat.card (Outer (NativeSporadic.Carrier .Ru)) ≤ 2 := by
    rw [show Nat.card (Outer (NativeSporadic.Carrier .Ru)) =
        Nat.card (Outer Sporadic.RuSchreier.ruP) from
      CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv
        Sporadic.RuSchreier.ruEquivP,
      Sporadic.RuSchreier.card_outer_ruP]
    norm_num
  exact outClauseFor_of_card_outer_le_four (h.trans (by norm_num))

theorem outClauseFor_sporadic_Suz
    [Finite (NativeSporadic.Carrier .Suz)] :
    OutClauseFor (NativeSporadic.Carrier .Suz) :=
  outClauseFor_of_card_outer_le_four
    (Sporadic.SuzOddCore.outer_carrier_suz.1.le.trans (by norm_num))

theorem outClauseFor_sporadic_Co1
    [Finite (NativeSporadic.Carrier .Co1)] :
    OutClauseFor (NativeSporadic.Carrier .Co1) := by
  have h := (Sporadic.Co1Schreier.catalog_schreier_of_inputs.{0}
    fun K _ e => Sporadic.Co2Schreier.AT_Co2_model_Schreier K e).2.2.1
  exact outClauseFor_of_not_dvd fun _ hp hp2 _ =>
    not_dvd_card_outer_of_isPGroup_two (K := NativeSporadic.Carrier .Co1) h hp hp2

theorem outClauseFor_sporadic_Co2
    [Finite (NativeSporadic.Carrier .Co2)] :
    OutClauseFor (NativeSporadic.Carrier .Co2) := by
  obtain ⟨e⟩ : Nonempty (NativeSporadic.Carrier .Co2 ≃* NativeSporadic.Co2) :=
    ⟨MulEquiv.refl _⟩
  have h := (Sporadic.Co2Schreier.AT_Co2_model_Schreier _ e).2.1
  exact outClauseFor_of_not_dvd fun _ hp hp2 _ =>
    not_dvd_card_outer_of_isPGroup_two (K := NativeSporadic.Carrier .Co2) h hp hp2

theorem outClauseFor_sporadic_Co3
    [Finite (NativeSporadic.Carrier .Co3)] :
    OutClauseFor (NativeSporadic.Carrier .Co3) := by
  have h : Nat.card (Outer NativeSporadic.Co3) = 1 :=
    CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1
  exact outClauseFor_of_card_outer_le_four (h.le.trans (by norm_num))

theorem outClauseFor_sporadic_Fi22
    [Finite (NativeSporadic.Carrier .Fi22)] :
    OutClauseFor (NativeSporadic.Carrier .Fi22) :=
  outClauseFor_of_card_outer_le_four
    (ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22.le.trans (by norm_num))

theorem outClauseFor_sporadic_Fi23
    [Finite (NativeSporadic.Carrier .Fi23)] :
    OutClauseFor (NativeSporadic.Carrier .Fi23) :=
  outClauseFor_of_card_outer_le_four
    (Sporadic.FischerOddCore.card_outer_fi23.le.trans (by norm_num))

theorem outClauseFor_sporadic_Fi24Prime
    [Finite (NativeSporadic.Carrier .Fi24Prime)] :
    OutClauseFor (NativeSporadic.Carrier .Fi24Prime) :=
  outClauseFor_of_card_outer_le_four
    (Sporadic.Schreier.Fi24.card_outer_fi24prime.le.trans (by norm_num))

theorem outClauseFor_sporadic_HN
    [Finite (NativeSporadic.Carrier .HN)] :
    OutClauseFor (NativeSporadic.Carrier .HN) :=
  outClauseFor_of_card_outer_le_four
    (CFSG.RankThree.PartOne.SPOR.card_outer_HN.le.trans (by norm_num))

theorem outClauseFor_sporadic_Ly
    [Finite (NativeSporadic.Carrier .Ly)] :
    OutClauseFor (NativeSporadic.Carrier .Ly) := by
  rcases CFSG.RankThree.PartOne.SPOR.card_outer_Ly with h | h <;>
    exact outClauseFor_of_card_outer_le_four (h.le.trans (by norm_num))

theorem outClauseFor_sporadic_Th
    [Finite (NativeSporadic.Carrier .Th)] :
    OutClauseFor (NativeSporadic.Carrier .Th) :=
  outClauseFor_of_card_outer_le_four
    (CFSG.RankThree.PartOne.SPOR.card_outer_Th.le.trans (by norm_num))

theorem outClauseFor_sporadic_B
    [Finite (NativeSporadic.Carrier .B)] :
    OutClauseFor (NativeSporadic.Carrier .B) :=
  outClauseFor_of_card_outer_le_four
    (CFSG.RankThree.PartOne.SPOR.card_outer_B.le.trans (by norm_num))

theorem outClauseFor_sporadic_M
    [Finite (NativeSporadic.Carrier .M)] [IsSimpleGroup (NativeSporadic.Carrier .M)] :
    OutClauseFor (NativeSporadic.Carrier .M) :=
  outClauseFor_of_card_outer_le_four
    ((CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple (MulEquiv.refl _)).le.trans
      (by norm_num))

end GL83.I713
