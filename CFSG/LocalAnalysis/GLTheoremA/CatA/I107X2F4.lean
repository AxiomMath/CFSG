module

public import CFSG.GH74.Filter.Lie.SepWitness
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LCore
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X2

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly CFSG.GH74.Filter.Lie
open CFSG.LieType.Chevalley


@[expose] def f4Seven : SepWitness Tag.F4 7 where
  word := ![([] : List (Fin 4)), ([1] : List (Fin 4)), ([1] : List (Fin 4)), ([3, 1] : List (Fin 4)),
    ([1, 2, 1] : List (Fin 4)), ([3, 1, 2, 1] : List (Fin 4)), ([0, 1, 2, 3, 1, 2, 1] : List (Fin 4))]
  simple := ![(1 : Fin 4), (2 : Fin 4), (0 : Fin 4), (2 : Fin 4), (0 : Fin 4), (0 : Fin 4), (0 : Fin 4)]
  sep := ![([1] : List (Fin 4)), ([2, 1, 2] : List (Fin 4)), ([1, 0] : List (Fin 4)),
    ([2, 1, 2, 3] : List (Fin 4)), ([1, 2, 0, 1, 2, 0] : List (Fin 4)),
    ([1, 2, 0, 1, 2, 3, 0] : List (Fin 4)), ([1, 2, 0, 1, 2, 3, 2, 1, 2, 0] : List (Fin 4))]

theorem f4Seven_check : f4Seven.check = true := by decide +kernel

theorem charP_two_of_card' {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hc, m, hp, hcard⟩ := FiniteField.card' K
  rw [← Nat.card_eq_fintype_card, hK] at hcard
  have hdvd : p ∣ 2 ^ n := by
    rw [hcard]
    exact dvd_pow_self p m.ne_zero
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hc

theorem f4Seven_pRank {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    7 * n ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (adjointGroup Tag.F4 K)) := by
  haveI : CharP K 2 := charP_two_of_card' hK
  exact SepWitness.le_pRank (p := 2) f4Seven_check hK

theorem twoRankLow_F4_holds (S : Type) [Group S] [Finite S] (lab : GLALabel) (hS : IsSimpleGroup S)
    (hrk : Rk2IsLabel S lab) (ht : lab.tag = .F4) :
    twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have hraw := rk2IsLabel_rawDatum hrk
  obtain ⟨tag, rank, n⟩ := lab
  obtain rfl : tag = .F4 := ht
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
  obtain ⟨-, hna, ⟨θ⟩⟩ := hQ
  have e0 : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false) ≃*
      AdjointQuotient Tag.F4 K :=
    (CFSG.StandardType.centerQuot_chevGroup_equiv K Tag.F4).some
  haveI : Finite (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)) :=
    Finite.of_equiv _ θ.toEquiv
  haveI : Finite (AdjointQuotient Tag.F4 K) := Finite.of_equiv _ e0.toEquiv
  haveI : Finite (adjointGroup Tag.F4 K) :=
    Finite.of_equiv _ (adjointQuotientEquiv Tag.F4 K).toEquiv
  rw [CFSG.LocalAnalysis.GLTheoremA.I107L.pRank_eq_of_quotient θ hna,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) e0,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 2) (adjointQuotientEquiv Tag.F4 K)]
  exact f4Seven_pRank hK

end CFSG.LocalAnalysis.GLTheoremA.I107X2

end
