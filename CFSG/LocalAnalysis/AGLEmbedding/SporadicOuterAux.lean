module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.Schreier.PairHSOut
public import CFSG.Sporadic.Schreier.PairMcLOut
public import CFSG.Sporadic.Schreier.PairHePairs
public import CFSG.Sporadic.Schreier.RuAutInner
public import CFSG.Sporadic.SuzOddCore.Outer
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartOne.KP.SporadicRankFi22
public import CFSG.Sporadic.FischerOddCore.Fi23Aut
public import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartOne.SPOR.OuterB
public import CFSG.RankThree.PartOne.SPOR.OuterM
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem card_outer_dvd_two_of_le_two {G : Type*} [Group G] [Finite G]
    (h : Nat.card (Outer G) ≤ 2) : Nat.card (Outer G) ∣ 2 := by
  have h0 : 0 < Nat.card (Outer G) := Nat.card_pos
  obtain h1 | h2 : Nat.card (Outer G) = 1 ∨ Nat.card (Outer G) = 2 := by omega
  · rw [h1]
    exact one_dvd 2
  · rw [h2]

theorem card_outer_dvd_two_of_eq {G : Type*} [Group G]
    (h : Nat.card (Outer G) = 1 ∨ Nat.card (Outer G) = 2) : Nat.card (Outer G) ∣ 2 := by
  rcases h with h | h <;> rw [h]
  exact one_dvd 2

theorem not_dvd_card_outer_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Nat.card (Outer G) ∣ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (Outer H) := by
  rw [← Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hd.trans h))


theorem card_outer_carrier_dvd_two (hM : IsSimpleGroup CFSG.Open.MonsterY443Derived)
    (s : TauCeti.SporadicName) : Nat.card (Outer (NativeSporadic.Carrier s)) ∣ 2 := by
  cases s with
  | M11 =>
    exact card_outer_dvd_two_of_le_two (G := NativeSporadic.M11)
      CFSG.Sporadic.Schreier.at_m11_schreier.1
  | M12 =>
    exact card_outer_dvd_two_of_eq (G := NativeSporadic.M12)
      (.inr CFSG.ComponentClassification.M12Cover.card_outer)
  | M22 =>
    exact card_outer_dvd_two_of_eq (G := NativeSporadic.M22)
      (.inr CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.2.1)
  | M23 =>
    exact card_outer_dvd_two_of_le_two (G := NativeSporadic.M23)
      CFSG.Sporadic.Schreier.at_m23_schreier.1
  | M24 => exact card_outer_dvd_two_of_eq (G := NativeSporadic.M24) (.inl card_outer_M24)
  | J1 =>
    exact card_outer_dvd_two_of_eq (G := NativeSporadic.J1)
      (.inl CFSG.Sporadic.Schreier.at_j1_schreier.1)
  | J2 =>
    exact card_outer_dvd_two_of_le_two (G := NativeSporadic.J2)
      CFSG.Sporadic.Schreier.AT_J2_Schreier.1
  | J3 =>
    exact card_outer_dvd_two_of_le_two (G := NativeSporadic.J3)
      (CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.j3_outer_card_le
        CFSG.Sporadic.Schreier.j3PermEquiv)
  | J4 => exact card_outer_dvd_two_of_eq (.inl card_outer_J4)
  | HS =>
    exact card_outer_dvd_two_of_le_two (G := NativeSporadic.HS)
      CFSG.Sporadic.Schreier.HS_outer_card_le_two.1
  | McL =>
    exact card_outer_dvd_two_of_le_two (G := NativeSporadic.McL)
      CFSG.Sporadic.Schreier.McL_outer_card_le_two.1
  | He =>
    exact card_outer_dvd_two_of_le_two (G := NativeSporadic.He)
      CFSG.Sporadic.Schreier.AT_He_Schreier.1
  | Ru =>
    exact card_outer_dvd_two_of_le_two (G := NativeSporadic.Ru)
      (CFSG.Sporadic.Schreier.outer_card_le_of_equiv
        (CFSG.Sporadic.RuSchreier.card_outer_ruP.trans_le (by norm_num))
        CFSG.Sporadic.RuSchreier.ruEquivP)
  | Suz => exact card_outer_dvd_two_of_eq (.inr CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1)
  | ONan =>
    exact CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two
      ⟨(MulEquiv.refl _ : NativeSporadic.Carrier .ONan ≃* NativeSporadic.ON)⟩
  | Co1 => exact card_outer_dvd_two_of_eq (.inl CFSG.RankThree.PartOne.SPOR.card_outer_Co1)
  | Co2 => exact card_outer_dvd_two_of_eq (.inl CFSG.RankThree.PartOne.SPOR.card_outer_Co2)
  | Co3 =>
    exact card_outer_dvd_two_of_eq (G := NativeSporadic.Co3)
      (.inl CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1)
  | Fi22 =>
    exact card_outer_dvd_two_of_eq (G := NativeSporadic.Fi22)
      (.inr CFSG.RankThree.PartOne.card_outer_fi22_carrier)
  | Fi23 =>
    exact card_outer_dvd_two_of_eq (G := NativeSporadic.Fi23)
      (.inl CFSG.Sporadic.FischerOddCore.card_outer_fi23)
  | Fi24Prime =>
    exact card_outer_dvd_two_of_eq (G := NativeSporadic.Fi24prime)
      (.inr CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime)
  | HN => exact card_outer_dvd_two_of_eq (.inr CFSG.RankThree.PartOne.SPOR.card_outer_HN)
  | Ly => exact card_outer_dvd_two_of_eq CFSG.RankThree.PartOne.SPOR.card_outer_Ly
  | Th => exact card_outer_dvd_two_of_eq (.inl CFSG.RankThree.PartOne.SPOR.card_outer_Th)
  | B => exact card_outer_dvd_two_of_eq (.inl CFSG.RankThree.PartOne.SPOR.card_outer_B)
  | M =>
    have : IsSimpleGroup (NativeSporadic.Carrier .M) :=
      CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.isSimpleGroup
    exact card_outer_dvd_two_of_eq
      (.inl (CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple (MulEquiv.refl _)))

theorem not_dvd_card_outer_sporadic_of
    (hbr : ∀ s : TauCeti.SporadicName,
      Nonempty (Blueprint.NativeSporadic.Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hM : IsSimpleGroup CFSG.Open.MonsterY443Derived) :
    ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (TauCeti.CFSGIndex.sporadic s).Group) := fun s _ hp hp2 =>
  (hbr s).elim fun e => not_dvd_card_outer_of_mulEquiv e (card_outer_carrier_dvd_two hM s) hp hp2

end CFSG.AGLEmbedding
