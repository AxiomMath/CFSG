module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuterAux
import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem card_outer_native_dvd_two (s : TauCeti.SporadicName)
    (hM : s = .M → IsSimpleGroup (NativeSporadic.Carrier .M)) :
    Nat.card (Outer (NativeSporadic.Carrier s)) ∣ 2 := by
  cases s with
  | M11 =>
    exact AGLEmbedding.card_outer_dvd_two_of_le_two (G := NativeSporadic.M11)
      CFSG.Sporadic.Schreier.at_m11_schreier.1
  | M12 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (G := NativeSporadic.M12)
      (.inr CFSG.ComponentClassification.M12Cover.card_outer)
  | M22 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (G := NativeSporadic.M22)
      (.inr CFSG.Monster.B.TwoA.Fischer.catalog_M22_full_automorphism_order.2.1)
  | M23 =>
    exact AGLEmbedding.card_outer_dvd_two_of_le_two (G := NativeSporadic.M23)
      CFSG.Sporadic.Schreier.at_m23_schreier.1
  | M24 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (G := NativeSporadic.M24)
      (.inl AGLEmbedding.card_outer_M24)
  | J1 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (G := NativeSporadic.J1)
      (.inl CFSG.Sporadic.Schreier.at_j1_schreier.1)
  | J2 =>
    exact AGLEmbedding.card_outer_dvd_two_of_le_two (G := NativeSporadic.J2)
      CFSG.Sporadic.Schreier.AT_J2_Schreier.1
  | J3 =>
    exact AGLEmbedding.card_outer_dvd_two_of_le_two (G := NativeSporadic.J3)
      (CFSG.Sporadic.Schreier.outer_card_le_of_equiv CFSG.Sporadic.SmallOddCore.j3_outer_card_le
        CFSG.Sporadic.Schreier.j3PermEquiv)
  | J4 => exact AGLEmbedding.card_outer_dvd_two_of_eq (.inl AGLEmbedding.card_outer_J4)
  | HS =>
    exact AGLEmbedding.card_outer_dvd_two_of_le_two (G := NativeSporadic.HS)
      CFSG.Sporadic.Schreier.HS_outer_card_le_two.1
  | McL =>
    exact AGLEmbedding.card_outer_dvd_two_of_le_two (G := NativeSporadic.McL)
      CFSG.Sporadic.Schreier.McL_outer_card_le_two.1
  | He =>
    exact AGLEmbedding.card_outer_dvd_two_of_le_two (G := NativeSporadic.He)
      CFSG.Sporadic.Schreier.AT_He_Schreier.1
  | Ru =>
    exact AGLEmbedding.card_outer_dvd_two_of_le_two (G := NativeSporadic.Ru)
      (CFSG.Sporadic.Schreier.outer_card_le_of_equiv
        (CFSG.Sporadic.RuSchreier.card_outer_ruP.trans_le (by norm_num))
        CFSG.Sporadic.RuSchreier.ruEquivP)
  | Suz =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (.inr CFSG.Sporadic.SuzOddCore.outer_carrier_suz.1)
  | ONan =>
    exact CFSG.Sporadic.SteinbergBI.cti_on_outer_order_divides_two
      ⟨(MulEquiv.refl _ : NativeSporadic.Carrier .ONan ≃* NativeSporadic.ON)⟩
  | Co1 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (.inl CFSG.RankThree.PartOne.SPOR.card_outer_Co1)
  | Co2 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (.inl CFSG.RankThree.PartOne.SPOR.card_outer_Co2)
  | Co3 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (G := NativeSporadic.Co3)
      (.inl CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1)
  | Fi22 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (G := NativeSporadic.Fi22)
      (.inr CFSG.RankThree.PartOne.card_outer_fi22_carrier)
  | Fi23 =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (G := NativeSporadic.Fi23)
      (.inl CFSG.Sporadic.FischerOddCore.card_outer_fi23)
  | Fi24Prime =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (G := NativeSporadic.Fi24prime)
      (.inr CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime)
  | HN =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (.inr CFSG.RankThree.PartOne.SPOR.card_outer_HN)
  | Ly => exact AGLEmbedding.card_outer_dvd_two_of_eq CFSG.RankThree.PartOne.SPOR.card_outer_Ly
  | Th =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (.inl CFSG.RankThree.PartOne.SPOR.card_outer_Th)
  | B =>
    exact AGLEmbedding.card_outer_dvd_two_of_eq (.inl CFSG.RankThree.PartOne.SPOR.card_outer_B)
  | M =>
    have : IsSimpleGroup (NativeSporadic.Carrier .M) := hM rfl
    exact AGLEmbedding.card_outer_dvd_two_of_eq
      (.inl (CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple (MulEquiv.refl _)))

theorem card_outer_dvd_two {S : Type} [Group S] [IsSimpleGroup S]
    (hS : NativeSporadic.SporadicRep S) : Nat.card (Outer S) ∣ 2 := by
  obtain ⟨s, ⟨e⟩⟩ := hS
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact card_outer_native_dvd_two s fun hs => by subst hs; exact e.symm.isSimpleGroup

section General

theorem sporadic_outer_two_pow : ∀ (S : Type) [Group S] [Finite S],
    NativeSporadic.SporadicRep S → ∃ k : ℕ, Nat.card (Outer S) ∣ 2 ^ k := by
  intro S _ _ ⟨s, ⟨e⟩⟩
  refine ⟨1, ?_⟩
  rw [pow_one, Nat.card_congr (equivalence e).toEquiv]
  exact card_outer_native_dvd_two s fun _ =>
    CFSG.Blueprint.NativeSporadic.MonsterModel.isSimpleGroup_y443Derived

end General

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
