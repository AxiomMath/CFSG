module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SSmall
import CFSG.Sporadic.Schreier.PairMcLOut
import CFSG.Sporadic.Schreier.RuAutInner
import CFSG.Sporadic.Schreier.Co1CatalogSchreier
import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
import CFSG.Sporadic.Co2Schreier.Model
import CFSG.Sporadic.FischerOddCore.Fi23Aut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
import CFSG.RankThree.PartOne.KP.Co3Aut
import CFSG.RankThree.PartOne.SPOR.OuterSimple
import CFSG.Sporadic.ONOddCore.OuterOrder
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
public import CFSG.LocalAnalysis.GL83PartI.I713.Sporadic
public import CFSG.Sporadic.NativeFinite
public import CFSG.Sporadic.Schreier.M23

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms GL83.I713

theorem liftClause_sporadic_M11
    [Finite (NativeSporadic.Carrier .M11)]
    [IsSimpleGroup (NativeSporadic.Carrier .M11)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .M11, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .M11) :=
  liftClause_of_card_outer_le_four hnonab (Sporadic.Schreier.at_m11_schreier.1.trans (by norm_num))

theorem liftClause_sporadic_M12
    [Finite (NativeSporadic.Carrier .M12)]
    [IsSimpleGroup (NativeSporadic.Carrier .M12)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .M12, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .M12) :=
  liftClause_of_card_outer_le_four hnonab Sporadic.Schreier.at_m12_schreier.1

theorem liftClause_sporadic_M22
    [Finite (NativeSporadic.Carrier .M22)]
    [IsSimpleGroup (NativeSporadic.Carrier .M22)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .M22, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .M22) :=
  liftClause_of_card_outer_le_four hnonab Sporadic.Schreier.at_m22_schreier.1

theorem liftClause_sporadic_M23
    [Finite (NativeSporadic.Carrier .M23)]
    [IsSimpleGroup (NativeSporadic.Carrier .M23)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .M23, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .M23) :=
  liftClause_of_card_outer_le_four hnonab (Sporadic.Schreier.at_m23_schreier.1.trans (by norm_num))

theorem liftClause_sporadic_M24
    [Finite (NativeSporadic.Carrier .M24)]
    [IsSimpleGroup (NativeSporadic.Carrier .M24)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .M24, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .M24) :=
  liftClause_of_card_outer_le_four hnonab Sporadic.Schreier.at_m24_schreier.1

theorem liftClause_sporadic_J1
    [Finite (NativeSporadic.Carrier .J1)]
    [IsSimpleGroup (NativeSporadic.Carrier .J1)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .J1, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .J1) :=
  liftClause_of_card_outer_le_four hnonab
    (Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num))

theorem liftClause_sporadic_J2
    [Finite (NativeSporadic.Carrier .J2)]
    [IsSimpleGroup (NativeSporadic.Carrier .J2)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .J2, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .J2) :=
  liftClause_of_card_outer_le_four hnonab
    (Sporadic.Schreier.AT_J2_Schreier.1.trans (by norm_num))

theorem liftClause_sporadic_J3
    [Finite (NativeSporadic.Carrier .J3)]
    [IsSimpleGroup (NativeSporadic.Carrier .J3)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .J3, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .J3) :=
  liftClause_of_card_outer_le_six hnonab Sporadic.Schreier.AT_J3_Schreier.1

theorem liftClause_sporadic_HS
    [Finite (NativeSporadic.Carrier .HS)]
    [IsSimpleGroup (NativeSporadic.Carrier .HS)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .HS, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .HS) :=
  liftClause_of_card_outer_le_four hnonab
    (CFSG.RankThree.PartOne.SPOR.sporadicHS_outer_le_two.trans (by norm_num))

theorem liftClause_sporadic_McL
    [Finite (NativeSporadic.Carrier .McL)]
    [IsSimpleGroup (NativeSporadic.Carrier .McL)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .McL, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .McL) :=
  liftClause_of_card_outer_le_four hnonab
    (Sporadic.Schreier.McL_outer_card_le_two.1.trans (by norm_num))

theorem liftClause_sporadic_He
    [Finite (NativeSporadic.Carrier .He)]
    [IsSimpleGroup (NativeSporadic.Carrier .He)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .He, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .He) :=
  liftClause_of_card_outer_le_four hnonab
    (Sporadic.Schreier.AT_He_Schreier.1.trans (by norm_num))

theorem liftClause_sporadic_Ru
    [Finite (NativeSporadic.Carrier .Ru)]
    [IsSimpleGroup (NativeSporadic.Carrier .Ru)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Ru, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Ru) := by
  have h : Nat.card (Outer (NativeSporadic.Carrier .Ru)) ≤ 2 := by
    rw [show Nat.card (Outer (NativeSporadic.Carrier .Ru)) =
        Nat.card (Outer Sporadic.RuSchreier.ruP) from
      CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv
        Sporadic.RuSchreier.ruEquivP,
      Sporadic.RuSchreier.card_outer_ruP]
    norm_num
  exact liftClause_of_card_outer_le_four hnonab (h.trans (by norm_num))

theorem liftClause_sporadic_Suz
    [Finite (NativeSporadic.Carrier .Suz)]
    [IsSimpleGroup (NativeSporadic.Carrier .Suz)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Suz, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Suz) :=
  liftClause_of_card_outer_le_four hnonab
    (Sporadic.SuzOddCore.outer_carrier_suz.1.le.trans (by norm_num))

theorem liftClause_sporadic_Co1
    [Finite (NativeSporadic.Carrier .Co1)]
    [IsSimpleGroup (NativeSporadic.Carrier .Co1)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Co1, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Co1) := by
  have h := (Sporadic.Co1Schreier.catalog_schreier_of_inputs.{0}
    fun K _ e => Sporadic.Co2Schreier.AT_Co2_model_Schreier K e).2.2.1
  exact liftClause_of_not_dvd fun _ hp hp2 _ =>
    not_dvd_card_outer_of_isPGroup_two (K := NativeSporadic.Carrier .Co1) h hp hp2

theorem liftClause_sporadic_Co2
    [Finite (NativeSporadic.Carrier .Co2)]
    [IsSimpleGroup (NativeSporadic.Carrier .Co2)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Co2, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Co2) := by
  obtain ⟨e⟩ : Nonempty (NativeSporadic.Carrier .Co2 ≃* NativeSporadic.Co2) :=
    ⟨MulEquiv.refl _⟩
  have h := (Sporadic.Co2Schreier.AT_Co2_model_Schreier _ e).2.1
  exact liftClause_of_not_dvd fun _ hp hp2 _ =>
    not_dvd_card_outer_of_isPGroup_two (K := NativeSporadic.Carrier .Co2) h hp hp2

theorem liftClause_sporadic_Co3
    [Finite (NativeSporadic.Carrier .Co3)]
    [IsSimpleGroup (NativeSporadic.Carrier .Co3)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Co3, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Co3) := by
  have h : Nat.card (Outer NativeSporadic.Co3) = 1 :=
    CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1
  exact liftClause_of_card_outer_le_four hnonab (h.le.trans (by norm_num))

theorem liftClause_sporadic_Fi22
    [Finite (NativeSporadic.Carrier .Fi22)]
    [IsSimpleGroup (NativeSporadic.Carrier .Fi22)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Fi22, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Fi22) :=
  liftClause_of_card_outer_le_four hnonab
    (ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22.le.trans (by norm_num))

theorem liftClause_sporadic_Fi23
    [Finite (NativeSporadic.Carrier .Fi23)]
    [IsSimpleGroup (NativeSporadic.Carrier .Fi23)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Fi23, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Fi23) :=
  liftClause_of_card_outer_le_four hnonab
    (Sporadic.FischerOddCore.card_outer_fi23.le.trans (by norm_num))

theorem liftClause_sporadic_Fi24Prime
    [Finite (NativeSporadic.Carrier .Fi24Prime)]
    [IsSimpleGroup (NativeSporadic.Carrier .Fi24Prime)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Fi24Prime, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Fi24Prime) :=
  liftClause_of_card_outer_le_four hnonab
    (Sporadic.Schreier.Fi24.card_outer_fi24prime.le.trans (by norm_num))

theorem liftClause_sporadic_HN
    [Finite (NativeSporadic.Carrier .HN)]
    [IsSimpleGroup (NativeSporadic.Carrier .HN)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .HN, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .HN) :=
  liftClause_of_card_outer_le_four hnonab
    (CFSG.RankThree.PartOne.SPOR.card_outer_HN.le.trans (by norm_num))

theorem liftClause_sporadic_Ly
    [Finite (NativeSporadic.Carrier .Ly)]
    [IsSimpleGroup (NativeSporadic.Carrier .Ly)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Ly, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Ly) := by
  rcases CFSG.RankThree.PartOne.SPOR.card_outer_Ly with h | h <;>
    exact liftClause_of_card_outer_le_four hnonab (h.le.trans (by norm_num))

theorem liftClause_sporadic_Th
    [Finite (NativeSporadic.Carrier .Th)]
    [IsSimpleGroup (NativeSporadic.Carrier .Th)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .Th, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .Th) :=
  liftClause_of_card_outer_le_four hnonab
    (CFSG.RankThree.PartOne.SPOR.card_outer_Th.le.trans (by norm_num))

theorem liftClause_sporadic_B
    [Finite (NativeSporadic.Carrier .B)]
    [IsSimpleGroup (NativeSporadic.Carrier .B)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .B, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .B) :=
  liftClause_of_card_outer_le_four hnonab
    (CFSG.RankThree.PartOne.SPOR.card_outer_B.le.trans (by norm_num))

theorem liftClause_sporadic_M
    [Finite (NativeSporadic.Carrier .M)] [IsSimpleGroup (NativeSporadic.Carrier .M)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .M, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .M) :=
  liftClause_of_card_outer_le_four hnonab
    ((CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple (MulEquiv.refl _)).le.trans
      (by norm_num))

local instance finite_carrier_J4' : Finite (NativeSporadic.Carrier .J4) :=
  CFSG.Sporadic.finite_carrier_of_ne_M .J4 (by decide)

theorem liftClause_sporadic_J4
    [IsSimpleGroup (NativeSporadic.Carrier .J4)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .J4, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .J4) :=
  liftClause_of_card_outer_le_four hnonab
    (CFSG.AGLEmbedding.card_outer_J4.le.trans (by norm_num))

theorem liftClause_sporadic_ONan
    [Finite (NativeSporadic.Carrier .ONan)]
    [IsSimpleGroup (NativeSporadic.Carrier .ONan)]
    (hnonab : ∃ a b : NativeSporadic.Carrier .ONan, a * b ≠ b * a) :
    LiftClause (NativeSporadic.Carrier .ONan) := by
  apply liftClause_of_card_outer_le_four hnonab
  show Nat.card (Outer NativeSporadic.ON) ≤ 4
  exact Nat.le_of_dvd (by norm_num) CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1

theorem liftClause_sporadicRep

    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (h : NativeSporadic.SporadicRep S) : LiftClause S := by
  obtain ⟨s, ⟨e⟩⟩ := h
  have : Finite (NativeSporadic.Carrier s) := Finite.of_equiv S e.toEquiv
  have : IsSimpleGroup (NativeSporadic.Carrier s) := e.symm.isSimpleGroup
  have hnonab' : ∃ a b : NativeSporadic.Carrier s, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa only [map_mul] using h))⟩
  refine LiftClause.of_mulEquiv e ?_
  cases s with
  | M11 => exact liftClause_sporadic_M11 hnonab'
  | M12 => exact liftClause_sporadic_M12 hnonab'
  | M22 => exact liftClause_sporadic_M22 hnonab'
  | M23 => exact liftClause_sporadic_M23 hnonab'
  | M24 => exact liftClause_sporadic_M24 hnonab'
  | J1 => exact liftClause_sporadic_J1 hnonab'
  | J2 => exact liftClause_sporadic_J2 hnonab'
  | J3 => exact liftClause_sporadic_J3 hnonab'
  | J4 => exact liftClause_sporadic_J4 hnonab'
  | HS => exact liftClause_sporadic_HS hnonab'
  | McL => exact liftClause_sporadic_McL hnonab'
  | He => exact liftClause_sporadic_He hnonab'
  | Ru => exact liftClause_sporadic_Ru hnonab'
  | Suz => exact liftClause_sporadic_Suz hnonab'
  | ONan => exact liftClause_sporadic_ONan hnonab'
  | Co1 => exact liftClause_sporadic_Co1 hnonab'
  | Co2 => exact liftClause_sporadic_Co2 hnonab'
  | Co3 => exact liftClause_sporadic_Co3 hnonab'
  | Fi22 => exact liftClause_sporadic_Fi22 hnonab'
  | Fi23 => exact liftClause_sporadic_Fi23 hnonab'
  | Fi24Prime => exact liftClause_sporadic_Fi24Prime hnonab'
  | HN => exact liftClause_sporadic_HN hnonab'
  | Ly => exact liftClause_sporadic_Ly hnonab'
  | Th => exact liftClause_sporadic_Th hnonab'
  | B => exact liftClause_sporadic_B hnonab'
  | M => exact liftClause_sporadic_M hnonab'

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
