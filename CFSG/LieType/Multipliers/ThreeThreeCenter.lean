module

public import CFSG.Open.Defs
public import CFSG.Blueprint.Catalog
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitModel
import CFSG.GH74.Generic.BProg.B2.L3Cover
import CFSG.Quasithin.Background.C126RFTypes

public section

namespace CFSG.LieType.Multipliers

open CFSG.Blueprint (LieModel)

theorem center_eq_bot_of_lieModel_psu_three_three
    {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (h : LieModel (L ⧸ Subgroup.center L) .PSU 3 3 1) :
    Subgroup.center L = ⊥ := by
  obtain ⟨-, F, _, _, hFcard, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hdvd : Nat.card (Subgroup.center L) ∣ Nat.gcd 3 (3 ^ 1 + 1) :=
    letI : Fintype F := Fintype.ofFinite F
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    letI : CharP F 3 :=
      charP_of_card_eq_prime_pow (p := 3) (f := 2) (by
        rw [← Nat.card_eq_fintype_card, hFcard]
        norm_num)
    CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.card_center_dvd_gcd_of_psu
      (L := L) (F := F) (p := 3) (f := 1) (n := 3) ⟨hq.1⟩
      (by norm_num) le_rfl hFcard le_rfl (by norm_num) e
  rw [show Nat.gcd 3 (3 ^ 1 + 1) = 1 by norm_num, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

theorem center_eq_bot_of_lieModel_psl_three_three {L : Type} [Group L] [Finite L]
    (hq : CFSG.Open.IsQuasisimple L) (h : LieModel (L ⧸ Subgroup.center L) .PSL 3 3 1) :
    Subgroup.center L = ⊥ := by
  exact (CFSG.GH74.Generic.BProg.B2.l3_three_cover_center
    (CFSG.Quasithin.C126.c126_isQuasisimple_of_open hq) h).1

end CFSG.LieType.Multipliers
