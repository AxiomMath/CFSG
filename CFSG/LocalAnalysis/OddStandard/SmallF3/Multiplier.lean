module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.Models.Blueprint
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Open

private theorem card_center_dvd_griessHopfMultiplier_aux {S Q : Type} [Group S] [Group Q]
    (hQ : Group.IsPerfect Q) (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (griessHopfMultiplier S) := by
  have := hQ
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := CFSG.RankThree.PerfectCover.hopfMultiplier S)
    (CFSG.RankThree.PerfectCover.hopfLift q hq hker.le)

theorem card_center_dvd_card_griessHopfMultiplier {Q : Type} [Group Q] (hQ : Group.IsPerfect Q) :
    Nat.card (center Q) ∣ Nat.card (griessHopfMultiplier (Q ⧸ center Q)) :=
  card_center_dvd_griessHopfMultiplier_aux hQ (MulEquiv.refl _)

theorem card_griessHopfMultiplier_psl_four_three (hGA : GriessAllModelsStatement)
    {Q : Type} [Group Q] (h : CFSG.Blueprint.LieModel Q .PSL 4 3 1) :
    Nat.card (griessHopfMultiplier Q) = 2 := by
  obtain ⟨e⟩ := (hGA Q .PSL 4 3 1
    (CFSG.Models.LieModel.of_blueprint (by decide) h)).2
  rw [Nat.card_congr e.toEquiv]
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 4 3 1 = (2, 1) := by
    change (Nat.gcd 4 (3 ^ 1 - 1), 1) = (2, 1)
    norm_num
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 3 1 = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

theorem card_griessHopfMultiplier_psu_four_three (hGA : GriessAllModelsStatement)
    {Q : Type} [Group Q] (h : CFSG.Blueprint.LieModel Q .PSU 4 3 1) :
    Nat.card (griessHopfMultiplier Q) = 36 := by
  obtain ⟨e⟩ := (hGA Q .PSU 4 3 1
    (CFSG.Models.LieModel.of_blueprint (by decide) h)).2
  rw [Nat.card_congr e.toEquiv]
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 4 3 1 = (4, 1) := by
    change (Nat.gcd 4 (3 ^ 1 + 1), 1) = (4, 1)
    norm_num
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 3 1 = (3, 3) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

theorem card_center_eq_two_of_psl_four_three (hGA : GriessAllModelsStatement)
    {L : Type} [Group L] (hL : Group.IsPerfect L) (hev : Even (Nat.card (center L)))
    (h : CFSG.Blueprint.LieModel (L ⧸ center L) .PSL 4 3 1) :
    Nat.card (center L) = 2 := by
  have hdvd : Nat.card (center L) ∣ Nat.card (griessHopfMultiplier (L ⧸ center L)) :=
    card_center_dvd_card_griessHopfMultiplier hL
  rw [card_griessHopfMultiplier_psl_four_three hGA h] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · rw [h1] at hev
    exact absurd hev Nat.not_even_one
  · exact h2

theorem card_center_dvd_thirtySix_of_psu_four_three (hGA : GriessAllModelsStatement)
    {L : Type} [Group L] (hL : Group.IsPerfect L)
    (h : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 4 3 1) :
    Nat.card (center L) ∣ 36 := by
  have hdvd : Nat.card (center L) ∣ Nat.card (griessHopfMultiplier (L ⧸ center L)) :=
    card_center_dvd_card_griessHopfMultiplier hL
  rwa [card_griessHopfMultiplier_psu_four_three hGA h] at hdvd

end CFSG.OddStandard.SmallF3
