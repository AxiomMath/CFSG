module

public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Models.Transport
public import CFSG.Models.Blueprint
public import CFSG.Open.GriessAllModelsStatement

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.RankThree.PerfectCover

theorem card_center_dvd_card_hopfMultiplier_of_perfect {Q : Type} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (hopfMultiplier (Q ⧸ Subgroup.center Q)) := by
  have hker : (QuotientGroup.mk' (Subgroup.center Q)).ker ≤ Subgroup.center Q :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨-, ⟨_h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier (QuotientGroup.mk' (Subgroup.center Q))
      (QuotientGroup.mk'_surjective _) hker
  have hdvd : Nat.card (QuotientGroup.mk' (Subgroup.center Q)).ker ∣
      Nat.card (hopfMultiplier (Q ⧸ Subgroup.center Q)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rwa [QuotientGroup.ker_mk'] at hdvd

theorem card_hopfMultiplier_of_griess (hGA : CFSG.Open.GriessAllModelsStatement)
    (X : Type) [Group X] (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p f : ℕ)
    (h : CFSG.Models.LieModel X t n p f) :
    Nat.card (hopfMultiplier X) = Nat.card (CFSG.Blueprint.Multiplier.generic t n p f ×
      CFSG.Blueprint.Multiplier.exceptional t n p f) := by
  obtain ⟨-, ⟨F⟩⟩ := hGA X t n p f h
  exact (Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv).symm.trans
    (Nat.card_congr F.toEquiv)

theorem card_multiplier_psl_four_four :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 4 2 2 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 4 2 2) = 1 := by
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 4 2 2 = (1, 1) := by
    change (Nat.gcd 4 (2 ^ 2 - 1), 1) = (1, 1)
    norm_num
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 2 2 = (1, 1) := rfl
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

theorem card_multiplier_psu_four_two :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 4 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 2 1) = 2 := by
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 4 2 1 = (1, 1) := by
    change (Nat.gcd 4 (2 ^ 1 + 1), 1) = (1, 1)
    norm_num
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 1 = (2, 1) := rfl
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

theorem center_eq_bot_of_psl_four_four (hGA : CFSG.Open.GriessAllModelsStatement)
    {Q D : Type} [Group Q] [Finite Q] [Group D] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* D) (hD : CFSG.Blueprint.LieModel D .PSL 4 2 2)
    (hodd : Odd (Nat.card (Subgroup.center Q))) : Subgroup.center Q = ⊥ := by
  have ht : CFSG.Assembly.LowTwoRank.StatedLieTag.PSL ∈ CFSG.Blueprint.classicalTags := by
    decide
  have hQZ : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSL 4 2 2 :=
    CFSG.Models.LieModel.of_mulEquiv e.symm ((CFSG.Models.lieModel_iff_blueprint ht).mpr hD)
  have hdvd := card_center_dvd_card_hopfMultiplier_of_perfect hQ
  rw [card_hopfMultiplier_of_griess hGA (Q ⧸ Subgroup.center Q) .PSL 4 2 2 hQZ,
    card_multiplier_psl_four_four] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

theorem center_eq_bot_of_psu_four_two (hGA : CFSG.Open.GriessAllModelsStatement)
    {Q D : Type} [Group Q] [Finite Q] [Group D] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* D) (hD : CFSG.Blueprint.LieModel D .PSU 4 2 1)
    (hodd : Odd (Nat.card (Subgroup.center Q))) : Subgroup.center Q = ⊥ := by
  have ht : CFSG.Assembly.LowTwoRank.StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags := by
    decide
  have hQZ : CFSG.Models.LieModel (Q ⧸ Subgroup.center Q) .PSU 4 2 1 :=
    CFSG.Models.LieModel.of_mulEquiv e.symm ((CFSG.Models.lieModel_iff_blueprint ht).mpr hD)
  have hdvd := card_center_dvd_card_hopfMultiplier_of_perfect hQ
  rw [card_hopfMultiplier_of_griess hGA (Q ⧸ Subgroup.center Q) .PSU 4 2 1 hQZ,
    card_multiplier_psu_four_two] at hdvd
  have hle : Nat.card (Subgroup.center Q) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := hodd
  have h1 : Nat.card (Subgroup.center Q) = 1 := by omega
  exact Subgroup.card_eq_one.mp h1

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
