module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase234
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (ThreeTenTorusExclusion)

theorem dvd_card_of_threeTenHyp_of_isSLType_of_not_dvd_sub_one {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (h1 : ¬ d ∣ p - 1) : d ∣ Nat.card ↥I := by
  have hdvdAutI : d ∣ Nat.card (MulAut ↥I) := dvd_card_mulAut_of_threeTenHyp hhyp
  obtain ⟨hp, -, hd, hd2, -, -, -, -, -, -, -, -⟩ := hhyp
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardAutI : Nat.card (MulAut ↥I) =
      Nat.card (MulAut (SpecialLinearGroup (Fin 3) (ZMod p))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  have hdvdAutSL : d ∣ Nat.card (MulAut (SpecialLinearGroup (Fin 3) (ZMod p))) := by
    rwa [hcardAutI] at hdvdAutI
  have hinj : Function.Injective (descendAut 3 (ZMod p)) :=
    CFSG.RankThree.PartOne.AUTSL.descendAut_injective (n := 3) (K := ZMod p) (by norm_num)
  have hcardRange : Nat.card (MulAut (SpecialLinearGroup (Fin 3) (ZMod p))) =
      Nat.card (descendAut 3 (ZMod p)).range := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) hinj,
      Subgroup.card_top]
  have hdvdAutPSL : d ∣ Nat.card (MulAut (projectiveSL 3 (ZMod p))) := by
    have h : d ∣ Nat.card (descendAut 3 (ZMod p)).range := by
      rwa [hcardRange] at hdvdAutSL
    exact h.trans (Subgroup.card_subgroup_dvd_card _)
  have hcenter : Subgroup.center (projectiveSL 3 (ZMod p)) = ⊥ := by
    haveI : Group.IsPerfect (SpecialLinearGroup (Fin 3) (ZMod p)) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
    have h := Group.IsPerfect.center_quotient_center_eq_bot
      (G := SpecialLinearGroup (Fin 3) (ZMod p))
    have hmap := Subgroup.map_center_eq
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod p))
    rw [← hmap, h, Subgroup.map_bot]
  have hdvdProd : d ∣ Nat.card (projectiveSL 3 (ZMod p)) *
      Nat.card (Outer (projectiveSL 3 (ZMod p))) := by
    refine hdvdAutPSL.trans ?_
    have h := card_dvd_card_mul_card_outer (T := projectiveSL 3 (ZMod p)) hcenter
      (A := ⊤) le_top
    simpa only [Subgroup.card_top] using h
  have hOutdvd : Nat.card (Outer (projectiveSL 3 (ZMod p))) ∣ 2 * Nat.gcd 3 (p - 1) := by
    have hk : Nat.card (ZMod p) = p ^ 1 := by
      rw [pow_one, Nat.card_zmod]
    have h := higher_linear_outer_order_divides_field_gcd_bound
      (k := ZMod p) (p := p) (f := 1) (n := 3) hp le_rfl (by norm_num) hk
    simpa using h
  have hdvdPSL : d ∣ Nat.card (projectiveSL 3 (ZMod p)) := by
    by_contra hnot
    have hdvdOut : d ∣ Nat.card (Outer (projectiveSL 3 (ZMod p))) := by
      rcases (Nat.Prime.dvd_mul hd).1 hdvdProd with h | h
      · exact absurd h hnot
      · exact h
    have hdvd2 : d ∣ 2 * Nat.gcd 3 (p - 1) := hdvdOut.trans hOutdvd
    rcases (Nat.Prime.dvd_mul hd).1 hdvd2 with h2 | hg
    · have hd2' : d = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
        · exact absurd h hd.ne_one
        · exact h
      exact hd2 hd2'
    · have hdvdP1 : d ∣ p - 1 := hg.trans (Nat.gcd_dvd_right 3 (p - 1))
      exact h1 hdvdP1
  have hdvdSL : d ∣ Nat.card (SpecialLinearGroup (Fin 3) (ZMod p)) :=
    hdvdPSL.trans (Subgroup.card_quotient_dvd_card (scalars 3 (ZMod p)))
  rw [Nat.card_congr e.toEquiv]
  exact hdvdSL

theorem dvd_card_of_threeTenHyp_of_isSLType {H : Type} [Group H] [Finite H]
    {I D P Y : Subgroup H} {p d : ℕ} (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (htor : ThreeTenTorusExclusion p d) : d ∣ Nat.card ↥I :=
  dvd_card_of_threeTenHyp_of_isSLType_of_not_dvd_sub_one hhyp e htor.1

end CFSG.LocalAnalysis.AGL81I.Section3
