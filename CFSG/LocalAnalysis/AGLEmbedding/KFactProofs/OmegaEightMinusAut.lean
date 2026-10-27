module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeAut
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbedding

namespace OmegaEightMinusAut

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_dvd_of_isPGroup_mulAut {L : Type*} [Group L] [Finite L] {p a m : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hcard : Nat.card L = p ^ a * m) (hm : ¬ p ∣ m) (hOut : Nat.card (Outer L) ≤ 2)
    (S : Subgroup (MulAut L)) (hS : IsPGroup p S) : Nat.card S ∣ p ^ a := by
  have : Finite (MulAut L) := MulEquiv.finite_left
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hAut : Nat.card (MulAut L) = Nat.card (Outer L) * Nat.card (inner L) :=
    (inner L).card_eq_card_quotient_mul_card_subgroup
  have hInn : Nat.card (inner L) ∣ Nat.card L := Subgroup.card_range_dvd _
  have hdvd : Nat.card S ∣ p ^ a * (m * Nat.card (Outer L)) := by
    refine (Subgroup.card_subgroup_dvd_card S).trans ?_
    rw [hAut]
    refine (Nat.mul_dvd_mul_left _ hInn).trans ?_
    rw [hcard]
    exact ⟨1, by ring⟩
  have hpos : 0 < Nat.card (Outer L) := Nat.card_pos
  have hpOut : ¬ p ∣ Nat.card (Outer L) := fun h => by
    have := Nat.le_of_dvd hpos h
    have := (Fact.out : p.Prime).two_le
    omega
  have hcop : p.Coprime (m * Nat.card (Outer L)) :=
    Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
      ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpOut)
  rw [hk] at hdvd ⊢
  exact (Nat.Coprime.pow_left k hcop).dvd_of_dvd_mul_right hdvd

theorem card_eq_of_statedClassicalModel {T : Type} [Group T]
    (h : StatedClassicalModel T .POmegaMinus 4 2 1) : Nat.card T = 197406720 := by
  obtain ⟨K, _, _, _, hK, -, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.exists_mulEquiv_of_lieModel
      (Or.inl ⟨by decide, h⟩ : CFSG.Blueprint.LieModel T .POmegaMinus 4 2 1)
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.EvenSmallLie.OmegaEightMinus.card_elementaryGroup_qM hK

end OmegaEightMinusAut

theorem kFactOmegaEightMinusAut : KFactOmegaEightMinusAut := by
  intro L _ _ d hd ⟨e⟩ Q hQ
  rcases d with ⟨i, hi⟩
  obtain ⟨q, hqp, hqe, hiq⟩ := hd
  simp only at hiq
  subst hiq
  have hmodel :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even 4 q hi hqp e
  rw [hqp, hqe] at hmodel
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact OmegaEightMinusAut.card_dvd_of_isPGroup_mulAut (a := 4) (m := 2437120) (by norm_num)
    ((OmegaEightMinusAut.card_eq_of_statedClassicalModel hmodel).trans (by norm_num))
    (by norm_num) (CFSG.EvenSmallLie.OmegaEightMinus.card_outer_le_two hmodel) Q hQ

end CFSG.AGLEmbedding
