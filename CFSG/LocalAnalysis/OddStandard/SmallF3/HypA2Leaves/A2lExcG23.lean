module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lExcRee

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Open (ordA ordTwistedA ordBC ordD ordTwistedD)

@[expose] def a2lG23Comp : Prop :=
  ∀ (S : Type) [Group S], LieModel S .G2 0 3 1 → ∀ α : MulAut S, orderOf α = 2 →
    ∀ L : Subgroup (fixedSubgroup α), IsComponent L → LieModel L .PSL 2 2 3

theorem a2l_fStarSimple_card {Q : Type} [Group Q] (h : HypA2.FStarSimple Q) :
    Nat.card Q = 360 ∨ 504 < Nat.card Q := by
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have key : ∀ {t : CFSG.Open.StatedLieTag} {n d : ℕ}, n ≠ 0 → LieModel Q t n 3 d →
      (t = .PSL → Nat.card Q = ordA (n - 1) (3 ^ d)) ∧
      (t = .PSU → Nat.card Q = ordTwistedA (n - 1) (3 ^ d)) ∧
      (t = .PSp → Nat.card Q = ordBC n (3 ^ d)) ∧
      (t = .POmegaOdd → Nat.card Q = ordBC n (3 ^ d)) ∧
      (t = .POmegaPlus → Nat.card Q = ordD n (3 ^ d)) ∧
      (t = .POmegaMinus → Nat.card Q = ordTwistedD n (3 ^ d)) :=
    fun hn hm => CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp
      (GH74.statedClassicalModel_of_lieModel hn hm)
  unfold HypA2.FStarSimple at h
  rcases h with h1 | h2 | h3 | h4 | h5
  · left
    rw [(key (by norm_num) h1).1 rfl]
    decide
  · right
    rw [(key (by norm_num) h2).1 rfl]
    decide
  · right
    rw [(key (by norm_num) h3).1 rfl]
    decide
  · right
    rw [(key (by norm_num) h4).2.1 rfl]
    decide
  · right
    unfold SmallF3OmegaQuotient at h5
    rcases h5 with h | h | h | h | h | h
    · rw [(key (by norm_num) h).2.2.1 rfl]
      decide
    · rw [(key (by norm_num) h).1 rfl]
      decide
    · rw [(key (by norm_num) h).2.1 rfl]
      decide
    · rw [(key (by norm_num) h).2.2.2.1 rfl]
      decide
    · rw [(key (by norm_num) h).2.2.2.2.1 rfl]
      decide
    · rw [(key (by norm_num) h).2.2.2.2.2 rfl]
      decide

theorem a2l_not_fStarSimple_of_card_dvd {Q : Type} [Group Q] (h : HypA2.FStarSimple Q)
    (hd : Nat.card Q ∣ 504) : False := by
  rcases a2l_fStarSimple_card h with h1 | h1
  · rw [h1] at hd
    exact absurd hd (by decide)
  · exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)

theorem a2l_chev3On_g23 (hQ : a2lFixedQuasi) (hG : a2lG23Comp) :
    a2lChev3On fun S _ => LieModel S .G2 0 3 1 := by
  intro K _ _ hK h2 _ hnF hS σ hσ X hXσ hXc hXF
  exfalso
  obtain ⟨σ', P, hPF, hF⟩ := a2l_exc_reduce hK hnF hσ hXσ hXc hXF
  haveI : IsSimpleGroup (K ⧸ center K) := hK.2.1
  have hq := hQ (K ⧸ center K) hK.2.2
    ⟨.G2, 0, 3, 1, Nat.prime_three, by norm_num, hS.admissible, hS⟩
  obtain ⟨hP, hF'⟩ := a2l_exc_component hq hPF hF
  have hord : orderOf σ' = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact MulEquiv.ext fun y => hP.1 y) hPF.ne_one
  have hL := hG (K ⧸ center K) hS σ' hord _ hP.2.2.2
  have hcardL : Nat.card (P.subgroupOf (fixedSubgroup σ')) = 504 := by
    rw [GH74.card_of_lieModel_PSL (by norm_num) hL]
    decide
  have hcardP : Nat.card P = 504 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.2.1).toEquiv).symm.trans hcardL
  exact a2l_not_fStarSimple_of_card_dvd hF' (hcardP ▸ Subgroup.card_quotient_dvd_card _)

end CFSG.OddStandard.SmallF3.HypA2Leaves
