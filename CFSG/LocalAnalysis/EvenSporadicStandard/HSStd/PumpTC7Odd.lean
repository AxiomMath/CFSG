module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.EvenSporadicStandard.HSStd.PumpTC7

open Subgroup

theorem not_eight_dvd_card_inf_centralizer {M : Type*} [Group M] [Finite M] {P R : Subgroup M}
    (hPR : P ≤ R) (hidx : P.relIndex R ≤ 4) {z : M}
    (hodd : ¬ 2 ∣ Nat.card ↥(P ⊓ centralizer ({z} : Set M))) :
    ¬ 8 ∣ Nat.card ↥(R ⊓ centralizer ({z} : Set M)) := by
  set E : Subgroup M := R ⊓ centralizer ({z} : Set M) with hE
  have hPE : P ⊓ E = P ⊓ centralizer ({z} : Set M) := by
    rw [hE, ← inf_assoc, inf_eq_left.2 hPR]
  have hne : P.relIndex R ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_mul_card (H := P) (K := R)
    rw [h0, zero_mul] at this
    exact (Nat.card_pos (α := ↥R)).ne' this.symm
  have hle : P.relIndex E ≤ 4 :=
    (Subgroup.relIndex_le_of_le_right inf_le_left hne).trans hidx
  have hcard := Subgroup.relIndex_mul_card (H := P) (K := E)
  rw [hPE] at hcard
  intro h8
  rw [← hcard] at h8
  have hcop : Nat.Coprime 8 (Nat.card ↥(P ⊓ centralizer ({z} : Set M))) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
  have h8' : 8 ∣ P.relIndex E := hcop.dvd_of_dvd_mul_right h8
  have hpos : 0 < P.relIndex E := by
    rcases Nat.eq_zero_or_pos (P.relIndex E) with h0 | h0
    · rw [h0, zero_mul] at hcard
      exact absurd hcard.symm (Nat.card_pos (α := ↥E)).ne'
    · exact h0
  have := Nat.le_of_dvd hpos h8'
  omega

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def fixSet (z : Equiv.Perm α) : Finset α := Finset.univ.filter fun a => z a = a

theorem card_fix_modEq {p : ℕ} [Fact p.Prime] {x y : Equiv.Perm α} (hx : x ^ p = 1)
    (hcomm : x * y = y * x) :
    ((fixSet y).filter fun a => x a = a).card ≡ (fixSet y).card [MOD p] := by
  have hxy : ∀ a, y (x a) = x (y a) := fun a => by
    have := congrArg (fun w : Equiv.Perm α => w a) hcomm
    simpa [Equiv.Perm.mul_apply] using this.symm
  have hiff : ∀ a, (fun q => q ∈ fixSet y) (x a) ↔ (fun q => q ∈ fixSet y) a := by
    intro a
    simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hxy a]
    exact ⟨fun h => x.injective h, fun h => by rw [h]⟩
  let σ : Equiv.Perm {q // q ∈ fixSet y} := x.subtypePerm hiff
  have hσ : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    ext ⟨q, hq⟩
    simp [σ, Equiv.Perm.subtypePerm_pow, hx]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  rw [Fintype.card_coe] at hmod
  have hcard : σ.supportᶜ.card = ((fixSet y).filter fun a => x a = a).card := by
    refine Finset.card_bij (fun q _ => (q : α)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hq
      simp only [Finset.mem_filter]
      exact ⟨q.2, congrArg Subtype.val hq⟩
    · intro q _ q' _ h
      exact Subtype.ext h
    · intro a ha
      simp only [Finset.mem_filter] at ha
      refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
      rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      exact Subtype.ext ha.2
  rw [hcard] at hmod
  exact hmod

theorem false_of_commuting_fixed {z w : Equiv.Perm α} (hz : z ^ 3 = 1) (hw : w ^ 2 = 1)
    (hcomm : z * w = w * z) (hfz : (fixSet z).card = 2) (hfw : (fixSet w).card % 3 = 1) :
    False := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e1 := card_fix_modEq (p := 3) (x := z) (y := w) hz hcomm
  have e2 := card_fix_modEq (p := 2) (x := w) (y := z) hw hcomm.symm
  have hsub : ((fixSet z).filter fun a => w a = a).card ≤ (fixSet z).card :=
    Finset.card_filter_le _ _
  have hsame : ((fixSet w).filter fun a => z a = a).card =
      ((fixSet z).filter fun a => w a = a).card := by
    congr 1
    ext a
    simp only [fixSet, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hsame] at e1
  unfold Nat.ModEq at e1 e2
  omega

end CFSG.EvenSporadicStandard.HSStd.PumpTC7
