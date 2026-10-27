module

public import CFSG.FeitThompson.Local.LiftedAverageFixedDimension
import CFSG.FeitThompson.Local.RepresentationLiftArbitraryLevel

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix Module

section Congruence

variable {p d : ℕ} {A : Type*} [Group A] {ι : Type*} [Fintype ι]

private theorem sum_weighted_sum_subgroup [Fintype A] {R : Type*} [CommRing R]
    (B : ι → Subgroup A) [∀ i, DecidablePred (· ∈ B i)] (c : ι → R) (t : A → R)
    [∀ i, Fintype (B i)] :
    ∑ i, c i * ∑ b : B i, t (b : A) = ∑ a : A, (∑ i with a ∈ B i, c i) * t a := by
  have hin : ∀ i, ∑ b : B i, t (b : A) = ∑ a : A, if a ∈ B i then t a else 0 := fun i => by
    rw [← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) t).symm
  calc ∑ i, c i * ∑ b : B i, t (b : A)
      = ∑ a : A, ∑ i, (if a ∈ B i then c i * t a else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hin i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by split <;> simp
    _ = ∑ a : A, (∑ i with a ∈ B i, c i) * t a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_filter, Finset.sum_mul]

theorem sum_weighted_natCard_mul_finrank_glFixedSpace_zmod_eq_zero [Finite A]
    (hp : p.Prime) (hA : ¬ p ∣ Nat.card A) (ρ : A →* GL (Fin d) (ZMod p))
    (B : ι → Subgroup A) [∀ i, DecidablePred (· ∈ B i)] (c : ι → ℤ)
    (hc : ∀ a : A, ∑ i with a ∈ B i, c i = 0) {e : ℕ} (he : 1 ≤ e) :
    ((∑ i, c i * (Nat.card (B i) : ℤ) * (finrank (ZMod p) (glFixedSpace ρ (B i)) : ℤ) :
      ℤ) : ZMod (p ^ e)) = 0 := by
  have := Fintype.ofFinite A
  have : ∀ i, Fintype (B i) := fun i => Fintype.ofFinite _
  obtain ⟨ρe, hρe⟩ :=
    exists_monoidHom_glModPReduction_comp_eq (ι := Fin d) hp hA ρ he
  set t : A → ZMod (p ^ e) := fun a => (ρe a : Matrix (Fin d) (Fin d) (ZMod (p ^ e))).trace
    with ht
  push_cast
  calc ∑ i, (c i : ZMod (p ^ e)) * (Nat.card (B i) : ZMod (p ^ e)) *
        (finrank (ZMod p) (glFixedSpace ρ (B i)) : ZMod (p ^ e))
      = ∑ i, (c i : ZMod (p ^ e)) * ∑ b : B i, t (b : A) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, sum_trace_eq_natCard_mul_finrank_glFixedSpace hp
          (Nat.one_le_iff_ne_zero.1 he) hA ρ ρe hρe (B i)]
    _ = ∑ a : A, (∑ i with a ∈ B i, ((c i : ZMod (p ^ e)))) * t a :=
        sum_weighted_sum_subgroup B _ t
    _ = 0 := by
        refine Finset.sum_eq_zero fun a _ => ?_
        have : ∑ i with a ∈ B i, ((c i : ZMod (p ^ e))) = ((0 : ℤ) : ZMod (p ^ e)) := by
          rw [← hc a]; push_cast; rfl
        rw [this, Int.cast_zero, zero_mul]

theorem pow_dvd_sum_weighted_natCard_mul_finrank_glFixedSpace [Finite A]
    (hp : p.Prime) (hA : ¬ p ∣ Nat.card A) (ρ : A →* GL (Fin d) (ZMod p))
    (B : ι → Subgroup A) [∀ i, DecidablePred (· ∈ B i)] (c : ι → ℤ)
    (hc : ∀ a : A, ∑ i with a ∈ B i, c i = 0) {e : ℕ} (he : 1 ≤ e) :
    (p : ℤ) ^ e ∣ ∑ i, c i * (Nat.card (B i) : ℤ) *
      (finrank (ZMod p) (glFixedSpace ρ (B i)) : ℤ) := by
  rw [show ((p : ℤ) ^ e) = ((p ^ e : ℕ) : ℤ) by push_cast; ring,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact sum_weighted_natCard_mul_finrank_glFixedSpace_zmod_eq_zero hp hA ρ B c hc he

end Congruence

end CFSG.FeitThompson
