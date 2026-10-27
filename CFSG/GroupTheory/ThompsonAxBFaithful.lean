module

public import Mathlib.GroupTheory.PGroup
import CFSG.GroupTheory.ThompsonAxB

public section

namespace CFSG.GroupTheory

theorem eq_one_of_forall_fixed_of_coprime {W : Type*} [Group W] [Finite W] {p : ℕ} [Fact p.Prime]
    (hW : IsPGroup p W) {A : Subgroup (MulAut W)} (hA : IsPGroup p A) {b : MulAut W}
    (hbp : Nat.Coprime (orderOf b) p) (hAb : ∀ a ∈ A, a * b = b * a)
    (hfix : ∀ w : W, (∀ a ∈ A, a w = w) → b w = w) : b = 1 := by
  have hcard : ¬ p ∣ Nat.card (Subgroup.zpowers b) := by
    rw [Nat.card_zpowers]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp
      (Nat.coprime_comm.mp hbp)
  have hcomm : ∀ (a : Subgroup.zpowers b) (b' : A),
      (Subgroup.zpowers b).subtype a * A.subtype b' = A.subtype b' * (Subgroup.zpowers b).subtype a := by
    intro a b'
    have hb' : b ∈ Subgroup.centralizer ({(b' : MulAut W)} : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hAb b' b'.2
    have ha := (Subgroup.zpowers_le.mpr hb') a.2
    have h := Subgroup.mem_centralizer_iff.mp ha (b' : MulAut W) (Set.mem_singleton _)
    simpa using h.symm
  have hfix' : ∀ (a : Subgroup.zpowers b) (r : W),
      (∀ b' : A, A.subtype b' r = r) → (Subgroup.zpowers b).subtype a r = r := by
    intro a r hr
    have hrA : ∀ a' ∈ A, a' r = r := fun a' ha' => hr ⟨a', ha'⟩
    have hbw : b ∈ MulAction.stabilizer (MulAut W) r :=
      MulAction.mem_stabilizer_iff.mpr (hfix r hrA)
    have ha := Subgroup.zpowers_le.mpr hbw a.2
    simpa [MulAut.smul_def] using (MulAction.mem_stabilizer_iff.mp ha)
  have hthom := thompson_A_times_B hW hcard hA (Subgroup.zpowers b).subtype A.subtype hcomm hfix'
  have hb1 : (Subgroup.zpowers b).subtype ⟨b, Subgroup.mem_zpowers b⟩ = 1 := hthom _
  simpa using hb1

theorem eq_one_of_forall_fixed_of_commute {W : Type*} [Group W] [Finite W] {p : ℕ} [Fact p.Prime]
    (hW : IsPGroup p W) {A B : Subgroup (MulAut W)} (hA : IsPGroup p A)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hB : ∀ N : Subgroup (MulAut W), N ≤ B → (N.subgroupOf B).Normal → IsPGroup p N → N = ⊥)
    {b : MulAut W} (hb : b ∈ B) (hfix : ∀ w : W, (∀ a ∈ A, a w = w) → b w = w) : b = 1 := by
  let K : Subgroup (MulAut W) :=
    { carrier := {k | k ∈ B ∧ ∀ w : W, (∀ a ∈ A, a w = w) → k w = w}
      mul_mem' := by
        rintro x y ⟨hxB, hx⟩ ⟨hyB, hy⟩
        exact ⟨B.mul_mem hxB hyB, fun w hw => by
          rw [MulAut.mul_apply, hy w hw, hx w hw]⟩
      one_mem' := ⟨B.one_mem, fun w _ => by rw [MulAut.one_apply]⟩
      inv_mem' := by
        rintro x ⟨hxB, hx⟩
        refine ⟨B.inv_mem hxB, fun w hw => ?_⟩
        calc x⁻¹ w = x⁻¹ (x w) := by rw [hx w hw]
          _ = (x⁻¹ * x) w := rfl
          _ = w := by rw [inv_mul_cancel, MulAut.one_apply] }
  have hKB : K ≤ B := fun x hx => hx.1
  have hKnormal : (K.subgroupOf B).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKB]
    intro x c hx hc
    refine ⟨B.mul_mem (B.mul_mem hc hx.1) (B.inv_mem hc), fun w hw => ?_⟩
    have hcw : ∀ a ∈ A, a (c⁻¹ w) = c⁻¹ w := by
      intro a ha
      have hac : Commute a c := hAB a ha c hc
      calc a (c⁻¹ w) = (a * c⁻¹) w := rfl
        _ = (c⁻¹ * a) w := by rw [hac.inv_right.eq]
        _ = c⁻¹ (a w) := rfl
        _ = c⁻¹ w := by rw [hw a ha]
    simp only [MulAut.mul_apply]
    rw [hx.2 (c⁻¹ w) hcw]
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hKp : IsPGroup p K := by
    rw [isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero]
    intro q hq
    obtain ⟨hqprime, hqdvdcard, -⟩ := Nat.mem_primeFactors.mp hq
    haveI : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q hqdvdcard
    have hqeqp : q = p := by
      by_contra hne
      have hcop : Nat.Coprime (orderOf ((g : K) : MulAut W)) p := by
        rw [Subgroup.orderOf_coe, hg]
        exact (Nat.coprime_primes hqprime (Fact.out : p.Prime)).mpr hne
      have hcommg : ∀ a ∈ A, a * ((g : K) : MulAut W) = ((g : K) : MulAut W) * a :=
        fun a ha => hAB a ha _ g.2.1
      have hfixg : ∀ w : W, (∀ a ∈ A, a w = w) → ((g : K) : MulAut W) w = w :=
        fun w hw => g.2.2 w hw
      have hg1 : ((g : K) : MulAut W) = 1 :=
        eq_one_of_forall_fixed_of_coprime hW hA hcop hcommg hfixg
      have hg1' : g = 1 := Subtype.ext (by simpa using hg1)
      have hord : orderOf g = 1 := by rw [hg1', orderOf_one]
      rw [hg] at hord
      exact hqprime.one_lt.ne' hord
    rw [hqeqp]
    exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
  have hKbot : K = ⊥ := hB K hKB hKnormal hKp
  have hbK : b ∈ K := ⟨hb, hfix⟩
  have : b ∈ (⊥ : Subgroup (MulAut W)) := hKbot ▸ hbK
  simpa using this

end CFSG.GroupTheory
