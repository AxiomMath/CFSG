module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltHH
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55N1

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResHH

open Equiv Equiv.Perm Subgroup

theorem cycleType_of_orderOf_three {n : ℕ} (hn : n ≤ 7) {σ : Perm (Fin n)}
    (hσ : orderOf σ = 3) : ∃ k : ℕ, (k = 1 ∨ k = 2) ∧ σ.cycleType = Multiset.replicate k 3 := by
  have hall : ∀ m ∈ σ.cycleType, m = 3 := by
    intro m hm
    have h1 := dvd_of_mem_cycleType hm
    rw [hσ] at h1
    have h2 := two_le_of_mem_cycleType hm
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · omega
    · exact h
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum := sum_cycleType_le σ
  rw [hrep, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hne : σ.cycleType ≠ 0 := by
    rw [Ne, cycleType_eq_zero]
    rintro rfl
    rw [orderOf_one] at hσ
    omega
  have hc1 : Multiset.card σ.cycleType ≠ 0 := fun h => hne (Multiset.card_eq_zero.mp h)
  exact ⟨_, by omega, hrep⟩

theorem mem_alt_swap_mul_swap {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    swap a b * swap c d ∈ alternatingGroup (Fin n) := by
  rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  rfl

theorem std_config {n : ℕ} (hn : n = 6 ∨ n = 7) {k : ℕ} (hk : k = 1 ∨ k = 2) :
    ∃ c₀ u₁ u₂ : Perm (Fin n), c₀.cycleType = Multiset.replicate k 3 ∧
      u₁ ∈ alternatingGroup (Fin n) ∧ u₂ ∈ alternatingGroup (Fin n) ∧ u₁ * u₁ = 1 ∧
      u₂ * u₂ = 1 ∧ u₁ * u₂ = u₂ * u₁ ∧ c₀ * u₁ * c₀⁻¹ = u₂ ∧ c₀ * u₂ * c₀⁻¹ = u₁ * u₂ ∧
      u₂ ≠ u₁ := by
  rcases hn with rfl | rfl <;> rcases hk with rfl | rfl
  · refine ⟨swap 0 1 * swap 0 2, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
      (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType,
      mem_alt_swap_mul_swap (by decide) (by decide), mem_alt_swap_mul_swap (by decide)
        (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · refine ⟨(swap 0 1 * swap 0 2) * (swap 3 4 * swap 3 5), swap 0 3 * swap 1 4,
      swap 0 3 * swap 2 5, ?_, mem_alt_swap_mul_swap (by decide) (by decide),
      mem_alt_swap_mul_swap (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide),
        (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType,
        (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType]
      rfl
    all_goals decide
  · refine ⟨swap 0 1 * swap 0 2, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
      (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType,
      mem_alt_swap_mul_swap (by decide) (by decide), mem_alt_swap_mul_swap (by decide)
        (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide
  · refine ⟨(swap 0 1 * swap 0 2) * (swap 3 4 * swap 3 5), swap 0 3 * swap 1 4,
      swap 0 3 * swap 2 5, ?_, mem_alt_swap_mul_swap (by decide) (by decide),
      mem_alt_swap_mul_swap (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Disjoint.cycleType_mul (by unfold Perm.Disjoint; decide),
        (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType,
        (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).cycleType]
      rfl
    all_goals decide

theorem klein_of_orderOf_three {n : ℕ} (hn : n = 6 ∨ n = 7) {σ : Perm (Fin n)}
    (hσ : orderOf σ = 3) :
    ∃ Q : Subgroup (Perm (Fin n)), Q ≤ alternatingGroup (Fin n) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ (∀ x ∈ Q, x * x = 1) ∧
      (∀ x ∈ Q, σ * x * σ⁻¹ ∈ Q) ∧ ∃ x ∈ Q, σ * x * σ⁻¹ ≠ x := by
  obtain ⟨k, hk, hct⟩ := cycleType_of_orderOf_three (by omega) hσ
  obtain ⟨c₀, u₁, u₂, hc₀, hu₁A, hu₂A, h11, h22, hcomm, hcu1, hcu2, hne⟩ := std_config hn hk
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_iff_cycleType_eq.2 (hc₀.trans hct.symm))
  have hσ' : σ = g * c₀ * g⁻¹ := hg.symm
  have hconj : ∀ x : Perm (Fin n), σ * (g * x * g⁻¹) * σ⁻¹ = g * (c₀ * x * c₀⁻¹) * g⁻¹ := by
    intro x
    rw [hσ']
    group
  have hA : ∀ {u : Perm (Fin n)}, u ∈ alternatingGroup (Fin n) →
      g * u * g⁻¹ ∈ alternatingGroup (Fin n) :=
    fun hu => Subgroup.Normal.conj_mem inferInstance _ hu g
  obtain ⟨Q, hQA, hQc, hQe, hQn, x, hxQ, hxn⟩ :=
    AltHH.klein_abstract (alternatingGroup (Fin n)) (hA hu₁A) (hA hu₂A)
      (by rw [show g * u₁ * g⁻¹ * (g * u₁ * g⁻¹) = g * (u₁ * u₁) * g⁻¹ by group, h11]; group)
      (by rw [show g * u₂ * g⁻¹ * (g * u₂ * g⁻¹) = g * (u₂ * u₂) * g⁻¹ by group, h22]; group)
      (by
        rw [show g * u₁ * g⁻¹ * (g * u₂ * g⁻¹) = g * (u₁ * u₂) * g⁻¹ by group, hcomm]
        group)
      (by rw [hconj, hcu1])
      (by
        rw [hconj, hcu2]
        group)
      (fun h => hne (mul_left_cancel (mul_right_cancel h)))
  exact ⟨Q, hQA, hQc, hQe, hQn, x, hxQ, hxn⟩

theorem hhobsAt_of_perm {Y : Type} [Group Y] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : Y ≃* alternatingGroup (Fin n)) (b : MulAut Y) {σ : Perm (Fin n)} (hσ : orderOf σ = 3)
    (hb : ∀ y : Y, ((e (b y) : alternatingGroup (Fin n)) : Perm (Fin n)) =
      σ * ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) * σ⁻¹) :
    HHObsAt 3 2 Y b := by
  obtain ⟨Q, hQA, hQc, hQe, hQn, q, hqQ, hqn⟩ := klein_of_orderOf_three hn hσ
  let E : Subgroup Y := Q.comap (((alternatingGroup (Fin n)).subtype).comp e.toMonoidHom)
  have hmemE : ∀ y, y ∈ E ↔ ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ Q :=
    fun y => Iff.rfl
  refine ⟨Nat.prime_two, by norm_num, E, ?_, fun _ x hx y hy => ?_, fun x hx => ?_, ?_⟩
  · refine IsPGroup.iff_orderOf.2 fun g => ?_
    have hg2 : g * g = 1 := by
      apply Subtype.ext
      apply e.injective
      apply Subtype.ext
      have := hQe _ g.2
      simpa using this
    have hord : orderOf g ∣ 2 ^ 1 := by
      have := orderOf_dvd_of_pow_eq_one (x := g) (n := 2) (by rw [pow_two]; exact hg2)
      simpa using this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact ⟨k, hk⟩
  · have := hQc _ hx _ hy
    apply e.injective
    apply Subtype.ext
    simpa using this
  · rw [hmemE, hb x]
    exact hQn _ hx
  · obtain ⟨x, hx⟩ := e.surjective ⟨q, hQA hqQ⟩
    refine ⟨x, ?_, ?_⟩
    · rw [hmemE, hx]
      exact hqQ
    · intro h
      apply hqn
      have h1 := hb x
      rw [h, hx] at h1
      exact h1.symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.ResHH
