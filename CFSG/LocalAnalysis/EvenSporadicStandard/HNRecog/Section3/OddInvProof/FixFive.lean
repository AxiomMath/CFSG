module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma oddInvFive_conj_iterate_apply {K : Type*} [Group K] (σ q : K) (n : ℕ) :
    (fun a : K => σ * a * σ⁻¹)^[n] q = σ ^ n * q * (σ ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      group

theorem oddInv_exists_fixed_conj {K : Type*} [Group K] [Finite K] (Q : Subgroup K) [Q.Normal]
    {c σ : K} (hσ : σ ^ 5 = 1)
    (hcomm : (σ : K ⧸ Q) * (c : K ⧸ Q) = (c : K ⧸ Q) * (σ : K ⧸ Q))
    (hF : ¬ 5 ∣ Nat.card {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q)}) :
    ∃ s : K, (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q) ∧ σ * s = s * σ := by
  classical
  let F := {s : K // (∃ k : K, k * c * k⁻¹ = s) ∧ (s : K ⧸ Q) = (c : K ⧸ Q)}
  haveI : Fintype F := Fintype.ofFinite F
  let f : Function.End F := fun s =>
    ⟨σ * s.1 * σ⁻¹, by
      obtain ⟨k, hk⟩ := s.2.1
      exact ⟨⟨σ * k, by rw [← hk]; group⟩, by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          s.2.2, hcomm]
        group⟩⟩
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    have hiter : ∀ n : ℕ, (f^[n] s).1 = (fun a : K => σ * a * σ⁻¹)^[n] s.1 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
          rw [Function.iterate_succ_apply']
          change σ * (f^[n] s).1 * σ⁻¹ = (fun a : K => σ * a * σ⁻¹)^[n + 1] s.1
          rw [Function.iterate_succ_apply', ih]
    show (f^[5] s).1 = s.1
    rw [hiter 5, oddInvFive_conj_iterate_apply, hσ]
    group
  by_contra hcon
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) (n := 1) hf5
  have hfixempty : Function.fixedPoints f = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro s hs
    refine hcon ⟨s.1, s.2.1, s.2.2, ?_⟩
    have hsval : σ * s.1 * σ⁻¹ = s.1 := by
      have h : (f s).1 = s.1 := congrArg Subtype.val hs
      exact h
    calc σ * s.1 = σ * s.1 * σ⁻¹ * σ := by group
      _ = s.1 * σ := by rw [hsval]
  have hmod0 : Fintype.card F ≡ 0 [MOD 5] := by
    simpa [hfixempty] using hmod
  exact hF (by
    rw [Nat.card_eq_fintype_card]
    exact Nat.modEq_zero_iff_dvd.mp hmod0)

end CFSG.EvenSporadicStandard.HNRecog.Section3
