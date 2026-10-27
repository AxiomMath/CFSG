module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.A6Cent
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem normalizer_le_of_a6 {N : Type*} [Group N] (e : N ≃* alternatingGroup (Fin 6))
    {P : Subgroup N} (hP : Nat.card P = 8) (hAut : IsPGroup 2 (MulAut ↥P)) :
    normalizer (P : Set N) ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite N := Finite.of_equiv _ e.symm.toEquiv
  have h2 : IsPGroup 2 (normalizer (P : Set N)) := by
    intro g
    obtain ⟨k, hk⟩ := hAut (P.normalizerMonoidHom g)
    rw [← map_pow] at hk
    refine ⟨k + 1, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a : normalizer (P : Set N), a = g ^ 2 ^ k := ⟨_, rfl⟩
    rw [← ha] at hk
    have hc : ∀ x ∈ P, (a : N) * x = x * (a : N) := by
      intro x hx
      have h1 := congrArg (fun f : MulAut ↥P => ((f ⟨x, hx⟩ : ↥P) : N)) hk
      simp at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    have hsq := sq_eq_one_of_comm_order_eight e P hP _ hc
    apply Subtype.ext
    have : (a : N) = (g : N) ^ 2 ^ k := by rw [ha]; rfl
    rw [this] at hsq
    simpa [pow_succ, pow_mul] using hsq
  have hcard : Nat.card (normalizer (P : Set N)) ∣ 360 := by
    have h1 := Subgroup.card_subgroup_dvd_card (normalizer (P : Set N))
    have h3 : Nat.card N = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rwa [h3] at h1
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    rw [← hn] at h16
    have := h16.trans hcard
    norm_num at this
  have hle : Nat.card (normalizer (P : Set N)) ≤ 8 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
      _ = 8 := by norm_num
  have hPle : P ≤ normalizer (P : Set N) := Subgroup.le_normalizer
  exact (Subgroup.eq_of_le_of_card_ge hPle (by rw [hP]; exact hle)).ge

end CFSG.EvenSporadicStandard.Fin76b
