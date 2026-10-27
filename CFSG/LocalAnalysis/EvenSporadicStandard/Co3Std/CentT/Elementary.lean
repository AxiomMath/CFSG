module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup

theorem le_of_orderOf_eq_two_pow {n k : ℕ} (hk : 0 < k) {σ : Equiv.Perm (Fin n)}
    (h : orderOf σ = 2 ^ k) : 2 ^ k ≤ n := by
  have hne : σ ^ (2 ^ (k - 1)) ≠ 1 := by
    intro hc
    have hdvd : orderOf σ ∣ 2 ^ (k - 1) := orderOf_dvd_iff_pow_eq_one.mpr hc
    rw [h] at hdvd
    have hle := Nat.le_of_dvd (by positivity) hdvd
    have hlt : 2 ^ (k - 1) < 2 ^ k :=
      Nat.pow_lt_pow_right (by norm_num) (Nat.sub_lt hk (by norm_num))
    omega
  obtain ⟨x, hx⟩ : ∃ x : Fin n, (σ ^ (2 ^ (k - 1))) x ≠ x := by
    by_contra h
    push_neg at h
    exact hne (Equiv.ext fun x => by simp [h x])
  have hx' : σ^[2 ^ (k - 1)] x ≠ x := by
    simpa [Equiv.Perm.coe_pow] using hx
  have hper : Function.IsPeriodicPt σ (orderOf σ) x := by
    show σ^[orderOf σ] x = x
    rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
    rfl
  have hdvd : Function.minimalPeriod σ x ∣ 2 ^ k := by
    rw [← h]
    exact Function.IsPeriodicPt.minimalPeriod_dvd hper
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hjk : j = k := by
    by_contra hjk
    have hlt : j < k := lt_of_le_of_ne hjle hjk
    have hdvd' : Function.minimalPeriod σ x ∣ 2 ^ (k - 1) := by
      rw [hj]
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mpr (by omega)
    have hper' : Function.IsPeriodicPt σ (2 ^ (k - 1)) x :=
      Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr hdvd'
    exact hx' hper'
  rw [hjk] at hj
  have hle : Function.minimalPeriod σ x ≤ n := by
    simpa using Function.minimalPeriod_le_card (f := σ) (x := x)
  rw [hj] at hle
  exact hle

theorem lt_relIndex_of_perm {E : Type} [Group E] [Finite E] {n : ℕ} (f : E →* Equiv.Perm (Fin n))
    (hf : Function.Injective f) {S : Subgroup E} {k : ℕ} (hk : 2 ≤ k) (hS : Nat.card S = 2 ^ k)
    (hn : n < 2 ^ (k - 1)) : ∀ M : Subgroup E, M ≤ S → IsCyclic ↥M → 2 < M.relIndex S := by
  intro M hMS hcyc
  by_contra hle
  push_neg at hle
  have hcardS : M.relIndex S * Nat.card M = 2 ^ k := by
    have h1 := Subgroup.relIndex_mul_card M S
    rwa [inf_of_le_left hMS, hS] at h1
  have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hkpos : 0 < k := by omega
    conv_lhs => rw [show k = (k - 1) + 1 from (Nat.sub_one_add_one_eq_of_pos hkpos).symm]
    rw [Nat.pow_succ']
  have hcardM_ge : 2 ^ (k - 1) ≤ Nat.card M := by
    have h1 : 2 * 2 ^ (k - 1) ≤ 2 * Nat.card M := by
      rw [← h2k]
      calc 2 ^ k = M.relIndex S * Nat.card M := hcardS.symm
        _ ≤ 2 * Nat.card M := Nat.mul_le_mul_right _ hle
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥M)
  have horder_g : orderOf g = Nat.card M := orderOf_eq_card_of_forall_mem_zpowers hg
  have horder_gE : orderOf (g : E) = orderOf g := Subgroup.orderOf_coe g
  have hdiv : orderOf (g : E) ∣ 2 ^ k := by
    rw [← hS]
    exact Subgroup.orderOf_dvd_natCard S (hMS g.2)
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hpow_le : 2 ^ (k - 1) ≤ 2 ^ j := by
    calc 2 ^ (k - 1) ≤ Nat.card M := hcardM_ge
      _ = orderOf g := horder_g.symm
      _ = orderOf (g : E) := horder_gE.symm
      _ = 2 ^ j := hj
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, pow_zero] at hpow_le
      have htwo : 2 ≤ 2 ^ (k - 1) := by
        calc 2 = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact hjpos
  have horder_fg : orderOf (f (g : E)) = 2 ^ j := by
    rw [orderOf_injective f hf (g : E), hj]
  have hle_n : 2 ^ j ≤ n := le_of_orderOf_eq_two_pow hjpos horder_fg
  omega

theorem hom_eq_one_of_normal_small {N : Type} [Group N] [Finite N] {c m : ℕ}
    (hprop : ∀ K : Subgroup N, K.Normal → K ≠ ⊤ → Nat.card K ≤ c) (hbig : c * m < Nat.card N)
    (R : Type) [Group R] [Finite R] (hR : Nat.card R ≤ m) (f : N →* R) : f = 1 := by
  rw [← MonoidHom.ker_eq_top_iff (f := f)]
  by_contra hne
  have hkercard : Nat.card f.ker ≤ c := hprop f.ker inferInstance hne
  have hrange : Nat.card f.range ≤ m := by
    have h1 : Nat.card f.range ≤ Nat.card R :=
      Nat.card_le_card_of_injective f.range.subtype (Subgroup.subtype_injective f.range)
    exact h1.trans hR
  have hcard : Nat.card N = Nat.card f.ker * Nat.card f.range :=
    (Subgroup.card_ker_mul_card_range f).symm
  have hle : Nat.card N ≤ c * m := by
    rw [hcard]
    exact Nat.mul_le_mul hkercard hrange
  omega

theorem le_of_normal_of_card_gt {D : Type} [Group D] [Finite D] {N M : Subgroup D} [N.Normal]
    [M.Normal] {c : ℕ}
    (hprop : ∀ K : Subgroup D, K ≤ N → (K.subgroupOf N).Normal → K ≠ N → Nat.card K ≤ c)
    (hcard : N.index * c < Nat.card M) : N ≤ M := by
  by_contra hNM
  have hKnormal : ((M ⊓ N).subgroupOf N).Normal := by
    rw [Subgroup.inf_subgroupOf_right M N]
    exact (inferInstance : M.Normal).subgroupOf N
  have hKne : M ⊓ N ≠ N := by
    intro h
    exact hNM (h ▸ inf_le_left)
  have hKcard : Nat.card (M ⊓ N : Subgroup D) ≤ c := hprop (M ⊓ N) inf_le_right hKnormal hKne
  have hrelN : N.relIndex M ≤ N.index := by
    simpa [Subgroup.relIndex_top_right] using
      Subgroup.relIndex_le_of_le_right (H := N) (K := M) (L := ⊤) le_top
        (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite (H := N))
  have hMle : Nat.card M ≤ N.index * Nat.card (M ⊓ N : Subgroup D) := by
    have h1 : N.relIndex M * Nat.card (M ⊓ N : Subgroup D) = Nat.card M := by
      have := Subgroup.relIndex_mul_card N M
      rwa [inf_comm] at this
    rw [← h1]
    exact Nat.mul_le_mul_right _ hrelN
  have h2 : N.index * Nat.card (M ⊓ N : Subgroup D) ≤ N.index * c := Nat.mul_le_mul_left _ hKcard
  exact absurd (lt_of_le_of_lt (le_trans hMle h2) hcard) (lt_irrefl _)

end CFSG.EvenSporadicStandard.Co3Std.CentT
