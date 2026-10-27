module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Perm
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank

public section

namespace GL83.PiGen

open Equiv Equiv.Perm MulAction CFSG.Open GL83.CompFam

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {p : ℕ} [Fact p.Prime]

theorem card_le_orbit_bound {R : Subgroup (Perm Ω)} (hR : IsElemAbelian p R) (ω : Ω) {s : ℕ}
    (hs : Nat.card (orbit R ω) = p ^ s) :
    Nat.card R ≤ p ^ s * p ^ ((Fintype.card Ω - p ^ s) / p) := by
  classical
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy => elem_comm hR hx hy
  have hRpg : IsPGroup p R := GL83.CompFam.isPGroup_of_elem hR
  set O : Finset Ω := (Set.toFinite (orbit R ω)).toFinset with hO
  have hOcard : O.card = p ^ s := by
    rw [← hs, Nat.card_eq_card_finite_toFinset (Set.toFinite (orbit R ω))]
  have hfix : ∀ g ∈ stabIn R ω, ∀ a ∉ (Finset.univ \ O : Finset Ω), g a = a := by
    intro g hg a ha
    have haO : a ∈ O := by
      by_contra h
      exact ha (by simp [h])
    obtain ⟨h, rfl⟩ := mem_orbit_iff.1 ((Set.Finite.mem_toFinset _).1 haO)
    have hga : g ω = ω := mem_fixSet_stabIn R ω g hg
    simp only [Subgroup.smul_def, Perm.smul_def]
    exact CFSG.AGLEmbedding.apply_apply_eq_of_commute hcomm (stabIn_le R ω hg) h.2 hga
  have hstab : Nat.card (stabIn R ω) ≤ p ^ ((Fintype.card Ω - p ^ s) / p) := by
    have hle := CFSG.AGLEmbedding.card_le_pow_of_forall_apply_eq (p := p) (Fintype.card Ω)
      (Finset.univ \ O) (by simpa using Finset.card_le_univ (Finset.univ \ O)) (stabIn R ω)
      (fun x hx y hy => hcomm x (stabIn_le R ω hx) y (stabIn_le R ω hy))
      (hRpg.to_le (stabIn_le R ω)) hfix
    rwa [Finset.card_sdiff_of_subset (Finset.subset_univ O), Finset.card_univ, hOcard] at hle
  rw [card_mul_card_stabIn R ω, hs]
  exact Nat.mul_le_mul_left _ hstab

theorem rank_add_pow_le {R : Subgroup (Perm Ω)} (hR : IsElemAbelian p R) (ω : Ω) {k s r : ℕ}
    (hn : Fintype.card Ω = k * p + 2) (hp3 : 3 ≤ p) (hs : 1 ≤ s)
    (horb : Nat.card (orbit R ω) = p ^ s) (hr : Nat.card R = p ^ r) : r + p ^ (s - 1) ≤ k + s := by
  have hp := (Fact.out : p.Prime)
  have hb := card_le_orbit_bound hR ω horb
  rw [hr] at hb
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hsn : p ^ (s' + 1) ≤ Fintype.card Ω := by
    rw [← horb]
    have h := Nat.card_le_card_of_injective (Subtype.val : (orbit R ω) → Ω) Subtype.val_injective
    rwa [Nat.card_eq_fintype_card (α := Ω)] at h
  set q := p ^ s' with hq
  have hpq : p ^ (s' + 1) = p * q := by rw [pow_succ, mul_comm]
  have hqk : q ≤ k := by
    by_contra hlt
    have : p * (k + 1) ≤ p * q := Nat.mul_le_mul_left _ (by omega)
    rw [hpq] at hsn
    nlinarith
  have hdiv : (Fintype.card Ω - p ^ (s' + 1)) / p = k - q := by
    rw [hpq, hn]
    have h1 : k * p + 2 - p * q = p * (k - q) + 2 := by
      rw [Nat.mul_sub, mul_comm k p]
      have : p * q ≤ p * k := Nat.mul_le_mul_left _ hqk
      omega
    rw [h1, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega)]
    simp
  rw [hdiv, ← pow_add] at hb
  have := (Nat.pow_le_pow_iff_right hp.one_lt).1 hb
  simp only [Nat.add_sub_cancel]
  omega

section Arith

theorem three_pow_ge (m : ℕ) (hm : 1 ≤ m) : m + 2 ≤ 3 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · norm_num
    · have := ih hm'
      rw [pow_succ]
      omega

theorem five_pow_ge (m : ℕ) (hm : 1 ≤ m) : m + 4 ≤ 5 ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · norm_num
    · have := ih hm'
      rw [pow_succ]
      omega

theorem two_mul_add_one_le_three_pow (a : ℕ) : 2 * a + 1 ≤ 3 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih => rw [pow_succ]; omega

theorem four_mul_add_one_le_five_pow (a : ℕ) : 4 * a + 1 ≤ 5 ^ a := by
  induction a with
  | zero => norm_num
  | succ a ih => rw [pow_succ]; omega

theorem no_big_orbit_arith {p k a r s : ℕ} (hp : p = 3 ∨ 5 ≤ p) (hk : 2 ≤ k) (hr : r ≤ k)
    (hs : 2 ≤ s) (hstar : ((k - 1) + (if p = 3 then 1 else 0)) * p ^ a ≤ a + r)
    (hP : r + p ^ (s - 1) ≤ k + s) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hstar
  rcases hp with rfl | hp5
  · simp only [ite_true] at hstar
    have h1 := three_pow_ge (s - 1) (by omega)
    have h3 := two_mul_add_one_le_three_pow a
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp at hstar
      omega
    · have : (m + 1) * (2 * a + 1) ≤ (m + 1) * 3 ^ a := Nat.mul_le_mul_left _ h3
      nlinarith
  · have hp3 : p ≠ 3 := by omega
    simp only [hp3, ite_false, add_zero] at hstar
    have h1 : s - 1 + 4 ≤ p ^ (s - 1) := by
      have := five_pow_ge (s - 1) (by omega)
      have h5 : 5 ^ (s - 1) ≤ p ^ (s - 1) := Nat.pow_le_pow_left hp5 _
      omega
    have h3 : 4 * a + 1 ≤ p ^ a := by
      have h5 := four_mul_add_one_le_five_pow a
      have h6 : 5 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp5 _
      omega
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp at hstar
      omega
    · have hm1 : 1 ≤ m := by omega
      have : m * (4 * a + 1) ≤ m * p ^ a := Nat.mul_le_mul_left _ h3
      nlinarith

end Arith

end GL83.PiGen
