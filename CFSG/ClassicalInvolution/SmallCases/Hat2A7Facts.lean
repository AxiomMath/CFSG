module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7FactsInputs
public import Certificates.Certificate9300
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open Equiv Equiv.Perm

section Dihedral

variable {G : Type*} [Group G] {s t : G}

private theorem sa_eq (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ 4 = 1) :
    s * (s * t) = (s * t) ^ 3 * s := by
  have h3 : (s * t) ^ 3 = t * s := by
    have h4 : (s * t) ^ 3 * (s * t) = 1 := by rw [← pow_succ]; exact hst
    have h5 : (t * s) * (s * t) = 1 := by
      calc (t * s) * (s * t) = t * (s * s) * t := by group
        _ = 1 := by rw [hs, mul_one]; exact ht
    exact mul_right_cancel (h4.trans h5.symm)
  rw [h3]
  calc s * (s * t) = (s * s) * t := by group
    _ = t := by rw [hs, one_mul]
    _ = t * (s * s) := by rw [hs, mul_one]
    _ = t * s * s := by group

theorem card_closure_pair_le_eight (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ 4 = 1) :
    Nat.card (Subgroup.closure ({s, t} : Set G)) ≤ 8 := by
  set a : G := s * t with ha
  have ha4 : a ^ 4 = 1 := hst
  have hs2 : s ^ 2 = 1 := by rw [pow_two]; exact hs
  have hsa : s * a = a ^ 3 * s := sa_eq hs ht hst
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ha_inv : a⁻¹ = a ^ 3 := by
    have : a * a ^ 3 = 1 := by rw [← pow_succ']; exact ha4
    exact inv_eq_of_mul_eq_one_right this
  let T : Set G := Set.range fun p : Fin 4 × Fin 2 => a ^ (p.1 : ℕ) * s ^ (p.2 : ℕ)
  have hmem : ∀ m j : ℕ, a ^ m * s ^ j ∈ T := by
    intro m j
    refine ⟨(⟨m % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    simp only
    rw [← pow_eq_pow_mod m ha4, ← pow_eq_pow_mod j hs2]
  have hsapow : ∀ i : ℕ, s * a ^ i = a ^ (3 * i) * s := by
    intro i
    induction i with
    | zero => simp
    | succ n ih =>
      calc s * a ^ (n + 1) = (s * a ^ n) * a := by rw [pow_succ]; group
        _ = a ^ (3 * n) * (s * a) := by rw [ih]; group
        _ = a ^ (3 * n) * (a ^ 3 * s) := by rw [hsa]
        _ = a ^ (3 * (n + 1)) * s := by rw [← mul_assoc, ← pow_add]; congr 2
  have hleft_s : ∀ y ∈ T, s * y ∈ T := by
    rintro y ⟨⟨i, j⟩, rfl⟩
    simp only
    have := hmem (3 * (i : ℕ)) ((j : ℕ) + 1)
    have e : s * (a ^ (i : ℕ) * s ^ (j : ℕ)) = a ^ (3 * (i : ℕ)) * s ^ ((j : ℕ) + 1) := by
      rw [← mul_assoc, hsapow, mul_assoc, ← pow_succ']
    rw [e]
    exact this
  have hleft_a : ∀ y ∈ T, a * y ∈ T := by
    rintro y ⟨⟨i, j⟩, rfl⟩
    simp only
    have := hmem ((i : ℕ) + 1) (j : ℕ)
    convert this using 1
    rw [pow_succ']
    group
  have hleft_spow : ∀ n : ℕ, ∀ y ∈ T, s ^ n * y ∈ T := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hleft_s _ (ih y hy)
  have hleft_apow : ∀ n : ℕ, ∀ y ∈ T, a ^ n * y ∈ T := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hleft_a _ (ih y hy)
  have hone : (1 : G) ∈ T := ⟨(0, 0), by simp⟩
  have hsub : (Subgroup.closure ({s, t} : Set G) : Set G) ⊆ T := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨(0, 1), by simp⟩
      · have h1 : s * a = x := by rw [ha, ← mul_assoc, hs, one_mul]
        have := hleft_s a ⟨(1, 0), by simp⟩
        rwa [h1] at this
    | one => exact hone
    | mul x y _ _ hx hy =>
      obtain ⟨⟨i, j⟩, rfl⟩ := hx
      simp only
      rw [mul_assoc]
      exact hleft_apow _ _ (hleft_spow _ _ hy)
    | inv x _ hx =>
      obtain ⟨⟨i, j⟩, rfl⟩ := hx
      simp only
      have h1 : (a ^ (i : ℕ) * s ^ (j : ℕ))⁻¹ = s ^ (j : ℕ) * a ^ (3 * (i : ℕ)) := by
        rw [mul_inv_rev, ← inv_pow, ← inv_pow, hs_inv, ha_inv, ← pow_mul]
      rw [h1]
      exact hleft_spow _ _ (by simpa using hmem (3 * (i : ℕ)) 0)
  calc Nat.card (Subgroup.closure ({s, t} : Set G))
      = Nat.card ((Subgroup.closure ({s, t} : Set G) : Set G)) := rfl
    _ ≤ Nat.card T := Nat.card_mono (Set.finite_range _) hsub
    _ ≤ Nat.card (Fin 4 × Fin 2) := Finite.card_range_le _
    _ = 8 := by simp

end Dihedral

@[expose] def D8 : Subgroup A7 := Subgroup.closure {sD, tD}

theorem sD_mem_D8 : sD ∈ D8 := Subgroup.subset_closure (by simp)

theorem tD_mem_D8 : tD ∈ D8 := Subgroup.subset_closure (by simp)

theorem dihedral_rel : sD * sD = 1 ∧ tD * tD = 1 ∧ (sD * tD) ^ 4 = 1 ∧ (sD * tD) ^ 2 ≠ 1 := by
  decide

theorem pow_ne_sD : ∀ i : Fin 4, (sD * tD) ^ (i : ℕ) ≠ sD := by
  decide

theorem orderOf_sD_mul_tD : orderOf (sD * tD) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨dihedral_rel.2.2.1, fun m hm hm0 => ?_⟩
  interval_cases m
  · decide
  · exact dihedral_rel.2.2.2
  · decide

theorem card_D8 : Nat.card D8 = 8 := by
  obtain ⟨h1, h2, h3, -⟩ := dihedral_rel
  refine le_antisymm (card_closure_pair_le_eight h1 h2 h3) ?_
  set N : Subgroup A7 := Subgroup.zpowers (sD * tD) with hN
  have hNle : N ≤ D8 := by
    rw [hN, Subgroup.zpowers_le]
    exact D8.mul_mem sD_mem_D8 tD_mem_D8
  have hNcard : Nat.card N = 4 := by
    rw [hN, Nat.card_zpowers, orderOf_sD_mul_tD]
  have hdvd : 4 ∣ Nat.card D8 := hNcard ▸ Subgroup.card_dvd_of_le hNle
  have hne : N ≠ D8 := by
    intro h
    have hs : sD ∈ N := h ▸ sD_mem_D8
    rw [hN, Subgroup.mem_zpowers_iff] at hs
    obtain ⟨k, hk⟩ := hs
    have hk' : (sD * tD) ^ (k % 4).toNat = sD := by
      have := zpow_mod_orderOf (sD * tD) k
      rw [orderOf_sD_mul_tD] at this
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
      push_cast at this
      rw [this, hk]
    exact pow_ne_sD ⟨(k % 4).toNat, by omega⟩ hk'
  have hcard : 4 < Nat.card D8 := by
    have h0 : 0 < Nat.card D8 := Nat.card_pos
    rcases Nat.lt_or_ge 4 (Nat.card D8) with h | h
    · exact h
    · exfalso
      exact hne (Subgroup.eq_of_le_of_card_ge hNle (by omega))
  obtain ⟨c, hc⟩ := hdvd
  omega

theorem a7_involution_conj :
    ∀ y : A7, y ≠ 1 → y * y = 1 → ∃ g : A7, g * tD * g⁻¹ = y := by
  exact Certificates.certificate9300.1

private theorem sq_eq_one_of_commute_gens :
    ∀ σ : Perm (Fin 7), σ * (sD : Perm (Fin 7)) = (sD : Perm (Fin 7)) * σ →
      σ * (tD : Perm (Fin 7)) = (tD : Perm (Fin 7)) * σ → σ * σ = 1 := by
  exact Certificates.certificate9300.2.1

theorem sq_eq_one_of_commute_D8 {σ : Perm (Fin 7)}
    (hσ : ∀ d : A7, d ∈ D8 → (d : Perm (Fin 7)) * σ = σ * d) : σ * σ = 1 :=
  sq_eq_one_of_commute_gens σ (hσ sD sD_mem_D8).symm (hσ tD tD_mem_D8).symm

theorem exists_commuting_conj :
    ∀ σ : Perm (Fin 7), σ * σ = 1 → σ ≠ 1 →
      ∃ a : A7, (a : Perm (Fin 7))⁻¹ * σ * a ≠ σ ∧
        ((a : Perm (Fin 7))⁻¹ * σ * a) * σ = σ * ((a : Perm (Fin 7))⁻¹ * σ * a) := by
  exact Certificates.certificate9300.2.2.1

@[expose] def evenCentralizer (σ : Perm (Fin 7)) : Subgroup A7 where
  carrier := {a | (a : Perm (Fin 7)) * σ = σ * a}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    calc ((a * b : A7) : Perm (Fin 7)) * σ = a * (b * σ) := by simp [mul_assoc]
      _ = a * (σ * b) := by rw [hb]
      _ = (a * σ) * b := by rw [mul_assoc]
      _ = σ * a * b := by rw [ha]
      _ = σ * ((a * b : A7) : Perm (Fin 7)) := by simp [mul_assoc]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have : (a : Perm (Fin 7))⁻¹ * ((a : Perm (Fin 7)) * σ) * (a : Perm (Fin 7))⁻¹ =
        (a : Perm (Fin 7))⁻¹ * (σ * a) * (a : Perm (Fin 7))⁻¹ := by rw [ha]
    simpa [mul_assoc] using this.symm

theorem mem_evenCentralizer {σ : Perm (Fin 7)} {a : A7} :
    a ∈ evenCentralizer σ ↔ (a : Perm (Fin 7)) * σ = σ * a := Iff.rfl

private theorem card_evenCentralizer_mod_aux :
    ∀ σ : Perm (Fin 7), σ * σ = 1 →
      Fintype.card {a : A7 // (a : Perm (Fin 7)) * σ = σ * a} % 16 = 8 := by
  exact Certificates.certificate9300.2.2.2

theorem card_evenCentralizer_mod
    {σ : Perm (Fin 7)} (hσ : σ * σ = 1) :
    Nat.card (evenCentralizer σ) % 16 = 8 := by
  have h := card_evenCentralizer_mod_aux σ hσ
  rw [← Nat.card_eq_fintype_card] at h
  exact h

end CFSG.ClassicalInvolution.Hat2A7
