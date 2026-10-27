module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Perm

public section

namespace GL83.PiGen

open Equiv Equiv.Perm GL83

section Fix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] def fixFinset (σ : Perm Ω) : Finset Ω := Finset.univ.filter fun ω => σ ω = ω

theorem mem_fixFinset {σ : Perm Ω} {ω : Ω} : ω ∈ fixFinset σ ↔ σ ω = ω := by
  simp [fixFinset]

theorem apply_mem_fixFinset_iff_of_commute {σ ρ : Perm Ω} (hc : σ * ρ = ρ * σ) (ω : Ω) :
    ρ ω ∈ fixFinset σ ↔ ω ∈ fixFinset σ := by
  have h : σ (ρ ω) = ρ (σ ω) := by
    have := congrArg (fun τ : Perm Ω => τ ω) hc
    simpa [Perm.mul_apply] using this
  rw [mem_fixFinset, mem_fixFinset, h]
  exact ⟨fun h' => ρ.injective h', fun h' => by rw [h']⟩

theorem card_fixFinset_modEq {p : ℕ} [Fact p.Prime] {σ : Perm Ω} (hσ : σ ^ p = 1) :
    Nat.card Ω ≡ (fixFinset σ).card [MOD p] := by
  have hE : IsPGroup p (Subgroup.zpowers σ) := fun g => ⟨1, by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 g.2
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]⟩
  have h := card_fixSet_modEq hE
  have hfix : fixSet (Subgroup.zpowers σ) = (fixFinset σ : Set Ω) := by
    ext ω
    simp only [mem_fixSet, Finset.mem_coe, mem_fixFinset]
    exact ⟨fun h => h σ (Subgroup.mem_zpowers σ), fun h e he => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      exact zpow_apply_eq_self_of_apply_eq_self h j⟩
  rw [hfix, Nat.card_coe_set_eq, Set.ncard_coe_finset] at h
  exact h

theorem exists_card_eq_of_modEq {p k n c : ℕ} (hp3 : 3 ≤ p) (hnk : n = k * p + 2)
    (hmod : n ≡ c [MOD p]) (hc : 3 ≤ c) : ∃ k' : ℕ, 1 ≤ k' ∧ c = k' * p + 2 := by
  have hn : n % p = 2 := by
    rw [hnk, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hc2 : c % p = 2 := (show c % p = n % p from hmod.symm).trans hn
  have hdiv : p * (c / p) + c % p = c := Nat.div_add_mod c p
  rw [hc2] at hdiv
  refine ⟨c / p, ?_, by rw [mul_comm]; linarith⟩
  by_contra hlt
  have h0 : c / p = 0 := Nat.lt_one_iff.1 (Nat.lt_of_not_le hlt)
  rw [h0] at hdiv
  omega

theorem zpowers_swap {a b : Ω} (hab : a ≠ b) {σ : Perm Ω} (hσ : σ ∈ Subgroup.zpowers (swap a b)) :
    σ = 1 ∨ σ = swap a b := by
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hσ
  have ho : orderOf (swap a b) = 2 := (show (swap a b).IsSwap from ⟨a, b, hab, rfl⟩).orderOf
  rw [← zpow_mod_orderOf, ho]
  rcases Int.emod_two_eq_zero_or_one j with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

omit [Fintype Ω] in
theorem fixes_of_commute_swap {a b : Ω} (hab : a ≠ b) {σ : Perm Ω}
    (hcomm : σ * swap a b = swap a b * σ) {p : ℕ} (hp : Odd p) (hσ : σ ^ p = 1) :
    σ a = a ∧ σ b = b := by
  have h1 : σ b = swap a b (σ a) := by
    have := congrArg (fun τ : Perm Ω => τ a) hcomm
    simpa [Perm.mul_apply] using this
  by_cases ha : σ a = a
  · refine ⟨ha, ?_⟩
    rw [h1, ha, swap_apply_left]
  · exfalso
    by_cases hb : σ a = b
    · have h2 : σ b = a := by rw [h1, hb, swap_apply_right]
      obtain ⟨m, rfl⟩ := hp
      have hb2 : (σ ^ 2) b = b := by rw [pow_two, Perm.mul_apply, h2, hb]
      have h3 : (σ ^ (2 * m + 1)) a = b := by
        rw [pow_succ, Perm.mul_apply, hb, pow_mul]
        exact pow_apply_eq_self_of_apply_eq_self hb2 m
      rw [hσ] at h3
      exact hab h3
    · have h2 : σ b = σ a := by rw [h1, swap_apply_of_ne_of_ne ha hb]
      exact hab (σ.injective h2).symm

omit [DecidableEq Ω] in
theorem exists_ne_one_fixing {D : Type*} [Group D] [Finite D] (f : D →* Perm Ω)
    (R : Subgroup (Perm Ω)) (hR : ∀ d, f d ∈ R) (ω : Ω)
    (h : Nat.card (MulAction.orbit R ω) < Nat.card D) : ∃ d : D, d ≠ 1 ∧ f d ω = ω := by
  have hmaps : ∀ d : D, f d ω ∈ MulAction.orbit R ω := fun d => ⟨⟨f d, hR d⟩, rfl⟩
  set g : D → MulAction.orbit R ω := fun d => ⟨f d ω, hmaps d⟩ with hg
  have hnot : ¬ Function.Injective g := fun hinj =>
    absurd (Nat.card_le_card_of_injective g hinj) (not_le.2 h)
  obtain ⟨x, y, hxy, hne⟩ : ∃ x y, g x = g y ∧ x ≠ y := by
    by_contra hcon
    exact hnot fun x y hxy => by_contra fun hne => hcon ⟨x, y, hxy, hne⟩
  have hfx : f x ω = f y ω := congrArg Subtype.val hxy
  refine ⟨y⁻¹ * x, fun h1 => hne (inv_mul_eq_one.1 h1).symm, ?_⟩
  rw [map_mul, map_inv, Perm.mul_apply, hfx]
  simp

omit [Fintype Ω] in
theorem swap_apply_mem_iff {S : Set Ω} {a b : Ω} (ha : a ∈ S) (hb : b ∈ S) (ω : Ω) :
    swap a b ω ∈ S ↔ ω ∈ S := by
  rw [swap_apply_def]
  split_ifs with h1 h2
  · subst h1
    exact ⟨fun _ => ha, fun _ => hb⟩
  · subst h2
    exact ⟨fun _ => hb, fun _ => ha⟩
  · exact Iff.rfl

theorem preserves_of_mem_zpowers_swap {S : Set Ω} {a b : Ω} (hab : a ≠ b) (ha : a ∈ S)
    (hb : b ∈ S) {σ : Perm Ω} (hσ : σ ∈ Subgroup.zpowers (swap a b)) (ω : Ω) :
    σ ω ∈ S ↔ ω ∈ S := by
  rcases zpowers_swap hab hσ with rfl | rfl
  · exact Iff.rfl
  · exact swap_apply_mem_iff ha hb ω

omit [Fintype Ω] in
theorem swap_conj_cyc3_ne {a b x y : Ω} (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a)
    (hyb : y ≠ b) (hxy : x ≠ y) : swap a b * cyc3 a x y * (swap a b)⁻¹ ≠ cyc3 a x y := by
  intro h
  have h1 := congrArg (fun τ : Perm Ω => τ b) h
  simp only [Perm.mul_apply, swap_inv, swap_apply_right] at h1
  rw [cyc3_apply_left ⟨hxa.symm, hya.symm, hxy⟩, swap_apply_of_ne_of_ne hxa hxb,
    cyc3_apply_of_ne hab.symm hxb.symm hyb.symm] at h1
  exact hxb h1

end Fix

end GL83.PiGen
