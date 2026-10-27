module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.OddStandard

open Equiv Subgroup

namespace SymFive

theorem mem_smul_sylow_iff {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (g x : G) :
    x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem conj_mem_smul_sylow {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (g : G) {v : G}
    (hv : v ∈ (P : Subgroup G)) : g * v * g⁻¹ ∈ ((g • P : Sylow p G) : Subgroup G) := by
  rwa [mem_smul_sylow_iff, show g⁻¹ * (g * v * g⁻¹) * g = v by group]

theorem conj_mem_normalizer_smul_sylow {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) (g : G)
    {n : G} (hn : n ∈ normalizer ((P : Subgroup G) : Set G)) :
    g * n * g⁻¹ ∈ normalizer (((g • P : Sylow p G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hn ⊢
  intro h
  have e : g⁻¹ * (g * n * g⁻¹ * h * (g * n * g⁻¹)⁻¹) * g = n * (g⁻¹ * h * g) * n⁻¹ := by group
  simp only [mem_smul_sylow_iff, e]
  exact hn _

theorem inv_mul_mul_ne_one {G : Type*} [Group G] {g x : G} (hx : x ≠ 1) : g⁻¹ * x * g ≠ 1 := by
  intro h
  apply hx
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

theorem inv_mul_swap_mul (g : Perm (Fin 5)) (i j : Fin 5) :
    g⁻¹ * swap i j * g = swap (g⁻¹ i) (g⁻¹ j) := by
  rw [swap_apply_apply g⁻¹ i j, inv_inv]

theorem card_perm_fin_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem card_alternatingGroup_fin_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  rfl

@[expose] def dihedralFinset : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 1 2 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 3 2 * swap 2 1,
    swap 0 2, swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2}

theorem mul_mem_dihedralFinset :
    ∀ a ∈ dihedralFinset, ∀ b ∈ dihedralFinset, a * b ∈ dihedralFinset := by
  decide +kernel

theorem inv_mem_dihedralFinset : ∀ a ∈ dihedralFinset, a⁻¹ ∈ dihedralFinset := by
  decide +kernel

@[expose] def dihedral : Subgroup (Perm (Fin 5)) where
  carrier := dihedralFinset
  mul_mem' ha hb := mul_mem_dihedralFinset _ ha _ hb
  one_mem' := by decide +kernel
  inv_mem' ha := inv_mem_dihedralFinset _ ha

theorem mem_dihedral {σ : Perm (Fin 5)} : σ ∈ dihedral ↔ σ ∈ dihedralFinset :=
  Iff.rfl

theorem card_dihedral : Nat.card dihedral = 8 := by
  have : Nat.card dihedral = Nat.card (dihedralFinset : Set (Perm (Fin 5))) := rfl
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide +kernel

theorem index_dihedral : dihedral.index = 15 := by
  have h := dihedral.card_mul_index
  rw [card_dihedral, card_perm_fin_five] at h
  omega

@[expose] def dihedralSylow : Sylow 2 (Perm (Fin 5)) :=
  (IsPGroup.of_card (n := 3) card_dihedral).toSylow (by rw [index_dihedral]; decide)

@[simp] theorem coe_dihedralSylow : (dihedralSylow : Subgroup (Perm (Fin 5))) = dihedral :=
  rfl

theorem swap_mem_dihedralFinset : ∀ a b : Fin 5, a ≠ b → swap a b ∈ dihedralFinset →
    swap a b = swap 0 2 ∨ swap a b = swap 1 3 := by
  decide +kernel

theorem exists_even_not_commute_swap_dihedral {a b : Fin 5} (hab : a ≠ b)
    (h : swap a b ∈ dihedral) :
    ∃ v ∈ dihedral, Perm.sign v = 1 ∧ swap a b * v ≠ v * swap a b := by
  refine ⟨swap 0 1 * swap 2 3, mem_dihedral.2 (by decide +kernel), by decide +kernel, ?_⟩
  rcases swap_mem_dihedralFinset a b hab h with h | h <;> rw [h] <;> decide +kernel

theorem swap_mem_smul_dihedralSylow_iff (g : Perm (Fin 5)) (i j : Fin 5) :
    swap i j ∈ ((g • dihedralSylow : Sylow 2 (Perm (Fin 5))) : Subgroup (Perm (Fin 5))) ↔
      swap (g⁻¹ i) (g⁻¹ j) ∈ dihedral := by
  rw [mem_smul_sylow_iff, inv_mul_swap_mul, coe_dihedralSylow]

@[expose] def kleinFinset : Finset (Perm (Fin 5)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem mul_mem_kleinFinset : ∀ a ∈ kleinFinset, ∀ b ∈ kleinFinset, a * b ∈ kleinFinset := by
  decide +kernel

theorem inv_mem_kleinFinset : ∀ a ∈ kleinFinset, a⁻¹ ∈ kleinFinset := by
  decide +kernel

theorem sign_of_mem_kleinFinset : ∀ a ∈ kleinFinset, Perm.sign a = 1 := by
  decide +kernel

@[expose] def klein : Subgroup (Perm (Fin 5)) where
  carrier := kleinFinset
  mul_mem' ha hb := mul_mem_kleinFinset _ ha _ hb
  one_mem' := by decide +kernel
  inv_mem' ha := inv_mem_kleinFinset _ ha

theorem mem_klein {σ : Perm (Fin 5)} : σ ∈ klein ↔ σ ∈ kleinFinset :=
  Iff.rfl

theorem klein_le_alternatingGroup : klein ≤ alternatingGroup (Fin 5) := fun σ hσ =>
  Perm.mem_alternatingGroup.2 (sign_of_mem_kleinFinset σ hσ)

theorem card_klein : Nat.card klein = 4 := by
  have : Nat.card klein = Nat.card (kleinFinset : Set (Perm (Fin 5))) := rfl
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide +kernel

@[expose] def kleinAlt : Subgroup (alternatingGroup (Fin 5)) :=
  klein.subgroupOf (alternatingGroup (Fin 5))

theorem mem_kleinAlt {σ : alternatingGroup (Fin 5)} :
    σ ∈ kleinAlt ↔ (σ : Perm (Fin 5)) ∈ kleinFinset :=
  mem_subgroupOf

theorem card_kleinAlt : Nat.card kleinAlt = 4 := by
  rw [kleinAlt, Nat.card_congr (subgroupOfEquivOfLe klein_le_alternatingGroup).toEquiv,
    card_klein]

theorem index_kleinAlt : kleinAlt.index = 15 := by
  have h := kleinAlt.card_mul_index
  rw [card_kleinAlt, card_alternatingGroup_fin_five] at h
  omega

@[expose] def kleinSylow : Sylow 2 (alternatingGroup (Fin 5)) :=
  (IsPGroup.of_card (n := 2) card_kleinAlt).toSylow (by rw [index_kleinAlt]; decide)

@[simp] theorem coe_kleinSylow :
    (kleinSylow : Subgroup (alternatingGroup (Fin 5))) = kleinAlt :=
  rfl

theorem conj_mem_kleinFinset :
    ∀ a ∈ kleinFinset, swap 0 1 * swap 1 2 * a * (swap 0 1 * swap 1 2)⁻¹ ∈ kleinFinset := by
  decide +kernel

theorem kleinFinset_transitive : ∀ a ∈ kleinFinset, ∀ b ∈ kleinFinset, a ≠ 1 → b ≠ 1 →
    b = a ∨ b = swap 0 1 * swap 1 2 * a * (swap 0 1 * swap 1 2)⁻¹ ∨
      b = (swap 0 1 * swap 1 2)⁻¹ * a * (swap 0 1 * swap 1 2) := by
  decide +kernel

@[expose] def threeCycle : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 1 2, Perm.mem_alternatingGroup.2 (by decide +kernel)⟩

@[simp] theorem coe_threeCycle : (threeCycle : Perm (Fin 5)) = swap 0 1 * swap 1 2 :=
  rfl

theorem threeCycle_mem_normalizer :
    threeCycle ∈ normalizer ((kleinSylow : Subgroup (alternatingGroup (Fin 5))) : Set _) := by
  refine mem_normalizer_fintype fun n hn => ?_
  rw [SetLike.mem_coe, coe_kleinSylow, mem_kleinAlt] at hn ⊢
  exact conj_mem_kleinFinset _ hn

theorem exists_mem_normalizer_conj_kleinSylow {x y : alternatingGroup (Fin 5)}
    (hx : x ∈ (kleinSylow : Subgroup (alternatingGroup (Fin 5))))
    (hy : y ∈ (kleinSylow : Subgroup (alternatingGroup (Fin 5)))) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ n ∈ normalizer ((kleinSylow : Subgroup (alternatingGroup (Fin 5))) : Set _),
      n * x * n⁻¹ = y := by
  rw [coe_kleinSylow, mem_kleinAlt] at hx hy
  have hx1' : (x : Perm (Fin 5)) ≠ 1 := by simpa using hx1
  have hy1' : (y : Perm (Fin 5)) ≠ 1 := by simpa using hy1
  rcases kleinFinset_transitive _ hx _ hy hx1' hy1' with h | h | h
  · exact ⟨1, one_mem _, by simpa using (Subtype.ext h).symm⟩
  · exact ⟨threeCycle, threeCycle_mem_normalizer, Subtype.ext (by simpa using h.symm)⟩
  · exact ⟨threeCycle⁻¹, inv_mem threeCycle_mem_normalizer, Subtype.ext (by simpa using h.symm)⟩

end SymFive

theorem exists_swap_mem_sylow_two (D : Sylow 2 (Perm (Fin 5))) :
    ∃ i j : Fin 5, i ≠ j ∧ swap i j ∈ (D : Subgroup (Perm (Fin 5))) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) SymFive.dihedralSylow D
  refine ⟨g 0, g 2, g.injective.ne (by decide), ?_⟩
  rw [SymFive.swap_mem_smul_dihedralSylow_iff]
  simp only [Perm.coe_inv, symm_apply_apply]
  exact SymFive.mem_dihedral.2 (by decide +kernel)

theorem exists_even_not_commute_swap_of_sylow (D : Sylow 2 (Perm (Fin 5))) {i j : Fin 5}
    (hij : i ≠ j) (h : swap i j ∈ (D : Subgroup (Perm (Fin 5)))) :
    ∃ v ∈ (D : Subgroup (Perm (Fin 5))), Perm.sign v = 1 ∧ swap i j * v ≠ v * swap i j := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) SymFive.dihedralSylow D
  rw [SymFive.swap_mem_smul_dihedralSylow_iff] at h
  obtain ⟨v, hv, hs, hc⟩ :=
    SymFive.exists_even_not_commute_swap_dihedral (g⁻¹.injective.ne hij) h
  refine ⟨g * v * g⁻¹, SymFive.conj_mem_smul_sylow _ g hv, by simp [hs], fun hcomm => hc ?_⟩
  rw [← SymFive.inv_mul_swap_mul]
  calc g⁻¹ * swap i j * g * v = g⁻¹ * (swap i j * (g * v * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * v * g⁻¹) * swap i j) * g := by rw [hcomm]
    _ = v * (g⁻¹ * swap i j * g) := by group

theorem exists_swap_of_sign_eq_neg_one {σ : Perm (Fin 5)} (h2 : σ * σ = 1)
    (hs : Perm.sign σ = -1) : ∃ i j : Fin 5, i ≠ j ∧ σ = swap i j := by
  revert σ
  decide +kernel

theorem eq_bot_of_normal_odd_perm_five (N : Subgroup (Perm (Fin 5))) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  have hle : N ≤ alternatingGroup (Fin 5) := by
    intro x hx
    rw [Perm.mem_alternatingGroup]
    have hpow : x ^ Nat.card N = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (G := N) (x := ⟨x, hx⟩))
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    have hsp : Perm.sign x ^ Nat.card N = 1 := by rw [← map_pow, hpow, map_one]
    rcases Int.units_eq_one_or (Perm.sign x) with h | h
    · exact h
    · rw [h, hN.neg_one_pow] at hsp
      exact absurd hsp (by decide)
  have := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5))) with
    h | h
  · exact (subgroupOf_eq_bot.1 h).eq_bot_of_le hle
  · rw [le_antisymm hle (subgroupOf_eq_top.1 h), SymFive.card_alternatingGroup_fin_five] at hN
    exact absurd hN (by decide)

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 :=
  SymFive.card_alternatingGroup_fin_five

theorem orderOf_ne_four_alternatingGroup_five (g : alternatingGroup (Fin 5)) :
    orderOf g ≠ 4 := by
  intro h4
  have key : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ^ 4 = 1 → σ ^ 2 = 1 := by
    decide +kernel
  have hg4 : (g : Perm (Fin 5)) ^ 4 = 1 := by
    rw [← h4, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  have hg2 : g ^ 2 = 1 :=
    Subtype.ext (by simpa using key g (Perm.mem_alternatingGroup.1 g.2) hg4)
  have := orderOf_dvd_of_pow_eq_one hg2
  rw [h4] at this
  exact absurd this (by decide)

theorem exists_mem_normalizer_conj_of_sylow_two_alternatingGroup_five
    (P : Sylow 2 (alternatingGroup (Fin 5))) {p q : alternatingGroup (Fin 5)}
    (hp : p ∈ (P : Subgroup (alternatingGroup (Fin 5)))) (hq : q ∈ (P : Subgroup _))
    (hp1 : p ≠ 1) (hq1 : q ≠ 1) :
    ∃ n ∈ normalizer ((P : Subgroup (alternatingGroup (Fin 5))) : Set _), n * p * n⁻¹ = q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) SymFive.kleinSylow P
  rw [SymFive.mem_smul_sylow_iff] at hp hq
  obtain ⟨n, hn, hc⟩ := SymFive.exists_mem_normalizer_conj_kleinSylow hp hq
    (SymFive.inv_mul_mul_ne_one hp1) (SymFive.inv_mul_mul_ne_one hq1)
  refine ⟨g * n * g⁻¹, SymFive.conj_mem_normalizer_smul_sylow _ g hn, ?_⟩
  calc g * n * g⁻¹ * p * (g * n * g⁻¹)⁻¹ = g * (n * (g⁻¹ * p * g) * n⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * q * g) * g⁻¹ := by rw [hc]
    _ = q := by group

theorem eq_top_of_alternatingGroup_le_of_exists_odd (X : Subgroup (Perm (Fin 5)))
    (h : alternatingGroup (Fin 5) ≤ X) {σ : Perm (Fin 5)} (hσ : σ ∈ X) (hs : Perm.sign σ = -1) :
    X = ⊤ := by
  refine eq_top_iff.2 fun τ _ => ?_
  rcases Int.units_eq_one_or (Perm.sign τ) with hτ | hτ
  · exact h (Perm.mem_alternatingGroup.2 hτ)
  · have hστ : σ⁻¹ * τ ∈ X := h (Perm.mem_alternatingGroup.2 (by simp [hs, hτ]))
    simpa using X.mul_mem hσ hστ

end CFSG.OddStandard
