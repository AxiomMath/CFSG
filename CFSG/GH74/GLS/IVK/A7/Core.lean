module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

public section

namespace CFSG.GH74.GLS.IVK.A7

open Equiv Equiv.Perm Subgroup

abbrev S7 : Type := Perm (Fin 7)

@[expose] def r : S7 := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def s : S7 := swap 0 2

@[expose] def f0 : S7 := swap 4 5

@[expose] def T0list : List S7 :=
  [1, r, r ^ 2, r ^ 3, s, s * r, s * r ^ 2, s * r ^ 3, f0, r * f0, r ^ 2 * f0, r ^ 3 * f0, s * f0,
    s * r * f0, s * r ^ 2 * f0, s * r ^ 3 * f0]

theorem T0list_cases {P : S7 → Prop} (h : ∀ x ∈ T0list, P x) :
    P 1 ∧ P r ∧ P (r ^ 2) ∧ P (r ^ 3) ∧ P s ∧ P (s * r) ∧ P (s * r ^ 2) ∧ P (s * r ^ 3) ∧ P f0 ∧
      P (r * f0) ∧ P (r ^ 2 * f0) ∧ P (r ^ 3 * f0) ∧ P (s * f0) ∧ P (s * r * f0) ∧
      P (s * r ^ 2 * f0) ∧ P (s * r ^ 3 * f0) := by
  simp only [T0list, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  exact h

theorem mem_T0list_iff {x : S7} : x ∈ T0list ↔
    x = 1 ∨ x = r ∨ x = r ^ 2 ∨ x = r ^ 3 ∨ x = s ∨ x = s * r ∨ x = s * r ^ 2 ∨ x = s * r ^ 3 ∨
      x = f0 ∨ x = r * f0 ∨ x = r ^ 2 * f0 ∨ x = r ^ 3 * f0 ∨ x = s * f0 ∨ x = s * r * f0 ∨
      x = s * r ^ 2 * f0 ∨ x = s * r ^ 3 * f0 := by
  simp [T0list]

theorem T0_closed : ∀ x ∈ T0list, ∀ y ∈ T0list, x * y ∈ T0list := by
  intro x hx y hy
  rw [mem_T0list_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide +kernel

theorem T0_inv : ∀ x ∈ T0list, x⁻¹ ∈ T0list := by
  intro x hx
  rw [mem_T0list_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide +kernel

@[expose] def T0 : Subgroup S7 where
  carrier := {x | x ∈ T0list}
  one_mem' := by decide +kernel
  mul_mem' := fun {x y} hx hy => T0_closed x hx y hy
  inv_mem' := fun {x} hx => T0_inv x hx

theorem mem_T0_iff {x : S7} : x ∈ T0 ↔ x ∈ T0list := Iff.rfl

theorem T0list_nodup : T0list.Nodup := by decide +kernel

theorem card_T0 : Nat.card T0 = 16 := by
  have h : (T0 : Set S7) = ↑(T0list.toFinset) := by
    ext x
    simp [mem_T0_iff]
  show Nat.card (T0 : Set S7) = 16
  rw [h]
  exact (Nat.card_eq_finsetCard T0list.toFinset).trans
    (by rw [List.toFinset_card_of_nodup T0list_nodup]; rfl)

theorem card_S7 : Nat.card S7 = 5040 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

theorem factorization_S7 : (Nat.card S7).factorization 2 = 4 := by
  rw [card_S7, show (5040 : ℕ) = 2 ^ 4 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]

@[expose] noncomputable def T0Sylow : Sylow 2 S7 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard T0 (by rw [card_T0, factorization_S7]; norm_num)

theorem exists_conj_T0 (T : Sylow 2 S7) :
    ∃ g : S7, ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S7 T0Sylow T
  refine ⟨g, fun x => ?_⟩
  rw [← hg]
  show x ∈ ((g • T0Sylow : Sylow 2 S7) : Subgroup S7) ↔ _
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have : g⁻¹ * (MulAut.conj g • y) * g = y := by simp [MulAut.smul_def]; group
    rw [this]
    exact hy
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.smul_def]; group⟩

@[expose] def P0list : List S7 :=
  [1, r ^ 2, s * r, s * r ^ 3, r * f0, r ^ 3 * f0, s * f0, s * r ^ 2 * f0]

theorem mem_P0list_iff {x : S7} : x ∈ P0list ↔
    x = 1 ∨ x = r ^ 2 ∨ x = s * r ∨ x = s * r ^ 3 ∨ x = r * f0 ∨ x = r ^ 3 * f0 ∨ x = s * f0 ∨
      x = s * r ^ 2 * f0 := by
  simp [P0list]

theorem T0list_even_iff : ∀ x ∈ T0list, (sign x = 1 ↔ x ∈ P0list) := by
  intro x hx
  rw [mem_T0list_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide +kernel

theorem P0list_sub : ∀ x ∈ P0list, x ∈ T0list := by
  intro x hx
  rw [mem_P0list_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem P0list_even : ∀ x ∈ P0list, sign x = 1 := fun x hx =>
  (T0list_even_iff x (P0list_sub x hx)).mpr hx

theorem T0_comm_f0 : ∀ x ∈ T0list, x * f0 = f0 * x := by
  intro x hx
  rw [mem_T0list_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide +kernel

theorem unique_swap : ∀ x ∈ T0list, x.support.card = 2 → (∀ y ∈ P0list, y * x = x * y) → x = f0 := by
  intro x hx h1 h2
  rw [mem_T0list_iff] at hx
  simp only [P0list, List.forall_mem_cons] at h2
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, -⟩ := h2
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
  first
    | exact absurd h1 (by decide +kernel)
    | exact absurd c1 (by decide +kernel)
    | exact absurd c2 (by decide +kernel)
    | exact absurd c3 (by decide +kernel)
    | exact absurd c4 (by decide +kernel)
    | exact absurd c5 (by decide +kernel)
    | exact absurd c6 (by decide +kernel)
    | exact absurd c7 (by decide +kernel)
    | exact absurd c8 (by decide +kernel)
    | rfl

theorem unique_central_involution : ∀ z ∈ P0list, z ^ 2 = 1 → z ≠ 1 →
    (∀ y ∈ P0list, y * z = z * y) → z = r ^ 2 := by
  intro z hz h1 h2 h3
  rw [mem_P0list_iff] at hz
  simp only [P0list, List.forall_mem_cons] at h3
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, -⟩ := h3
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
    | exact absurd (by decide +kernel) h2
    | exact absurd h1 (by decide +kernel)
    | exact absurd c1 (by decide +kernel)
    | exact absurd c2 (by decide +kernel)
    | exact absurd c3 (by decide +kernel)
    | exact absurd c4 (by decide +kernel)
    | exact absurd c5 (by decide +kernel)
    | exact absurd c6 (by decide +kernel)
    | exact absurd c7 (by decide +kernel)
    | exact absurd c8 (by decide +kernel)
    | rfl

theorem f0_mul_r_sq_support : (f0 * r ^ 2).support.card = 6 := by decide +kernel

theorem f0_mul_r_sq_sq : (f0 * r ^ 2) ^ 2 = 1 := by decide +kernel

section General

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem cycleType_replicate_two (σ : Perm α) (h : σ ^ 2 = 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h
    have h3 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    exact (Nat.le_of_dvd two_pos (h1.trans h2)).antisymm h3
  have h1 := Multiset.eq_replicate_of_mem hall
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [h1, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [h1]
  congr 1
  omega

theorem sign_conj_eq (g x : Perm α) : sign (g⁻¹ * x * g) = sign x := by
  rw [sign_mul, sign_mul, sign_inv, mul_comm (sign g * sign x), ← mul_assoc, Int.units_mul_self,
    one_mul]

theorem cycleType_conj_inv (g f : Perm α) : (g⁻¹ * f * g).cycleType = f.cycleType := by
  simpa using Equiv.Perm.cycleType_conj (τ := g⁻¹) (σ := f)

theorem alternating_inf_zpowers_eq_bot (f : Perm α) (hf2 : f ^ 2 = 1) (hfs : sign f = -1) :
    alternatingGroup α ⊓ zpowers f = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxA, hxf⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxf
  have hxA' : sign (f ^ k) = 1 := Equiv.Perm.mem_alternatingGroup.mp hxA
  rw [map_zpow, hfs] at hxA'
  have hk : Even k := by
    by_contra hk
    rw [Int.not_even_iff_odd] at hk
    rw [hk.neg_one_zpow] at hxA'
    exact absurd hxA' (by decide)
  obtain ⟨m, hm⟩ := hk
  rw [hm, ← two_mul, zpow_mul]
  have : f ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact hf2
  rw [this, one_zpow]
  exact Subgroup.one_mem _

end General

section Conj

variable {T : Sylow 2 S7} {g : S7}

theorem f0_mem_T0list : f0 ∈ T0list := by decide +kernel

theorem f0_isSwap : f0.IsSwap := ⟨4, 5, by decide, rfl⟩

theorem f0_cycleType : f0.cycleType = {2} := Equiv.Perm.isSwap_iff_cycleType.mp f0_isSwap

theorem f0_sq : f0 ^ 2 = 1 := by decide +kernel

theorem mem_T_inf_A7 (hg : ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0) (x : S7) :
    x ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) ↔ g⁻¹ * x * g ∈ P0list := by
  rw [Subgroup.mem_inf, hg, Equiv.Perm.mem_alternatingGroup, ← sign_conj_eq g x]
  exact ⟨fun ⟨h1, h2⟩ => (T0list_even_iff _ h1).mp h2,
    fun h => ⟨P0list_sub _ h, P0list_even _ h⟩⟩

theorem fT_mem (hg : ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0) :
    g * f0 * g⁻¹ ∈ (T : Subgroup S7) := by
  rw [hg]
  have : g⁻¹ * (g * f0 * g⁻¹) * g = f0 := by group
  rw [this]
  exact f0_mem_T0list

theorem fT_comm (hg : ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0) :
    ∀ x ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7), x * (g * f0 * g⁻¹) = (g * f0 * g⁻¹) * x := by
  intro x hx
  have hy := (mem_T_inf_A7 hg x).mp hx
  have hc := T0_comm_f0 _ (P0list_sub _ hy)
  obtain ⟨y, hyx⟩ : ∃ y, y = g⁻¹ * x * g := ⟨_, rfl⟩
  have hx' : x = g * y * g⁻¹ := by rw [hyx]; group
  rw [← hyx] at hc
  rw [hx']
  calc g * y * g⁻¹ * (g * f0 * g⁻¹) = g * (y * f0) * g⁻¹ := by group
    _ = g * (f0 * y) * g⁻¹ := by rw [hc]
    _ = g * f0 * g⁻¹ * (g * y * g⁻¹) := by group

theorem fT_isSwap : (g * f0 * g⁻¹).IsSwap := by
  rw [Equiv.Perm.isSwap_iff_cycleType, show g * f0 * g⁻¹ = (g⁻¹)⁻¹ * f0 * g⁻¹ by simp,
    cycleType_conj_inv, f0_cycleType]

theorem split_unique (hg : ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0) {f : S7}
    (hfT : f ∈ (T : Subgroup S7)) (hf : f.cycleType = {2})
    (hc : ∀ x ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7), x * f = f * x) :
    f = g * f0 * g⁻¹ := by
  have h1 : g⁻¹ * f * g ∈ T0list := (hg f).mp hfT
  have h2 : (g⁻¹ * f * g).support.card = 2 := by
    rw [← Equiv.Perm.sum_cycleType, cycleType_conj_inv, hf]
    rfl
  have h3 : ∀ y ∈ P0list, y * (g⁻¹ * f * g) = (g⁻¹ * f * g) * y := by
    intro y hy
    have hxmem : g * y * g⁻¹ ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) := by
      rw [mem_T_inf_A7 hg]
      have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [this]
      exact hy
    have hcx := hc _ hxmem
    calc y * (g⁻¹ * f * g) = g⁻¹ * ((g * y * g⁻¹) * f) * g := by group
      _ = g⁻¹ * (f * (g * y * g⁻¹)) * g := by rw [hcx]
      _ = (g⁻¹ * f * g) * y := by group
  have h4 := unique_swap _ h1 h2 h3
  calc f = g * (g⁻¹ * f * g) * g⁻¹ := by group
    _ = g * f0 * g⁻¹ := by rw [h4]

theorem exists_split (T : Sylow 2 S7) :
    ∃ f : S7, orderOf f = 2 ∧ f.cycleType = {2} ∧ f ∈ (T : Subgroup S7) ∧
      (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) ⊓ zpowers f = ⊥ ∧
      (∀ x ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7), x * f = f * x) ∧
      (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) ⊔ zpowers f = (T : Subgroup S7) := by
  obtain ⟨g, hg⟩ := exists_conj_T0 T
  have hsw : (g * f0 * g⁻¹).IsSwap := fT_isSwap
  have hfT : g * f0 * g⁻¹ ∈ (T : Subgroup S7) := fT_mem hg
  have hsq : (g * f0 * g⁻¹) ^ 2 = 1 := by
    have : (g * f0 * g⁻¹) ^ 2 = g * f0 ^ 2 * g⁻¹ := by simp only [pow_two]; group
    rw [this, f0_sq]
    group
  have hsgn : sign (g * f0 * g⁻¹) = -1 := hsw.sign_eq
  refine ⟨g * f0 * g⁻¹, hsw.orderOf, Equiv.Perm.isSwap_iff_cycleType.mp hsw, hfT, ?_, fT_comm hg, ?_⟩
  · rw [eq_bot_iff]
    calc (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) ⊓ zpowers (g * f0 * g⁻¹)
        ≤ alternatingGroup (Fin 7) ⊓ zpowers (g * f0 * g⁻¹) :=
          inf_le_inf_right _ inf_le_right
      _ = ⊥ := alternating_inf_zpowers_eq_bot _ hsq hsgn
      _ ≤ ⊥ := le_rfl
  · apply le_antisymm
    · exact sup_le inf_le_left ((Subgroup.zpowers_le).mpr hfT)
    · intro x hx
      by_cases hs : sign x = 1
      · exact Subgroup.mem_sup_left ⟨hx, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
      · have hs' : sign x = -1 := by
          rcases Int.units_eq_one_or (sign x) with h | h
          · exact absurd h hs
          · exact h
        have hxf : x * (g * f0 * g⁻¹) ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) := by
          refine ⟨Subgroup.mul_mem _ hx hfT, Equiv.Perm.mem_alternatingGroup.mpr ?_⟩
          rw [sign_mul, hs', hsgn]
          rfl
        have := Subgroup.mul_mem _ (Subgroup.mem_sup_left hxf)
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers (g * f0 * g⁻¹))))
        rwa [mul_inv_cancel_right] at this

theorem central_involution_eq (hg : ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0) {z : S7}
    (hzT : z ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7)) (hz2 : orderOf z = 2)
    (hc : ∀ x ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7), x * z = z * x) :
    z = g * r ^ 2 * g⁻¹ := by
  have h1 : g⁻¹ * z * g ∈ P0list := (mem_T_inf_A7 hg z).mp hzT
  have hzz : z ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2] at this
  have h2 : (g⁻¹ * z * g) ^ 2 = 1 := by
    have : (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by simp only [pow_two]; group
    rw [this, hzz]
    group
  have h3 : g⁻¹ * z * g ≠ 1 := by
    intro h
    have : z = 1 := by
      calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have h4 : ∀ y ∈ P0list, y * (g⁻¹ * z * g) = (g⁻¹ * z * g) * y := by
    intro y hy
    have hxmem : g * y * g⁻¹ ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) := by
      rw [mem_T_inf_A7 hg]
      have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [this]
      exact hy
    have hcx := hc _ hxmem
    calc y * (g⁻¹ * z * g) = g⁻¹ * ((g * y * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [hcx]
      _ = (g⁻¹ * z * g) * y := by group
  have h5 := unique_central_involution _ h1 h2 h3 h4
  calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    _ = g * r ^ 2 * g⁻¹ := by rw [h5]

theorem cycleType_fz (g : S7) :
    (g * f0 * g⁻¹ * (g * r ^ 2 * g⁻¹)).cycleType = {2, 2, 2} := by
  have : g * f0 * g⁻¹ * (g * r ^ 2 * g⁻¹) = (g⁻¹)⁻¹ * (f0 * r ^ 2) * g⁻¹ := by simp [mul_assoc]
  rw [this, cycleType_conj_inv, cycleType_replicate_two _ f0_mul_r_sq_sq, f0_mul_r_sq_support]
  rfl

end Conj

section Index

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem card_inf_alternating (C : Subgroup (Perm α)) {x : Perm α} (hx : x ∈ C) (hs : sign x = -1) :
    Nat.card C = 2 * Nat.card ↥(C ⊓ alternatingGroup α) := by
  have hidx : ((alternatingGroup α).subgroupOf C).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨x, hx⟩, fun b => ?_⟩
    have hb : sign (b : Perm α) = 1 ∨ sign (b : Perm α) = -1 := Int.units_eq_one_or _
    show Xor (sign ((b : Perm α) * x) = 1) (sign (b : Perm α) = 1)
    rw [sign_mul, hs]
    rcases hb with hb | hb
    · rw [hb]
      simp [Xor]
    · rw [hb]
      simp [Xor]
  have h1 := Subgroup.card_mul_index ((alternatingGroup α).subgroupOf C)
  rw [hidx] at h1
  have h2 : Nat.card ↥((alternatingGroup α).subgroupOf C) = Nat.card ↥(C ⊓ alternatingGroup α) := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [h2] at h1
  omega

theorem exists_swap_mem_centralizer (u : Perm α) (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    ∃ a b : α, a ≠ b ∧ u a = b ∧ swap a b ∈ centralizer ({u} : Set (Perm α)) := by
  obtain ⟨a, ha⟩ : ∃ a, u a ≠ a := by
    by_contra h
    push Not at h
    exact hne (Equiv.ext h)
  refine ⟨a, u a, fun h => ha h.symm, rfl, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hub : u (u a) = a := by
    have := congrArg (fun f : Perm α => f a) hu
    simpa [pow_two] using this
  have h1 : u * swap a (u a) * u⁻¹ = swap a (u a) := by
    rw [← Equiv.swap_apply_apply, hub, Equiv.swap_comm]
  calc swap a (u a) * u = u * swap a (u a) * u⁻¹ * u := by rw [h1]
    _ = u * swap a (u a) := by group

end Index

theorem nonempty_mulEquiv_of_injective_of_card {G H : Type*} [Group G] [Group H] [Finite H]
    (φ : G →* H) (hφ : Function.Injective φ) (S : Subgroup H) (hle : φ.range ≤ S)
    (hcard : Nat.card S = Nat.card G) : Nonempty (G ≃* S) := by
  have hr : Nat.card φ.range = Nat.card G := (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have : φ.range = S := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hr])
  exact ⟨(MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr this)⟩

theorem card_centralizer_S7 (u : S7) :
    Nat.card (centralizer ({u} : Set S7)) =
      Nat.factorial (7 - u.cycleType.sum) * u.cycleType.prod *
        ∏ n ∈ u.cycleType.toFinset, Nat.factorial (u.cycleType.count n) := by
  simpa using Equiv.Perm.nat_card_centralizer u

theorem card_centralizer_S7_two {u : S7} (h : u.cycleType = {2}) :
    Nat.card (centralizer ({u} : Set S7)) = 240 := by
  rw [card_centralizer_S7, h]
  decide

theorem card_centralizer_S7_two_two {u : S7} (h : u.cycleType = {2, 2}) :
    Nat.card (centralizer ({u} : Set S7)) = 48 := by
  rw [card_centralizer_S7, h]
  decide

theorem card_centralizer_S7_two_two_two {u : S7} (h : u.cycleType = {2, 2, 2}) :
    Nat.card (centralizer ({u} : Set S7)) = 48 := by
  rw [card_centralizer_S7, h]
  decide

theorem sign_swap_ne {a b : Fin 7} (h : a ≠ b) : sign (swap a b) = -1 := sign_swap h

theorem card_centralizer_S7_eq_two_mul (u : S7) (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    Nat.card (centralizer ({u} : Set S7)) =
      2 * Nat.card ↥(centralizer ({u} : Set S7) ⊓ alternatingGroup (Fin 7)) := by
  obtain ⟨a, b, hab, -, hmem⟩ := exists_swap_mem_centralizer u hu hne
  exact card_inf_alternating _ hmem (sign_swap_ne hab)

theorem card_centralizer_A7_two {u : S7} (h : u.cycleType = {2}) (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    Nat.card ↥(centralizer ({u} : Set S7) ⊓ alternatingGroup (Fin 7)) = 120 := by
  have h1 := card_centralizer_S7_eq_two_mul u hu hne
  rw [card_centralizer_S7_two h] at h1
  omega

theorem card_centralizer_A7_two_two {u : S7} (h : u.cycleType = {2, 2}) (hu : u ^ 2 = 1)
    (hne : u ≠ 1) :
    Nat.card ↥(centralizer ({u} : Set S7) ⊓ alternatingGroup (Fin 7)) = 24 := by
  have h1 := card_centralizer_S7_eq_two_mul u hu hne
  rw [card_centralizer_S7_two_two h] at h1
  omega

theorem card_centralizer_A7_two_two_two {u : S7} (h : u.cycleType = {2, 2, 2}) (hu : u ^ 2 = 1)
    (hne : u ≠ 1) :
    Nat.card ↥(centralizer ({u} : Set S7) ⊓ alternatingGroup (Fin 7)) = 24 := by
  have h1 := card_centralizer_S7_eq_two_mul u hu hne
  rw [card_centralizer_S7_two_two_two h] at h1
  omega

@[expose] def ι5 : Fin 5 ↪ Fin 7 := Fin.castLEEmb (by norm_num)

@[expose] noncomputable def emb5 : Perm (Fin 5) →* S7 := Equiv.Perm.viaEmbeddingHom ι5

theorem emb5_apply_of_ge (σ : Perm (Fin 5)) (x : Fin 7) (hx : 5 ≤ x.val) : emb5 σ x = x := by
  classical
  exact Equiv.Perm.viaEmbedding_apply_of_notMem σ _ x (by
    rintro ⟨y, rfl⟩
    have h1 := y.isLt
    have h2 : (ι5 y).val = y.val := rfl
    omega)

theorem emb5_apply (σ : Perm (Fin 5)) (x : Fin 5) : emb5 σ (ι5 x) = ι5 (σ x) := by
  classical
  exact Equiv.Perm.viaEmbedding_apply σ _ x

theorem sign_emb5 (σ : Perm (Fin 5)) : sign (emb5 σ) = sign σ := by
  let _ : DecidablePred (fun x => x ∈ Set.range ι5) := fun x => Classical.propDecidable _
  exact sign_extendDomain σ (Equiv.ofInjective ι5 ι5.injective)

@[expose] noncomputable def w5 (σ : Perm (Fin 5)) : S7 := if sign σ = 1 then 1 else swap 5 6

theorem w5_mul (σ τ : Perm (Fin 5)) : w5 (σ * τ) = w5 σ * w5 τ := by
  unfold w5
  rw [sign_mul]
  rcases Int.units_eq_one_or (sign σ) with h1 | h1 <;>
    rcases Int.units_eq_one_or (sign τ) with h2 | h2 <;>
    simp [h1, h2, Equiv.swap_mul_self]

theorem sign_w5 (σ : Perm (Fin 5)) : sign (w5 σ) = sign σ := by
  unfold w5
  rcases Int.units_eq_one_or (sign σ) with h1 | h1
  · simp [h1]
  · simp [h1, sign_swap_ne (show (5 : Fin 7) ≠ 6 by decide)]

theorem w5_apply_of_lt (σ : Perm (Fin 5)) (x : Fin 7) (hx : x.val < 5) : w5 σ x = x := by
  unfold w5
  split_ifs
  · rfl
  · apply Equiv.swap_apply_of_ne_of_ne
    · intro h; rw [h] at hx; simp at hx
    · intro h; rw [h] at hx; simp at hx

theorem emb5_comm_swap56 (σ : Perm (Fin 5)) : emb5 σ * swap 5 6 = swap 5 6 * emb5 σ := by
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases h5 : x = 5
  · left; exact emb5_apply_of_ge σ x (by rw [h5]; decide)
  · by_cases h6 : x = 6
    · left; exact emb5_apply_of_ge σ x (by rw [h6]; decide)
    · right; exact Equiv.swap_apply_of_ne_of_ne h5 h6

theorem emb5_comm_w5 (σ τ : Perm (Fin 5)) : emb5 σ * w5 τ = w5 τ * emb5 σ := by
  unfold w5
  split_ifs
  · simp
  · exact emb5_comm_swap56 σ

@[expose] noncomputable def Phi5 : Perm (Fin 5) →* S7 where
  toFun σ := emb5 σ * w5 σ
  map_one' := by simp [w5]
  map_mul' σ τ := by
    simp only [map_mul, w5_mul]
    calc emb5 σ * emb5 τ * (w5 σ * w5 τ) = emb5 σ * (emb5 τ * w5 σ) * w5 τ := by group
      _ = emb5 σ * (w5 σ * emb5 τ) * w5 τ := by rw [emb5_comm_w5 τ σ]
      _ = emb5 σ * w5 σ * (emb5 τ * w5 τ) := by group

theorem Phi5_injective : Function.Injective Phi5 := by
  intro σ τ h
  apply Equiv.ext
  intro x
  have hx : (ι5 x).val < 5 := by simp [ι5]
  have h1 := congrArg (fun f : S7 => f (ι5 x)) h
  simp only [Phi5, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.mul_apply] at h1
  rw [w5_apply_of_lt σ _ hx, w5_apply_of_lt τ _ hx, emb5_apply, emb5_apply] at h1
  exact ι5.injective h1

theorem Phi5_mem (σ : Perm (Fin 5)) :
    Phi5 σ ∈ centralizer ({swap 5 6} : Set S7) ⊓ alternatingGroup (Fin 7) := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · show emb5 σ * w5 σ * swap 5 6 = swap 5 6 * (emb5 σ * w5 σ)
    have hw : w5 σ * swap 5 6 = swap 5 6 * w5 σ := by
      unfold w5
      split_ifs <;> simp
    calc emb5 σ * w5 σ * swap 5 6 = emb5 σ * (w5 σ * swap 5 6) := by group
      _ = emb5 σ * (swap 5 6 * w5 σ) := by rw [hw]
      _ = (emb5 σ * swap 5 6) * w5 σ := by group
      _ = swap 5 6 * emb5 σ * w5 σ := by rw [emb5_comm_swap56]
      _ = swap 5 6 * (emb5 σ * w5 σ) := by group
  · refine Equiv.Perm.mem_alternatingGroup.mpr ?_
    show sign (emb5 σ * w5 σ) = 1
    rw [sign_mul, sign_emb5, sign_w5, Int.units_mul_self]

theorem swap56_cycleType : (swap 5 6 : S7).cycleType = {2} :=
  Equiv.Perm.isSwap_iff_cycleType.mp ⟨5, 6, by decide, rfl⟩

theorem centralizer_A7_swap56_equiv :
    Nonempty (Perm (Fin 5) ≃* ↥(centralizer ({swap 5 6} : Set S7) ⊓ alternatingGroup (Fin 7))) := by
  refine nonempty_mulEquiv_of_injective_of_card Phi5 Phi5_injective _ ?_ ?_
  · rintro _ ⟨σ, rfl⟩
    exact Phi5_mem σ
  · rw [card_centralizer_A7_two swap56_cycleType (by decide +kernel) (by decide +kernel)]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide

theorem map_conj_centralizer_inf_alternating (c f : S7) :
    (centralizer ({f} : Set S7) ⊓ alternatingGroup (Fin 7)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * f * c⁻¹} : Set S7) ⊓ alternatingGroup (Fin 7) := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have hx : x * f = f * x := Subgroup.mem_centralizer_singleton_iff.mp hx1
      show c * x * c⁻¹ * (c * f * c⁻¹) = c * f * c⁻¹ * (c * x * c⁻¹)
      calc c * x * c⁻¹ * (c * f * c⁻¹) = c * (x * f) * c⁻¹ := by group
        _ = c * (f * x) * c⁻¹ := by rw [hx]
        _ = c * f * c⁻¹ * (c * x * c⁻¹) := by group
    · refine Equiv.Perm.mem_alternatingGroup.mpr ?_
      have := Equiv.Perm.mem_alternatingGroup.mp hx2
      show sign (c * x * c⁻¹) = 1
      rw [sign_mul, sign_mul, sign_inv, this]
      rw [mul_comm (sign c) 1, one_mul]
      exact Int.units_mul_self _
  · rintro ⟨hy1, hy2⟩
    refine ⟨c⁻¹ * y * c, ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩, ?_⟩
    · have hy : y * (c * f * c⁻¹) = c * f * c⁻¹ * y := Subgroup.mem_centralizer_singleton_iff.mp hy1
      calc c⁻¹ * y * c * f = c⁻¹ * (y * (c * f * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * f * c⁻¹ * y) * c := by rw [hy]
        _ = f * (c⁻¹ * y * c) := by group
    · refine Equiv.Perm.mem_alternatingGroup.mpr ?_
      rw [sign_conj_eq]
      exact Equiv.Perm.mem_alternatingGroup.mp hy2
    · show c * (c⁻¹ * y * c) * c⁻¹ = y
      group

theorem centralizer_A7_swap_equiv {f : S7} (hf : f.IsSwap) :
    Nonempty (↥(centralizer ({f} : Set S7) ⊓ alternatingGroup (Fin 7)) ≃* Perm (Fin 5)) := by
  obtain ⟨c, hc⟩ : ∃ c : S7, c * f * c⁻¹ = swap 5 6 := by
    have : IsConj f (swap 5 6) := Equiv.Perm.isConj_iff_cycleType_eq.mpr
      (by rw [Equiv.Perm.isSwap_iff_cycleType.mp hf, swap56_cycleType])
    exact isConj_iff.mp this
  obtain ⟨e56⟩ := centralizer_A7_swap56_equiv
  have hmap := map_conj_centralizer_inf_alternating c f
  rw [hc] at hmap
  let e1 := Subgroup.equivMapOfInjective (centralizer ({f} : Set S7) ⊓ alternatingGroup (Fin 7))
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  exact ⟨(e1.trans (MulEquiv.subgroupCongr hmap)).trans e56.symm⟩

theorem card_le_four_of_sq_eq_one (E : Subgroup S7) (hE : E ≤ alternatingGroup (Fin 7))
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using hsq x x.2
  obtain ⟨Sy, hSy⟩ := hE2.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_T0 Sy
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hE2
  set E' : Set S7 := (fun x => g⁻¹ * x * g) '' (E : Set S7) with hE'
  have hsub : E' ⊆ ↑(P0list.toFinset) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxT : x ∈ (Sy : Subgroup S7) ⊓ alternatingGroup (Fin 7) := ⟨hSy hx, hE hx⟩
    simpa using (mem_T_inf_A7 hg x).mp hxT
  have hinj : Function.Injective (fun x : S7 => g⁻¹ * x * g) := fun x y h => by
    simpa using h
  have hcardE' : E'.ncard = Nat.card E := by
    rw [hE', Set.ncard_image_of_injective _ hinj]
    exact (Nat.card_coe_set_eq _).symm
  have hle : E'.ncard ≤ 8 := by
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : P0list.toFinset.card = 8 := by decide +kernel
    omega
  by_contra hgt
  push Not at hgt
  have hn8 : Nat.card E = 8 := by
    have h2 : 2 ^ n ≤ 8 := by omega
    have h3 : n ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> simp_all
  have heq : E' = ↑(P0list.toFinset) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcardE', hn8, Set.ncard_coe_finset]; decide +kernel)
      (Finset.finite_toSet _)
  have hmem : r * f0 ∈ E' := by
    rw [heq]
    simp only [Finset.mem_coe, List.mem_toFinset]
    decide +kernel
  obtain ⟨x, hx, hxr⟩ := hmem
  have h1 := hsq x hx
  have h2 : (r * f0) * (r * f0) = 1 := by
    rw [← hxr]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [h1]; group
  exact absurd h2 (by decide +kernel)

@[expose] def klein (a b : S7) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    Subgroup S7 where
  carrier := {1, a, b, a * b}
  one_mem' := by simp
  mul_mem' := by
    have haab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have hbab : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
    have habaa : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
    have habb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
    have habab : a * b * (a * b) = 1 := by rw [← mul_assoc, habaa, hb]
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h'] <;>
      simp only [one_mul, mul_one, ha, hb, haab, hbab, habaa, habb, habab, hab.symm, true_or, or_true]
  inv_mem' := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    have hia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    rcases hx with h | h | h | h <;> rw [h]
    · simp
    · simp [hia]
    · simp [hib]
    · right; right; right; rw [mul_inv_rev, hia, hib, hab]

theorem mem_klein {a b : S7} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a} {x : S7} :
    x ∈ klein a b ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  show x ∈ ({1, a, b, a * b} : Set S7) ↔ _
  simp

theorem card_klein {a b : S7} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (klein a b ha hb hab) = 4 := by
  have h1 : (klein a b ha hb hab : Set S7) = {1, a, b, a * b} := rfl
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hne
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact (inv_eq_of_mul_eq_one_right ha).symm
  have hab2 : a * b ≠ a := fun h => hb1 (mul_eq_left.mp h)
  have hab3 : a * b ≠ b := fun h => ha1 (mul_eq_right.mp h)
  show Nat.card (klein a b ha hb hab : Set S7) = 4
  rw [h1, Nat.card_coe_set_eq]
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hab3.symm]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, hab2.symm⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha1.symm, hb1.symm, hab1.symm⟩

@[expose] def inv1 : S7 := swap 0 1

@[expose] def inv2 : S7 := swap 0 1 * swap 2 3

@[expose] def inv3 : S7 := swap 0 1 * swap 2 3 * swap 4 5

theorem inv1_cycleType : inv1.cycleType = {2} :=
  Equiv.Perm.isSwap_iff_cycleType.mp ⟨0, 1, by decide, rfl⟩

theorem inv2_cycleType : inv2.cycleType = {2, 2} := by
  rw [cycleType_replicate_two inv2 (by decide +kernel)]
  have : inv2.support.card = 4 := by decide +kernel
  rw [this]
  rfl

theorem inv3_cycleType : inv3.cycleType = {2, 2, 2} := by
  rw [cycleType_replicate_two inv3 (by decide +kernel)]
  have : inv3.support.card = 6 := by decide +kernel
  rw [this]
  rfl

theorem involution_cycleType (u : S7) (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    u.cycleType = {2} ∨ u.cycleType = {2, 2} ∨ u.cycleType = {2, 2, 2} := by
  have h := cycleType_replicate_two u hu
  have hle : u.support.card ≤ 7 := by
    simpa using Finset.card_le_univ u.support
  have hpos : 0 < u.support.card := by
    rw [Finset.card_pos]
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty, Equiv.Perm.support_eq_empty_iff] at h0
    exact hne h0
  have heven : 2 * (u.support.card / 2) = u.support.card := by
    have hs := Equiv.Perm.sum_cycleType u
    rw [h, Multiset.sum_replicate, smul_eq_mul] at hs
    omega
  rw [h]
  have hk : u.support.card / 2 = 1 ∨ u.support.card / 2 = 2 ∨ u.support.card / 2 = 3 := by omega
  rcases hk with hk | hk | hk <;> rw [hk]
  · left; rfl
  · right; left; rfl
  · right; right; rfl

theorem exists_conj_inv {u : S7} (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    (∃ c : S7, c * u * c⁻¹ = inv1) ∨ (∃ c : S7, c * u * c⁻¹ = inv2) ∨
      (∃ c : S7, c * u * c⁻¹ = inv3) := by
  rcases involution_cycleType u hu hne with h | h | h
  · left
    exact isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [h, inv1_cycleType]))
  · right; left
    exact isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [h, inv2_cycleType]))
  · right; right
    exact isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [h, inv3_cycleType]))

theorem klein_data_inv1 : ∃ a b : S7, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧
    a ≠ b ∧ sign a = 1 ∧ sign b = 1 ∧ a * inv1 = inv1 * a ∧ b * inv1 = inv1 * b :=
  ⟨swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem klein_data_inv2 : ∃ a b : S7, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧
    a ≠ b ∧ sign a = 1 ∧ sign b = 1 ∧ a * inv2 = inv2 * a ∧ b * inv2 = inv2 * b :=
  ⟨swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem klein_data_inv3 : ∃ a b : S7, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧
    a ≠ b ∧ sign a = 1 ∧ sign b = 1 ∧ a * inv3 = inv3 * a ∧ b * inv3 = inv3 * b :=
  ⟨swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem klein_data_conj {u v : S7} (c : S7) (hc : c * u * c⁻¹ = v)
    (h : ∃ a b : S7, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a ≠ b ∧ sign a = 1 ∧ sign b = 1 ∧ a * v = v * a ∧ b * v = v * b) :
    ∃ a b : S7, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a ≠ b ∧ sign a = 1 ∧ sign b = 1 ∧ a * u = u * a ∧ b * u = u * b := by
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne, hsa, hsb, hav, hbv⟩ := h
  have hu : u = c⁻¹ * v * c := by rw [← hc]; group
  have conj : ∀ x : S7, x * v = v * x → (c⁻¹ * x * c) * u = u * (c⁻¹ * x * c) := by
    intro x hx
    rw [hu]
    calc c⁻¹ * x * c * (c⁻¹ * v * c) = c⁻¹ * (x * v) * c := by group
      _ = c⁻¹ * (v * x) * c := by rw [hx]
      _ = c⁻¹ * v * c * (c⁻¹ * x * c) := by group
  refine ⟨c⁻¹ * a * c, c⁻¹ * b * c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, conj a hav, conj b hbv⟩
  · calc c⁻¹ * a * c * (c⁻¹ * a * c) = c⁻¹ * (a * a) * c := by group
      _ = 1 := by rw [ha]; group
  · calc c⁻¹ * b * c * (c⁻¹ * b * c) = c⁻¹ * (b * b) * c := by group
      _ = 1 := by rw [hb]; group
  · calc c⁻¹ * a * c * (c⁻¹ * b * c) = c⁻¹ * (a * b) * c := by group
      _ = c⁻¹ * (b * a) * c := by rw [hab]
      _ = c⁻¹ * b * c * (c⁻¹ * a * c) := by group
  · intro h
    apply ha1
    calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hb1
    calc b = c * (c⁻¹ * b * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hne
    calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      _ = c * (c⁻¹ * b * c) * c⁻¹ := by rw [h]
      _ = b := by group
  · rw [sign_conj_eq]; exact hsa
  · rw [sign_conj_eq]; exact hsb

theorem exists_klein_data (u : S7) (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    ∃ a b : S7, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧
      a ≠ b ∧ sign a = 1 ∧ sign b = 1 ∧ a * u = u * a ∧ b * u = u * b := by
  rcases exists_conj_inv hu hne with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact klein_data_conj c hc klein_data_inv1
  · exact klein_data_conj c hc klein_data_inv2
  · exact klein_data_conj c hc klein_data_inv3

theorem klein_in_centralizer (u : S7) (hu : u ^ 2 = 1) (hne : u ≠ 1) :
    ∃ E : Subgroup S7, E ≤ centralizer ({u} : Set S7) ⊓ alternatingGroup (Fin 7) ∧
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 4 := by
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne', hsa, hsb, hau, hbu⟩ := exists_klein_data u hu hne
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hbab : b * (a * b) = a := by rw [hab, ← mul_assoc, hb, one_mul]
  have habaa : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have habb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have habab : a * b * (a * b) = 1 := by rw [← mul_assoc, habaa, hb]
  refine ⟨klein a b ha hb hab, ?_, ?_, ?_, card_klein ha hb hab ha1 hb1 hne'⟩
  · intro x hx
    rw [mem_klein] at hx
    have habu : a * b * u = u * (a * b) := by
      calc a * b * u = a * (b * u) := by group
        _ = a * (u * b) := by rw [hbu]
        _ = (a * u) * b := by group
        _ = (u * a) * b := by rw [hau]
        _ = u * (a * b) := by group
    have hsab : sign (a * b) = 1 := by rw [sign_mul, hsa, hsb]; rfl
    rcases hx with h | h | h | h <;> rw [h]
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (by simp),
        Equiv.Perm.mem_alternatingGroup.mpr (by simp)⟩
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hau, Equiv.Perm.mem_alternatingGroup.mpr hsa⟩
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hbu, Equiv.Perm.mem_alternatingGroup.mpr hsb⟩
    · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr habu, Equiv.Perm.mem_alternatingGroup.mpr hsab⟩
  · intro x hx y hy
    rw [mem_klein] at hx hy
    rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h'] <;>
      simp only [one_mul, mul_one, haab, hbab, habaa, habb, hab.symm]
  · intro x hx
    rw [mem_klein] at hx
    rcases hx with h | h | h | h <;> rw [h]
    · simp
    · exact ha
    · exact hb
    · exact habab

theorem involutions_conj_alternating {x y : S7} (hx : x ∈ alternatingGroup (Fin 7))
    (hy : y ∈ alternatingGroup (Fin 7)) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) :
    ∃ c ∈ alternatingGroup (Fin 7), c * x * c⁻¹ = y := by
  have hxx : x ^ 2 = 1 := by have := pow_orderOf_eq_one x; rwa [hx2] at this
  have hyy : y ^ 2 = 1 := by have := pow_orderOf_eq_one y; rwa [hy2] at this
  have hx1 : x ≠ 1 := by
    rintro rfl; rw [orderOf_one] at hx2; omega
  have hy1 : y ≠ 1 := by
    rintro rfl; rw [orderOf_one] at hy2; omega
  have hcyc : ∀ {w : S7}, w ^ 2 = 1 → w ≠ 1 → w ∈ alternatingGroup (Fin 7) →
      w.cycleType = {2, 2} := by
    intro w hw hw1 hwA
    have hs := Equiv.Perm.mem_alternatingGroup.mp hwA
    rcases involution_cycleType w hw hw1 with h | h | h
    · exfalso
      rw [Equiv.Perm.sign_of_cycleType, h] at hs
      exact absurd hs (by decide)
    · exact h
    · exfalso
      rw [Equiv.Perm.sign_of_cycleType, h] at hs
      exact absurd hs (by decide)
  have hconj : IsConj x y := Equiv.Perm.isConj_iff_cycleType_eq.mpr
    (by rw [hcyc hxx hx1 hx, hcyc hyy hy1 hy])
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  by_cases hcs : sign c = 1
  · exact ⟨c, Equiv.Perm.mem_alternatingGroup.mpr hcs, hc⟩
  · have hcs' : sign c = -1 := by
      rcases Int.units_eq_one_or (sign c) with h | h
      · exact absurd h hcs
      · exact h
    obtain ⟨a, b, hab, hxa, hmem⟩ := exists_swap_mem_centralizer x hxx hx1
    have hw : swap a b * x = x * swap a b := (Subgroup.mem_centralizer_singleton_iff.mp hmem)
    refine ⟨c * swap a b, Equiv.Perm.mem_alternatingGroup.mpr ?_, ?_⟩
    · rw [sign_mul, hcs', sign_swap hab]; rfl
    · calc c * swap a b * x * (c * swap a b)⁻¹ = c * (swap a b * x * (swap a b)⁻¹) * c⁻¹ := by group
        _ = c * x * c⁻¹ := by
          have : swap a b * x * (swap a b)⁻¹ = x := by rw [hw]; group
          rw [this]
        _ = y := hc

@[expose] def D8list : List S7 := [1, r, r ^ 2, r ^ 3, s, s * r, s * r ^ 2, s * r ^ 3]

theorem mem_D8list_iff {x : S7} : x ∈ D8list ↔
    x = 1 ∨ x = r ∨ x = r ^ 2 ∨ x = r ^ 3 ∨ x = s ∨ x = s * r ∨ x = s * r ^ 2 ∨ x = s * r ^ 3 := by
  simp [D8list]

theorem D8_closed : ∀ x ∈ D8list, ∀ y ∈ D8list, x * y ∈ D8list := by
  intro x hx y hy
  rw [mem_D8list_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem D8_inv : ∀ x ∈ D8list, x⁻¹ ∈ D8list := by
  intro x hx
  rw [mem_D8list_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

@[expose] def D8 : Subgroup S7 where
  carrier := {x | x ∈ D8list}
  one_mem' := by decide +kernel
  mul_mem' := fun {x y} hx hy => D8_closed x hx y hy
  inv_mem' := fun {x} hx => D8_inv x hx

theorem mem_D8_iff {x : S7} : x ∈ D8 ↔ x ∈ D8list := Iff.rfl

theorem D8list_nodup : D8list.Nodup := by decide +kernel

theorem card_D8 : Nat.card D8 = 8 := by
  have h : (D8 : Set S7) = ↑(D8list.toFinset) := by
    ext x
    simp [mem_D8_iff]
  show Nat.card (D8 : Set S7) = 8
  rw [h]
  exact (Nat.card_eq_finsetCard D8list.toFinset).trans
    (by rw [List.toFinset_card_of_nodup D8list_nodup]; rfl)

theorem D8_fix : ∀ x ∈ D8list, ∀ i : Fin 7, 4 ≤ i.val → x i = i := by
  intro x hx
  rw [mem_D8list_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem D8_comm_rsq : ∀ x ∈ D8list, x * r ^ 2 = r ^ 2 * x := by
  intro x hx
  rw [mem_D8list_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem rsq_fix : ∀ i : Fin 7, 4 ≤ i.val → (r ^ 2) i = i := by decide +kernel

theorem rsq_sq : (r ^ 2) ^ 2 = 1 := by decide +kernel

theorem rsq_support : (r ^ 2).support.card = 4 := by decide +kernel

theorem rsq_cycleType : (r ^ 2 : S7).cycleType = {2, 2} := by
  rw [cycleType_replicate_two _ rsq_sq, rsq_support]
  rfl

theorem rsq_ne_one : (r ^ 2 : S7) ≠ 1 := by decide +kernel

@[expose] def ι3 : Fin 3 ↪ Fin 7 where
  toFun i := ⟨i.val + 4, by omega⟩
  inj' i j h := by
    apply Fin.ext
    have := congrArg Fin.val h
    simp at this
    exact this

@[expose] noncomputable def emb3 : Perm (Fin 3) →* S7 := Equiv.Perm.viaEmbeddingHom ι3

theorem emb3_injective : Function.Injective emb3 := Equiv.Perm.viaEmbeddingHom_injective ι3

theorem emb3_apply_of_lt (σ : Perm (Fin 3)) (x : Fin 7) (hx : x.val < 4) : emb3 σ x = x := by
  classical
  exact Equiv.Perm.viaEmbedding_apply_of_notMem σ _ x (by
    rintro ⟨y, rfl⟩
    have h1 := y.isLt
    have h2 : (ι3 y).val = y.val + 4 := rfl
    omega)

theorem emb3_comm {d : S7} (hd : ∀ i : Fin 7, 4 ≤ i.val → d i = i) (σ : Perm (Fin 3)) :
    d * emb3 σ = emb3 σ * d := by
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases hx : 4 ≤ x.val
  · left; exact hd x hx
  · right; exact emb3_apply_of_lt σ x (by omega)

theorem PsiD_comm (d : D8) (σ : Perm (Fin 3)) : Commute (D8.subtype d) (emb3 σ) :=
  emb3_comm (fun i hi => D8_fix d.1 d.2 i hi) σ

noncomputable def PsiD : D8 × Perm (Fin 3) →* S7 :=
  MonoidHom.noncommCoprod D8.subtype emb3 PsiD_comm

theorem PsiD_apply (d : D8) (σ : Perm (Fin 3)) : PsiD (d, σ) = (d : S7) * emb3 σ :=
  MonoidHom.noncommCoprod_apply _ _ _ _

theorem PsiD_injective : Function.Injective PsiD := by
  rw [injective_iff_map_eq_one]
  rintro ⟨d, σ⟩ h
  rw [PsiD_apply] at h
  have hd : (d : S7) = 1 := by
    apply Equiv.ext
    intro x
    by_cases hx : 4 ≤ x.val
    · exact (D8_fix d.1 d.2 x hx).trans rfl
    · have := congrArg (fun f : S7 => f x) h
      simp only [Equiv.Perm.mul_apply, emb3_apply_of_lt σ x (by omega)] at this
      simpa using this
  have hσ : emb3 σ = 1 := by
    rw [hd, one_mul] at h
    exact h
  have hσ' : σ = 1 := emb3_injective (by rw [hσ, map_one])
  have hd' : d = 1 := Subtype.ext hd
  simp [hd', hσ']

theorem PsiD_mem (d : D8) (σ : Perm (Fin 3)) : PsiD (d, σ) ∈ centralizer ({r ^ 2} : Set S7) := by
  rw [PsiD_apply]
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have hd := D8_comm_rsq d.1 d.2
  have he : emb3 σ * r ^ 2 = r ^ 2 * emb3 σ := (emb3_comm rsq_fix σ).symm
  calc (d : S7) * emb3 σ * r ^ 2 = d * (emb3 σ * r ^ 2) := by group
    _ = d * (r ^ 2 * emb3 σ) := by rw [he]
    _ = (d * r ^ 2) * emb3 σ := by group
    _ = r ^ 2 * d * emb3 σ := by rw [hd]
    _ = r ^ 2 * (d * emb3 σ) := by group

theorem card_centralizer_rsq : Nat.card (centralizer ({r ^ 2} : Set S7)) = 48 :=
  card_centralizer_S7_two_two rsq_cycleType

theorem centralizer_rsq_equiv :
    Nonempty ((D8 × Perm (Fin 3)) ≃* ↥(centralizer ({r ^ 2} : Set S7))) := by
  refine nonempty_mulEquiv_of_injective_of_card PsiD PsiD_injective _ ?_ ?_
  · rintro _ ⟨⟨d, σ⟩, rfl⟩
    exact PsiD_mem d σ
  · rw [card_centralizer_rsq, Nat.card_prod, card_D8]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide

theorem range_PsiD : PsiD.range = centralizer ({r ^ 2} : Set S7) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨⟨d, σ⟩, rfl⟩
    exact PsiD_mem d σ
  · rw [card_centralizer_rsq]
    have : Nat.card PsiD.range = Nat.card (D8 × Perm (Fin 3)) :=
      (Nat.card_congr (MonoidHom.ofInjective PsiD_injective).toEquiv).symm
    rw [this, Nat.card_prod, card_D8]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide

theorem map_conj_centralizer_singleton (c f : S7) :
    (centralizer ({f} : Set S7)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * f * c⁻¹} : Set S7) := by
  ext y
  constructor
  · rintro ⟨x, hx1, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hx : x * f = f * x := Subgroup.mem_centralizer_singleton_iff.mp hx1
    show c * x * c⁻¹ * (c * f * c⁻¹) = c * f * c⁻¹ * (c * x * c⁻¹)
    calc c * x * c⁻¹ * (c * f * c⁻¹) = c * (x * f) * c⁻¹ := by group
      _ = c * (f * x) * c⁻¹ := by rw [hx]
      _ = c * f * c⁻¹ * (c * x * c⁻¹) := by group
  · intro hy1
    refine ⟨c⁻¹ * y * c, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · have hy : y * (c * f * c⁻¹) = c * f * c⁻¹ * y := Subgroup.mem_centralizer_singleton_iff.mp hy1
      calc c⁻¹ * y * c * f = c⁻¹ * (y * (c * f * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * f * c⁻¹ * y) * c := by rw [hy]
        _ = f * (c⁻¹ * y * c) := by group
    · show c * (c⁻¹ * y * c) * c⁻¹ = y
      group

theorem centralizer_conj_equiv (c f : S7) :
    Nonempty (↥(centralizer ({f} : Set S7)) ≃* ↥(centralizer ({c * f * c⁻¹} : Set S7))) :=
  ⟨(Subgroup.equivMapOfInjective _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
    (MulEquiv.subgroupCongr (map_conj_centralizer_singleton c f))⟩

theorem T_le_centralizer {T : Sylow 2 S7} {g : S7}
    (hg : ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0) {z : S7}
    (hzT : z ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7))
    (hc : ∀ x ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7), x * z = z * x) :
    (T : Subgroup S7) ≤ centralizer ({z} : Set S7) := by
  intro x hx
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  by_cases hs : sign x = 1
  · exact hc x ⟨hx, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
  · have hs' : sign x = -1 := by
      rcases Int.units_eq_one_or (sign x) with h | h
      · exact absurd h hs
      · exact h
    have hfT : g * f0 * g⁻¹ ∈ (T : Subgroup S7) := fT_mem hg
    have hfs : sign (g * f0 * g⁻¹) = -1 := fT_isSwap.sign_eq
    have hxf : x * (g * f0 * g⁻¹) ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) := by
      refine ⟨Subgroup.mul_mem _ hx hfT, Equiv.Perm.mem_alternatingGroup.mpr ?_⟩
      rw [sign_mul, hs', hfs]
      rfl
    have h1 := hc _ hxf
    have h2 := fT_comm hg z hzT
    have h4 : x * z * (g * f0 * g⁻¹) = z * x * (g * f0 * g⁻¹) := by
      calc x * z * (g * f0 * g⁻¹) = x * (z * (g * f0 * g⁻¹)) := by group
        _ = x * ((g * f0 * g⁻¹) * z) := by rw [h2]
        _ = x * (g * f0 * g⁻¹) * z := by group
        _ = z * (x * (g * f0 * g⁻¹)) := h1
        _ = z * x * (g * f0 * g⁻¹) := by group
    exact mul_right_cancel h4

theorem c3_sq : (swap 4 5 * swap 5 6 : S7) ^ 3 = 1 := by decide +kernel

theorem c3_ne : (swap 4 5 * swap 5 6 : S7) ≠ 1 := by decide +kernel

theorem c3_order : orderOf (swap 4 5 * swap 5 6 : S7) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime c3_sq c3_ne

theorem c3_fix : ∀ i : Fin 7, i.val < 4 → (swap 4 5 * swap 5 6 : S7) i = i := by decide +kernel

theorem c3_comm_rsq : (swap 4 5 * swap 5 6 : S7) * r ^ 2 = r ^ 2 * (swap 4 5 * swap 5 6) := by
  decide +kernel

theorem central_involution_data {T : Sylow 2 S7} {g : S7}
    (hg : ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0) {z : S7}
    (hzT : z ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7)) (hz2 : orderOf z = 2)
    (hc : ∀ x ∈ (T : Subgroup S7) ⊓ alternatingGroup (Fin 7), x * z = z * x) :
    Nonempty (↥(centralizer ({z} : Set S7)) ≃* (D8 × Perm (Fin 3))) ∧
      ∃ X : Subgroup S7, Nat.card X = 3 ∧ X ⊔ (T : Subgroup S7) = centralizer ({z} : Set S7) := by
  have hz : z = g * r ^ 2 * g⁻¹ := central_involution_eq hg hzT hz2 hc
  obtain ⟨e1⟩ := centralizer_rsq_equiv
  obtain ⟨e2⟩ := centralizer_conj_equiv g (r ^ 2)
  refine ⟨⟨(by rw [hz]; exact e2.symm.trans e1.symm : ↥(centralizer ({z} : Set S7)) ≃* _)⟩, ?_⟩
  have hcard : Nat.card ↥(centralizer ({z} : Set S7)) = 48 := by
    rw [hz]
    apply card_centralizer_S7_two_two
    have : g * r ^ 2 * g⁻¹ = (g⁻¹)⁻¹ * r ^ 2 * g⁻¹ := by simp
    rw [this, cycleType_conj_inv, rsq_cycleType]
  refine ⟨Subgroup.zpowers (g * (swap 4 5 * swap 5 6) * g⁻¹), ?_, ?_⟩
  · rw [Nat.card_zpowers]
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      (swap 4 5 * swap 5 6 : S7)
    simpa [MulAut.conj_apply, c3_order] using this
  · have hTle := T_le_centralizer hg hzT hc
    have hXle : Subgroup.zpowers (g * (swap 4 5 * swap 5 6) * g⁻¹) ≤ centralizer ({z} : Set S7) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hcomm : (swap 4 5 * swap 5 6 : S7) * r ^ 2 = r ^ 2 * (swap 4 5 * swap 5 6) :=
        c3_comm_rsq
      rw [hz]
      calc g * (swap 4 5 * swap 5 6) * g⁻¹ * (g * r ^ 2 * g⁻¹)
          = g * ((swap 4 5 * swap 5 6) * r ^ 2) * g⁻¹ := by group
        _ = g * (r ^ 2 * (swap 4 5 * swap 5 6)) * g⁻¹ := by rw [hcomm]
        _ = g * r ^ 2 * g⁻¹ * (g * (swap 4 5 * swap 5 6) * g⁻¹) := by group
    apply Subgroup.eq_of_le_of_card_ge (sup_le hXle hTle)
    rw [hcard]
    have hX3 : 3 ∣ Nat.card ↥(Subgroup.zpowers (g * (swap 4 5 * swap 5 6) * g⁻¹) ⊔
        (T : Subgroup S7)) := by
      have h1 := Subgroup.card_dvd_of_le
        (le_sup_left : Subgroup.zpowers (g * (swap 4 5 * swap 5 6) * g⁻¹) ≤
          Subgroup.zpowers (g * (swap 4 5 * swap 5 6) * g⁻¹) ⊔ (T : Subgroup S7))
      rw [Nat.card_zpowers] at h1
      have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
        (swap 4 5 * swap 5 6 : S7)
      simp [MulAut.conj_apply, c3_order] at this
      rw [this] at h1
      exact h1
    have h16 : 16 ∣ Nat.card ↥(Subgroup.zpowers (g * (swap 4 5 * swap 5 6) * g⁻¹) ⊔
        (T : Subgroup S7)) := by
      have h1 := Subgroup.card_dvd_of_le
        (le_sup_right : (T : Subgroup S7) ≤
          Subgroup.zpowers (g * (swap 4 5 * swap 5 6) * g⁻¹) ⊔ (T : Subgroup S7))
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hT16 : Nat.card (T : Subgroup S7) = 16 := by
        rw [Sylow.card_eq_multiplicity, factorization_S7]
        norm_num
      rw [hT16] at h1
      exact h1
    have h48 : 48 ∣ Nat.card ↥(Subgroup.zpowers (g * (swap 4 5 * swap 5 6) * g⁻¹) ⊔
        (T : Subgroup S7)) := by
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 16) hX3 h16
      simpa using this
    exact Nat.le_of_dvd Nat.card_pos h48

theorem T0_inf_A7_coe : ((T0 ⊓ alternatingGroup (Fin 7) : Subgroup S7) : Set S7) = ↑(P0list.toFinset) := by
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    have h1 : x ∈ T0list := hx1
    have h2 : sign x = 1 := Equiv.Perm.mem_alternatingGroup.mp hx2
    simpa using (T0list_even_iff x h1).mp h2
  · intro hx
    have hx' : x ∈ P0list := by simpa using hx
    exact ⟨P0list_sub x hx', Equiv.Perm.mem_alternatingGroup.mpr (P0list_even x hx')⟩

theorem P0list_nodup : P0list.Nodup := by decide +kernel

theorem card_T0_inf_A7 : Nat.card ↥(T0 ⊓ alternatingGroup (Fin 7)) = 8 := by
  show Nat.card ((T0 ⊓ alternatingGroup (Fin 7) : Subgroup S7) : Set S7) = 8
  rw [T0_inf_A7_coe]
  exact (Nat.card_eq_finsetCard P0list.toFinset).trans
    (by rw [List.toFinset_card_of_nodup P0list_nodup]; rfl)

theorem T_inf_A7_eq_map {T : Sylow 2 S7} {g : S7}
    (hg : ∀ x : S7, x ∈ (T : Subgroup S7) ↔ g⁻¹ * x * g ∈ T0) :
    (T : Subgroup S7) ⊓ alternatingGroup (Fin 7) =
      (T0 ⊓ alternatingGroup (Fin 7)).map (MulAut.conj g).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨hy1, hy2⟩
    refine ⟨g⁻¹ * y * g, ⟨(hg y).mp hy1, ?_⟩, ?_⟩
    · refine Equiv.Perm.mem_alternatingGroup.mpr ?_
      rw [sign_conj_eq]
      exact Equiv.Perm.mem_alternatingGroup.mp hy2
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
  · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
    refine ⟨(hg _).mpr ?_, ?_⟩
    · show g⁻¹ * (g * x * g⁻¹) * g ∈ T0
      have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [this]
      exact hx1
    · refine Equiv.Perm.mem_alternatingGroup.mpr ?_
      have h1 := Equiv.Perm.mem_alternatingGroup.mp hx2
      have h2 := sign_conj_eq g⁻¹ x
      simp only [inv_inv] at h2
      show sign (g * x * g⁻¹) = 1
      rw [h2]
      exact h1

section Edges

open scoped Pointwise

abbrev Edge : Type := Set.powersetCard (Fin 4) 2

theorem card_Edge : Nat.card Edge = 6 := by
  rw [Set.powersetCard.card]
  simp [Nat.card_eq_fintype_card]
  decide

@[expose] noncomputable def eE : Fin 6 ≃ Edge := (Finite.equivFinOfCardEq card_Edge).symm

@[expose] noncomputable def rho6 : Perm (Fin 4) →* Perm (Fin 6) :=
  (Equiv.permCongrHom eE.symm).toMonoidHom.comp (MulAction.toPermHom (Perm (Fin 4)) Edge)

@[expose] def ι6 : Fin 6 ↪ Fin 7 := Fin.castLEEmb (by norm_num)

@[expose] noncomputable def emb6 : Perm (Fin 6) →* S7 := Equiv.Perm.viaEmbeddingHom ι6

@[expose] noncomputable def Phi0 : Perm (Fin 4) →* S7 := emb6.comp rho6

theorem rho6_apply (σ : Perm (Fin 4)) (i : Fin 6) : rho6 σ i = eE.symm (σ • eE i) := by
  simp [rho6, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem rho6_apply_eq_iff (σ : Perm (Fin 4)) (i j : Fin 6) :
    rho6 σ i = j ↔ σ • eE i = eE j := by
  rw [rho6_apply, Equiv.symm_apply_eq]

theorem emb6_apply_of_ge (σ : Perm (Fin 6)) (x : Fin 7) (hx : 6 ≤ x.val) : emb6 σ x = x := by
  classical
  exact Equiv.Perm.viaEmbedding_apply_of_notMem σ _ x (by
    rintro ⟨y, rfl⟩
    have h1 := y.isLt
    have h2 : (ι6 y).val = y.val := rfl
    omega)

theorem emb6_apply (σ : Perm (Fin 6)) (x : Fin 6) : emb6 σ (ι6 x) = ι6 (σ x) := by
  classical
  exact Equiv.Perm.viaEmbedding_apply σ _ x

theorem emb6_injective : Function.Injective emb6 := Equiv.Perm.viaEmbeddingHom_injective ι6

theorem sign_emb6 (σ : Perm (Fin 6)) : sign (emb6 σ) = sign σ := by
  let _ : DecidablePred (fun x => x ∈ Set.range ι6) := fun x => Classical.propDecidable _
  exact sign_extendDomain σ (Equiv.ofInjective ι6 ι6.injective)

theorem rho6_injective : Function.Injective rho6 := by
  rw [injective_iff_map_eq_one]
  intro σ h
  have hfix : ∀ s : Edge, σ • s = s := by
    intro s
    obtain ⟨i, rfl⟩ := eE.surjective s
    have := congrArg (fun π : Perm (Fin 6) => π i) h
    simp only [Equiv.Perm.coe_one, id_eq] at this
    exact (rho6_apply_eq_iff σ i i).mp this
  have hfix' : ∀ s : Finset (Fin 4), s.card = 2 → σ • s = s := by
    intro s hs
    have := hfix ⟨s, hs⟩
    exact congrArg Subtype.val this
  apply Equiv.ext
  intro x
  have key : ∀ x : Fin 4, ∃ y z : Fin 4, y ≠ z ∧ x ≠ y ∧ x ≠ z := by decide
  obtain ⟨y, z, hyz, hxy, hxz⟩ := key x
  have h1 := hfix' {x, y} (by simp [Finset.card_pair hxy])
  have h2 := hfix' {x, z} (by simp [Finset.card_pair hxz])
  have hx1 : σ x ∈ ({x, y} : Finset (Fin 4)) := by
    rw [← h1]; simp [Finset.mem_smul_finset]
  have hx2 : σ x ∈ ({x, z} : Finset (Fin 4)) := by
    rw [← h2]; simp [Finset.mem_smul_finset]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
  rcases hx1 with h | h
  · simpa using h
  · rcases hx2 with h' | h'
    · simpa using h'
    · exact absurd (h.symm.trans h') hyz

end Edges

section Edges2

open scoped Pointwise

@[expose] def cmpE : Perm Edge :=
  Function.Involutive.toPerm
    (fun s : Edge => (⟨s.1ᶜ, by
      have h : s.1.card = 2 := s.2
      show s.1ᶜ.card = 2
      rw [Finset.card_compl, h]
      rfl⟩ : Edge))
    (fun s => Subtype.ext (compl_compl s.1))

theorem cmpE_apply (s : Edge) : (cmpE s).1 = s.1ᶜ := rfl

theorem cmpE_cmpE (s : Edge) : cmpE (cmpE s) = s := Subtype.ext (compl_compl s.1)

theorem cmpE_ne (s : Edge) : cmpE s ≠ s := by
  intro h
  have h1 : s.1ᶜ = s.1 := congrArg Subtype.val h
  have h2 : s.1.card = 2 := s.2
  have h3 : s.1 = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have : x ∈ s.1ᶜ := by rw [h1]; exact hx
    exact (Finset.mem_compl.mp this) hx
  rw [h3] at h2
  simp at h2

theorem cmpE_comm (σ : Perm (Fin 4)) (s : Edge) : cmpE (σ • s) = σ • cmpE s := by
  apply Subtype.ext
  show (σ • s.1)ᶜ = σ • s.1ᶜ
  ext x
  rw [Finset.mem_compl, ← Finset.inv_smul_mem_iff, ← Finset.inv_smul_mem_iff, Finset.mem_compl]

@[expose] noncomputable def cmp6 : Perm (Fin 6) := Equiv.permCongr eE.symm cmpE

theorem cmp6_apply (x : Fin 6) : cmp6 x = eE.symm (cmpE (eE x)) := by
  simp [cmp6, Equiv.permCongr_apply]

theorem cmp6_sq : cmp6 * cmp6 = 1 := by
  apply Equiv.ext
  intro x
  simp [Equiv.Perm.mul_apply, cmp6_apply, cmpE_cmpE]

theorem cmp6_ne (x : Fin 6) : cmp6 x ≠ x := by
  intro h
  rw [cmp6_apply, Equiv.symm_apply_eq] at h
  exact cmpE_ne _ h

theorem rho6_comm_cmp6 (σ : Perm (Fin 4)) : rho6 σ * cmp6 = cmp6 * rho6 σ := by
  apply Equiv.ext
  intro x
  simp only [Equiv.Perm.mul_apply, rho6_apply, cmp6_apply, Equiv.apply_symm_apply]
  have h := cmpE_comm σ (eE x)
  rw [h]

@[expose] noncomputable def c0 : S7 := emb6 cmp6

theorem c0_sq : c0 ^ 2 = 1 := by
  rw [pow_two, c0, ← map_mul, cmp6_sq, map_one]

theorem c0_support : c0.support = Finset.univ.image ι6 := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Equiv.Perm.mem_support] at hx
    by_contra hxn
    have hx6 : 6 ≤ x.val := by
      by_contra h
      apply hxn
      refine Finset.mem_image.mpr ⟨⟨x.val, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rfl
    exact hx (emb6_apply_of_ge cmp6 x hx6)
  · rw [Finset.card_image_of_injective _ ι6.injective]
    have h1 : (Finset.univ.image ι6 : Finset (Fin 7)) ⊆ c0.support := by
      intro y hy
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Equiv.Perm.mem_support]
      intro h
      rw [c0, emb6_apply] at h
      exact cmp6_ne x (ι6.injective h)
    have h2 := Finset.card_le_card h1
    rwa [Finset.card_image_of_injective _ ι6.injective] at h2

theorem c0_cycleType : c0.cycleType = {2, 2, 2} := by
  rw [cycleType_replicate_two c0 c0_sq, c0_support, Finset.card_image_of_injective _ ι6.injective]
  rfl

theorem sign_c0 : sign c0 = -1 := by
  rw [Equiv.Perm.sign_of_cycleType, c0_cycleType]
  decide

theorem Phi0_comm_c0 (σ : Perm (Fin 4)) : Phi0 σ * c0 = c0 * Phi0 σ := by
  show emb6 (rho6 σ) * emb6 cmp6 = emb6 cmp6 * emb6 (rho6 σ)
  rw [← map_mul, ← map_mul, rho6_comm_cmp6]

theorem Phi0_injective : Function.Injective Phi0 := by
  intro σ τ h
  exact rho6_injective (emb6_injective h)

theorem Phi0_ne_c0 (σ : Perm (Fin 4)) : Phi0 σ ≠ c0 := by
  intro h
  have h1 : rho6 σ = cmp6 := emb6_injective h
  have hs : ∀ s : Edge, σ • s = cmpE s := by
    intro s
    obtain ⟨i, rfl⟩ := eE.surjective s
    have := congrArg (fun π : Perm (Fin 6) => π i) h1
    simp only [rho6_apply, cmp6_apply] at this
    exact eE.symm.injective this
  have hmem : ∀ t : Finset (Fin 4), ∀ ht : t.card = 2, (0 : Fin 4) ∈ t →
      σ 0 ∈ (⟨t, ht⟩ : Edge).1ᶜ := by
    intro t ht h0
    have h2 := hs ⟨t, ht⟩
    have h3 : (σ • (⟨t, ht⟩ : Edge)).1 = (cmpE ⟨t, ht⟩).1 := congrArg Subtype.val h2
    rw [cmpE_apply] at h3
    rw [← h3]
    show σ 0 ∈ σ • t
    exact (Finset.smul_mem_smul_finset_iff (a := σ) (b := (0 : Fin 4))).mpr h0
  have e1 := hmem {0, 1} (by decide) (by simp)
  have e2 := hmem {0, 2} (by decide) (by simp)
  have e3 := hmem {0, 3} (by decide) (by simp)
  generalize σ 0 = y at e1 e2 e3
  revert y
  decide

end Edges2

section Edges3

theorem c0_mul_self : c0 * c0 = 1 := by rw [← pow_two]; exact c0_sq

theorem c0_ne_one : c0 ≠ 1 := by
  intro h
  have := congrArg (fun f : S7 => f.cycleType) h
  simp [c0_cycleType] at this

@[expose] noncomputable def kap (x : S7) : S7 := if sign x = 1 then 1 else c0

theorem kap_comm (x : S7) : kap x * c0 = c0 * kap x := by
  unfold kap
  split_ifs <;> simp

theorem kap_mul (x y : S7) : kap (x * y) = kap x * kap y := by
  unfold kap
  rw [sign_mul]
  rcases Int.units_eq_one_or (sign x) with h1 | h1 <;>
    rcases Int.units_eq_one_or (sign y) with h2 | h2 <;>
    simp [h1, h2, c0_mul_self]

theorem kap_comm_Phi0 (x : S7) (τ : Perm (Fin 4)) : kap x * Phi0 τ = Phi0 τ * kap x := by
  unfold kap
  split_ifs
  · simp
  · exact (Phi0_comm_c0 τ).symm

@[expose] noncomputable def Phi : Perm (Fin 4) →* S7 where
  toFun σ := Phi0 σ * kap (Phi0 σ)
  map_one' := by simp [kap]
  map_mul' σ τ := by
    simp only [map_mul, kap_mul]
    calc Phi0 σ * Phi0 τ * (kap (Phi0 σ) * kap (Phi0 τ))
        = Phi0 σ * (Phi0 τ * kap (Phi0 σ)) * kap (Phi0 τ) := by group
      _ = Phi0 σ * (kap (Phi0 σ) * Phi0 τ) * kap (Phi0 τ) := by rw [kap_comm_Phi0 _ τ]
      _ = Phi0 σ * kap (Phi0 σ) * (Phi0 τ * kap (Phi0 τ)) := by group

theorem Phi_mem (σ : Perm (Fin 4)) :
    Phi σ ∈ centralizer ({c0} : Set S7) ⊓ alternatingGroup (Fin 7) := by
  refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · show Phi0 σ * kap (Phi0 σ) * c0 = c0 * (Phi0 σ * kap (Phi0 σ))
    calc Phi0 σ * kap (Phi0 σ) * c0 = Phi0 σ * (kap (Phi0 σ) * c0) := by group
      _ = Phi0 σ * (c0 * kap (Phi0 σ)) := by rw [kap_comm]
      _ = (Phi0 σ * c0) * kap (Phi0 σ) := by group
      _ = (c0 * Phi0 σ) * kap (Phi0 σ) := by rw [Phi0_comm_c0]
      _ = c0 * (Phi0 σ * kap (Phi0 σ)) := by group
  · refine Equiv.Perm.mem_alternatingGroup.mpr ?_
    show sign (Phi0 σ * kap (Phi0 σ)) = 1
    rw [sign_mul]
    unfold kap
    rcases Int.units_eq_one_or (sign (Phi0 σ)) with h | h
    · simp [h]
    · simp [h, sign_c0]

theorem Phi_injective : Function.Injective Phi := by
  rw [injective_iff_map_eq_one]
  intro σ h
  have h' : Phi0 σ * kap (Phi0 σ) = 1 := h
  unfold kap at h'
  rcases Int.units_eq_one_or (sign (Phi0 σ)) with hs | hs
  · simp only [hs, ↓reduceIte, mul_one] at h'
    exact Phi0_injective (by rw [h', map_one])
  · exfalso
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    have h'' : Phi0 σ * c0 = 1 := by simpa [hs, hne] using h'
    have : Phi0 σ = c0 := by
      rw [mul_eq_one_iff_eq_inv] at h''
      rw [h'']
      exact inv_eq_of_mul_eq_one_right c0_mul_self
    exact Phi0_ne_c0 σ this

theorem centralizer_A7_c0_equiv :
    Nonempty (Perm (Fin 4) ≃* ↥(centralizer ({c0} : Set S7) ⊓ alternatingGroup (Fin 7))) := by
  refine nonempty_mulEquiv_of_injective_of_card Phi Phi_injective _ ?_ ?_
  · rintro _ ⟨σ, rfl⟩
    exact Phi_mem σ
  · rw [card_centralizer_A7_two_two_two c0_cycleType c0_sq c0_ne_one]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide

theorem centralizer_A7_two_two_two_equiv {u : S7} (h : u.cycleType = {2, 2, 2}) :
    Nonempty (↥(centralizer ({u} : Set S7) ⊓ alternatingGroup (Fin 7)) ≃* Perm (Fin 4)) := by
  obtain ⟨c, hc⟩ : ∃ c : S7, c * u * c⁻¹ = c0 := by
    have : IsConj u c0 := Equiv.Perm.isConj_iff_cycleType_eq.mpr (by rw [h, c0_cycleType])
    exact isConj_iff.mp this
  obtain ⟨e0⟩ := centralizer_A7_c0_equiv
  have hmap := map_conj_centralizer_inf_alternating c u
  rw [hc] at hmap
  let e1 := Subgroup.equivMapOfInjective (centralizer ({u} : Set S7) ⊓ alternatingGroup (Fin 7))
    (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  exact ⟨(e1.trans (MulEquiv.subgroupCongr hmap)).trans e0.symm⟩

end Edges3

section Four

@[expose] def S3list : List S7 :=
  [1, swap 4 5, swap 4 6, swap 5 6, swap 4 5 * swap 5 6, (swap 4 5 * swap 5 6) ^ 2]

theorem mem_S3list_iff {x : S7} : x ∈ S3list ↔
    x = 1 ∨ x = swap 4 5 ∨ x = swap 4 6 ∨ x = swap 5 6 ∨ x = swap 4 5 * swap 5 6 ∨
      x = (swap 4 5 * swap 5 6) ^ 2 := by
  simp [S3list]

@[expose] def C48list : List S7 := D8list.flatMap (fun d => S3list.map (fun e => d * e))

theorem mem_C48list_iff {x : S7} : x ∈ C48list ↔ ∃ d ∈ D8list, ∃ e ∈ S3list, x = d * e := by
  simp only [C48list, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨d, hd, e, he, rfl⟩
    exact ⟨d, hd, e, he, rfl⟩
  · rintro ⟨d, hd, e, he, rfl⟩
    exact ⟨d, hd, e, he, rfl⟩

theorem C48list_nodup : C48list.Nodup := by decide +kernel

theorem S3_comm_rsq : ∀ e ∈ S3list, e * r ^ 2 = r ^ 2 * e := by
  intro e he
  rw [mem_S3list_iff] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem C48list_subset : ∀ x ∈ C48list, x * r ^ 2 = r ^ 2 * x := by
  intro x hx
  obtain ⟨d, hd, e, he, rfl⟩ := mem_C48list_iff.mp hx
  have h1 := D8_comm_rsq d hd
  have h2 := S3_comm_rsq e he
  calc d * e * r ^ 2 = d * (e * r ^ 2) := by group
    _ = d * (r ^ 2 * e) := by rw [h2]
    _ = (d * r ^ 2) * e := by group
    _ = (r ^ 2 * d) * e := by rw [h1]
    _ = r ^ 2 * (d * e) := by group

theorem centralizer_rsq_eq : (centralizer ({r ^ 2} : Set S7) : Set S7) = ↑(C48list.toFinset) := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro x hx
    have : x ∈ C48list := by simpa using hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (C48list_subset x this)
  · rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup C48list_nodup]
    have h2 : ((centralizer ({r ^ 2} : Set S7) : Set S7)).ncard = 48 := by
      rw [← Nat.card_coe_set_eq]
      exact card_centralizer_rsq
    rw [h2]
    simp [C48list, D8list, S3list]
  · exact Set.toFinite _

theorem mem_C48list_of_commute {x : S7} (hx : x * r ^ 2 = r ^ 2 * x) : x ∈ C48list := by
  have : x ∈ (centralizer ({r ^ 2} : Set S7) : Set S7) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hx
  rw [centralizer_rsq_eq] at this
  simpa using this

end Four

section Classify

theorem klein_le (K : Subgroup S7) {a b : S7} {ha : a * a = 1} {hb : b * b = 1}
    {hab : a * b = b * a} (h1 : a ∈ K) (h2 : b ∈ K) : klein a b ha hb hab ≤ K := by
  intro x hx
  rw [mem_klein] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact K.one_mem
  · exact h1
  · exact h2
  · exact K.mul_mem h1 h2

theorem klein_eq_klein {a b a' b' : S7} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}
    {ha' : a' * a' = 1} {hb' : b' * b' = 1} {hab' : a' * b' = b' * a'}
    (h1 : a' ∈ klein a b ha hb hab) (h2 : b' ∈ klein a b ha hb hab)
    (h3 : a ∈ klein a' b' ha' hb' hab') (h4 : b ∈ klein a' b' ha' hb' hab') :
    klein a b ha hb hab = klein a' b' ha' hb' hab' :=
  le_antisymm (klein_le _ h3 h4) (klein_le _ h1 h2)

theorem klein_map_conj (a b : S7) (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (c : S7)
    (ha' : (c * a * c⁻¹) * (c * a * c⁻¹) = 1) (hb' : (c * b * c⁻¹) * (c * b * c⁻¹) = 1)
    (hab' : (c * a * c⁻¹) * (c * b * c⁻¹) = (c * b * c⁻¹) * (c * a * c⁻¹)) :
    (klein a b ha hb hab).map (MulAut.conj c).toMonoidHom =
      klein (c * a * c⁻¹) (c * b * c⁻¹) ha' hb' hab' := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := mem_klein.mp hx
    show c * x * c⁻¹ ∈ klein (c * a * c⁻¹) (c * b * c⁻¹) ha' hb' hab'
    rw [mem_klein]
    rcases hx' with rfl | rfl | rfl | rfl
    · left; group
    · right; left; rfl
    · right; right; left; rfl
    · right; right; right; group
  · apply klein_le
    · exact ⟨a, (mem_klein.mpr (Or.inr (Or.inl rfl))), rfl⟩
    · exact ⟨b, (mem_klein.mpr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩

theorem klein_eq_mul {a b : S7} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hb' : (a * b) * (a * b) = 1) (hab' : a * (a * b) = (a * b) * a) :
    klein a b ha hb hab = klein a (a * b) ha hb' hab' := by
  apply klein_eq_klein
  · exact mem_klein.mpr (Or.inr (Or.inl rfl))
  · exact mem_klein.mpr (Or.inr (Or.inr (Or.inr rfl)))
  · exact mem_klein.mpr (Or.inr (Or.inl rfl))
  · refine mem_klein.mpr (Or.inr (Or.inr (Or.inr ?_)))
    rw [← mul_assoc, ha, one_mul]

@[expose] def Surv8 : List S7 :=
  [s * r, s * r ^ 3, s * swap 4 5, s * swap 4 6, s * swap 5 6, s * r ^ 2 * swap 4 5,
    s * r ^ 2 * swap 4 6, s * r ^ 2 * swap 5 6]

theorem mem_Surv8_iff {x : S7} : x ∈ Surv8 ↔
    x = s * r ∨ x = s * r ^ 3 ∨ x = s * swap 4 5 ∨ x = s * swap 4 6 ∨ x = s * swap 5 6 ∨
      x = s * r ^ 2 * swap 4 5 ∨ x = s * r ^ 2 * swap 4 6 ∨ x = s * r ^ 2 * swap 5 6 := by
  simp [Surv8]

theorem surv_of_C48 : ∀ x ∈ C48list, x * x = 1 → sign x = 1 → x ≠ 1 → x ≠ r ^ 2 → x ∈ Surv8 := by
  intro x hx
  obtain ⟨d, hd, e, he, rfl⟩ := mem_C48list_iff.mp hx
  rw [mem_D8list_iff] at hd
  rw [mem_S3list_iff] at he
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end Classify

section Classify2

theorem klein_conj_to {a b a' b' : S7} {ha : a * a = 1} {hb : b * b = 1} {hab : a * b = b * a}
    {ha' : a' * a' = 1} {hb' : b' * b' = 1} {hab' : a' * b' = b' * a'} (c : S7)
    (h1 : c * a * c⁻¹ ∈ klein a' b' ha' hb' hab') (h2 : c * b * c⁻¹ ∈ klein a' b' ha' hb' hab')
    (h3 : c⁻¹ * a' * c ∈ klein a b ha hb hab) (h4 : c⁻¹ * b' * c ∈ klein a b ha hb hab) :
    (klein a b ha hb hab).map (MulAut.conj c).toMonoidHom = klein a' b' ha' hb' hab' := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := mem_klein.mp hx
    show c * x * c⁻¹ ∈ klein a' b' ha' hb' hab'
    rcases hx' with rfl | rfl | rfl | rfl
    · have : c * 1 * c⁻¹ = 1 := by group
      rw [this]
      exact Subgroup.one_mem _
    · exact h1
    · exact h2
    · have : c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ h1 h2
  · apply klein_le
    · exact ⟨c⁻¹ * a' * c, h3, by show c * (c⁻¹ * a' * c) * c⁻¹ = a'; group⟩
    · exact ⟨c⁻¹ * b' * c, h4, by show c * (c⁻¹ * b' * c) * c⁻¹ = b'; group⟩

@[expose] def Vsub : Subgroup S7 :=
  klein (r ^ 2) (s * r) (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] def Wsub : Subgroup S7 :=
  klein (r ^ 2) (s * f0) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem klein_r2_classify (b' : S7) (hb2 : b' * b' = 1) (hcb : r ^ 2 * b' = b' * r ^ 2)
    (hmem : b' ∈ Surv8) :
    ∃ c : S7, (klein (r ^ 2) b' (by decide +kernel) hb2 hcb).map (MulAut.conj c).toMonoidHom = Vsub ∨
      (klein (r ^ 2) b' (by decide +kernel) hb2 hcb).map (MulAut.conj c).toMonoidHom = Wsub := by
  rw [mem_Surv8_iff] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, Or.inl (klein_conj_to 1
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel))⟩
  · exact ⟨1, Or.inl (klein_conj_to 1
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel))⟩
  · exact ⟨1, Or.inr (klein_conj_to 1
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel))⟩
  · exact ⟨swap 5 6, Or.inr (klein_conj_to (swap 5 6)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel))⟩
  · exact ⟨swap 4 6, Or.inr (klein_conj_to (swap 4 6)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel))⟩
  · exact ⟨1, Or.inr (klein_conj_to 1
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel))⟩
  · exact ⟨swap 5 6, Or.inr (klein_conj_to (swap 5 6)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel))⟩
  · exact ⟨swap 4 6, Or.inr (klein_conj_to (swap 4 6)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel)
      (by rw [mem_klein]; decide +kernel) (by rw [mem_klein]; decide +kernel))⟩

end Classify2

section Classify3

theorem exists_two_gens (U : Subgroup S7) (hcard : Nat.card U = 4) :
    ∃ a ∈ U, ∃ b ∈ U, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  by_contra hcon
  push Not at hcon
  have hne : U ≠ ⊥ := by
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨⟨a, haU⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hsub : (U : Set S7) ⊆ {1, a} := by
    intro x hx
    by_cases hx1 : x = 1
    · simp [hx1]
    · have := hcon x hx a haU hx1 ha1'
      simp [this]
  have h1 : (U : Set S7).ncard ≤ ({1, a} : Set S7).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, a} : Set S7).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : S7) ({a} : Set S7)
    rw [Set.ncard_singleton] at this
    exact this
  have h3 : (U : Set S7).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  omega

theorem classify_four (U : Subgroup S7) (hU : U ≤ alternatingGroup (Fin 7))
    (hsq : ∀ x ∈ U, x * x = 1) (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hcard : Nat.card U = 4) :
    ∃ c : S7, U.map (MulAut.conj c).toMonoidHom = Vsub ∨
      U.map (MulAut.conj c).toMonoidHom = Wsub := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, haU, b, hbU, ha1, hb1, hab⟩ := exists_two_gens U hcard
  have ha := hsq a haU
  have hb := hsq b hbU
  have hcab := hcomm a haU b hbU
  have hUeq : klein a b ha hb hcab = U :=
    Subgroup.eq_of_le_of_card_ge (klein_le U haU hbU)
      (by rw [hcard, card_klein ha hb hcab ha1 hb1 hab])
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha) ha1
  have hr2A : r ^ 2 ∈ alternatingGroup (Fin 7) :=
    Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)
  have hr2o : orderOf (r ^ 2) = 2 := orderOf_eq_prime (by decide +kernel) rsq_ne_one
  obtain ⟨c₁, -, hc₁⟩ := involutions_conj_alternating (hU haU) hr2A ha2 hr2o
  have hb'2 : (c₁ * b * c₁⁻¹) * (c₁ * b * c₁⁻¹) = 1 := by
    calc (c₁ * b * c₁⁻¹) * (c₁ * b * c₁⁻¹) = c₁ * (b * b) * c₁⁻¹ := by group
      _ = 1 := by rw [hb]; group
  have hcb' : r ^ 2 * (c₁ * b * c₁⁻¹) = (c₁ * b * c₁⁻¹) * r ^ 2 := by
    rw [← hc₁]
    calc c₁ * a * c₁⁻¹ * (c₁ * b * c₁⁻¹) = c₁ * (a * b) * c₁⁻¹ := by group
      _ = c₁ * (b * a) * c₁⁻¹ := by rw [hcab]
      _ = c₁ * b * c₁⁻¹ * (c₁ * a * c₁⁻¹) := by group
  have hbs : sign (c₁ * b * c₁⁻¹) = 1 := by
    have h1 := Equiv.Perm.mem_alternatingGroup.mp (hU hbU)
    have h2 : sign (c₁ * b * c₁⁻¹) = sign b := by simpa using sign_conj_eq c₁⁻¹ b
    rw [h2]
    exact h1
  have hb'1 : c₁ * b * c₁⁻¹ ≠ 1 := by
    intro h
    apply hb1
    calc b = c₁⁻¹ * (c₁ * b * c₁⁻¹) * c₁ := by group
      _ = 1 := by rw [h]; group
  have hb'r : c₁ * b * c₁⁻¹ ≠ r ^ 2 := by
    intro h
    apply hab
    rw [← hc₁] at h
    calc a = c₁⁻¹ * (c₁ * a * c₁⁻¹) * c₁ := by group
      _ = c₁⁻¹ * (c₁ * b * c₁⁻¹) * c₁ := h.symm ▸ rfl
      _ = b := by group
  have hC48 : c₁ * b * c₁⁻¹ ∈ C48list := mem_C48list_of_commute hcb'.symm
  have hmem := surv_of_C48 _ hC48 hb'2 hbs hb'1 hb'r
  obtain ⟨c₂, hc₂⟩ := klein_r2_classify _ hb'2 hcb' hmem
  have hmap : U.map (MulAut.conj c₁).toMonoidHom =
      klein (r ^ 2) (c₁ * b * c₁⁻¹) (by decide +kernel) hb'2 hcb' := by
    rw [← hUeq]
    apply klein_conj_to c₁
    · rw [hc₁]; exact mem_klein.mpr (Or.inr (Or.inl rfl))
    · exact mem_klein.mpr (Or.inr (Or.inr (Or.inl rfl)))
    · rw [← hc₁]
      have : c₁⁻¹ * (c₁ * a * c₁⁻¹) * c₁ = a := by group
      rw [this]
      exact mem_klein.mpr (Or.inr (Or.inl rfl))
    · have : c₁⁻¹ * (c₁ * b * c₁⁻¹) * c₁ = b := by group
      rw [this]
      exact mem_klein.mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hcomp : ∀ V : Subgroup S7, (V.map (MulAut.conj c₁).toMonoidHom).map (MulAut.conj c₂).toMonoidHom =
      V.map (MulAut.conj (c₂ * c₁)).toMonoidHom := by
    intro V
    rw [Subgroup.map_map]
    congr 1
  refine ⟨c₂ * c₁, ?_⟩
  rw [← hcomp, hmap]
  exact hc₂

end Classify3

section WType

@[expose] def cW : S7 := r ^ 2 * f0

theorem cW_sq : cW ^ 2 = 1 := by decide +kernel

theorem cW_cycleType : cW.cycleType = {2, 2, 2} := by
  rw [cycleType_replicate_two cW cW_sq]
  have : cW.support.card = 6 := by decide +kernel
  rw [this]
  rfl

@[expose] def TcW : List S7 := [swap 0 2, swap 1 3, swap 4 5]

theorem swap_comm_cW : ∀ a b : Fin 7, a ≠ b → swap a b * cW = cW * swap a b → swap a b ∈ TcW := by
  decide +kernel

theorem mem_Wsub_iff {x : S7} : x ∈ Wsub ↔
    x = 1 ∨ x = r ^ 2 ∨ x = s * f0 ∨ x = r ^ 2 * (s * f0) := mem_klein

theorem Wsub_comm_cW : ∀ w ∈ Wsub, w * cW = cW * w := by
  intro w hw
  rw [mem_Wsub_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> decide +kernel

theorem cW_mul_mem_Wsub : ∀ τ ∈ TcW, cW * τ ∈ Wsub := by
  intro τ hτ
  simp only [TcW, List.mem_cons, List.not_mem_nil, or_false] at hτ
  rw [mem_Wsub_iff]
  rcases hτ with rfl | rfl | rfl <;> decide +kernel

theorem Wsub_elt : ∀ w ∈ Wsub, w = 1 ∨ ∃ τ ∈ TcW, w = cW * τ := by
  intro w hw
  rw [mem_Wsub_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · left; rfl
  · right; exact ⟨swap 4 5, by simp [TcW], by decide +kernel⟩
  · right; exact ⟨swap 1 3, by simp [TcW], by decide +kernel⟩
  · right; exact ⟨swap 0 2, by simp [TcW], by decide +kernel⟩

theorem conj_TcW_mem (x : S7) (hx : Commute x cW) : ∀ τ ∈ TcW, x * τ * x⁻¹ ∈ TcW := by
  intro τ hτ
  have hsw : ∃ a b : Fin 7, a ≠ b ∧ τ = swap a b ∧ Commute τ cW := by
    simp only [TcW, List.mem_cons, List.not_mem_nil, or_false] at hτ
    rcases hτ with rfl | rfl | rfl
    · exact ⟨0, 2, by decide, rfl, by show _ = _; decide +kernel⟩
    · exact ⟨1, 3, by decide, rfl, by show _ = _; decide +kernel⟩
    · exact ⟨4, 5, by decide, rfl, by show _ = _; decide +kernel⟩
  obtain ⟨a, b, hab, rfl, hτc⟩ := hsw
  have h1 : x * swap a b * x⁻¹ = swap (x a) (x b) := (Equiv.swap_apply_apply x a b).symm
  have hc : Commute (x * swap a b * x⁻¹) cW := (hx.mul_left hτc).mul_left hx.inv_left
  rw [h1] at hc ⊢
  exact swap_comm_cW _ _ (fun h => hab (x.injective h)) hc.eq

theorem centralizer_cW_le : centralizer ({cW} : Set S7) ≤ normalizer (Wsub : Set S7) := by
  intro x hx
  have hxc : Commute x cW := Subgroup.mem_centralizer_singleton_iff.mp hx
  have key : ∀ y : S7, y * cW = cW * y → ∀ w ∈ Wsub, y * w * y⁻¹ ∈ Wsub := by
    intro y hy w hw
    rcases Wsub_elt w hw with rfl | ⟨τ, hτ, rfl⟩
    · have : y * 1 * y⁻¹ = 1 := by group
      rw [this]
      exact Subgroup.one_mem _
    · have h1 : y * (cW * τ) * y⁻¹ = cW * (y * τ * y⁻¹) := by
        calc y * (cW * τ) * y⁻¹ = (y * cW) * τ * y⁻¹ := by group
          _ = (cW * y) * τ * y⁻¹ := by rw [hy]
          _ = cW * (y * τ * y⁻¹) := by group
      rw [h1]
      exact cW_mul_mem_Wsub _ (conj_TcW_mem y (Commute.eq hy |> fun h => h) τ hτ)
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    exact key x hxc.eq w hw
  · intro hw
    have hxi : x⁻¹ * cW = cW * x⁻¹ := (hxc.inv_left).eq
    have := key x⁻¹ hxi _ hw
    have e : x⁻¹ * (x * w * x⁻¹) * x⁻¹⁻¹ = w := by group
    rw [e] at this
    exact this

end WType

section WType2

theorem cW_unique : ∀ y ∈ C48list, y * (s * f0) = (s * f0) * y → y.support.card = 6 → y = cW := by
  intro y hy
  obtain ⟨d, hd, e, he, rfl⟩ := mem_C48list_iff.mp hy
  rw [mem_D8list_iff] at hd
  rw [mem_S3list_iff] at he
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem normalizer_le_centralizer_cW :
    normalizer (Wsub : Set S7) ≤ centralizer ({cW} : Set S7) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hnorm : ∀ w ∈ Wsub, x⁻¹ * w * x ∈ Wsub := by
    intro w hw
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) w).mp hw
    simpa using this
  have hr2 : x⁻¹ * r ^ 2 * x ∈ Wsub := hnorm _ (mem_Wsub_iff.mpr (Or.inr (Or.inl rfl)))
  have hsf : x⁻¹ * (s * f0) * x ∈ Wsub :=
    hnorm _ (mem_Wsub_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have hc1 := Wsub_comm_cW _ hr2
  have hc2 := Wsub_comm_cW _ hsf
  have h1 : (x * cW * x⁻¹) * r ^ 2 = r ^ 2 * (x * cW * x⁻¹) := by
    calc x * cW * x⁻¹ * r ^ 2 = x * (cW * (x⁻¹ * r ^ 2 * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * r ^ 2 * x) * cW) * x⁻¹ := by rw [← hc1]
      _ = r ^ 2 * (x * cW * x⁻¹) := by group
  have h2 : (x * cW * x⁻¹) * (s * f0) = (s * f0) * (x * cW * x⁻¹) := by
    calc x * cW * x⁻¹ * (s * f0) = x * (cW * (x⁻¹ * (s * f0) * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * (s * f0) * x) * cW) * x⁻¹ := by rw [← hc2]
      _ = (s * f0) * (x * cW * x⁻¹) := by group
  have h3 : x * cW * x⁻¹ ∈ C48list := mem_C48list_of_commute h1
  have h4 : (x * cW * x⁻¹).support.card = 6 := by
    rw [← Equiv.Perm.sum_cycleType, Equiv.Perm.cycleType_conj, cW_cycleType]
    rfl
  have h5 : x * cW * x⁻¹ = cW := cW_unique _ h3 h2 h4
  calc x * cW = (x * cW * x⁻¹) * x := by group
    _ = cW * x := by rw [h5]

theorem normalizer_Wsub_eq : normalizer (Wsub : Set S7) = centralizer ({cW} : Set S7) :=
  le_antisymm normalizer_le_centralizer_cW centralizer_cW_le

theorem N_Wsub_equiv :
    Nonempty (↥(normalizer (Wsub : Set S7) ⊓ alternatingGroup (Fin 7)) ≃* Perm (Fin 4)) := by
  obtain ⟨e⟩ := centralizer_A7_two_two_two_equiv cW_cycleType
  rw [normalizer_Wsub_eq]
  exact ⟨e⟩

end WType2

section VType

@[expose] def ι4 : Fin 4 ↪ Fin 7 := Fin.castLEEmb (by norm_num)

@[expose] noncomputable def emb4 : Perm (Fin 4) →* S7 := Equiv.Perm.viaEmbeddingHom ι4

theorem emb4_injective : Function.Injective emb4 := Equiv.Perm.viaEmbeddingHom_injective ι4

theorem emb4_apply_of_ge (σ : Perm (Fin 4)) (x : Fin 7) (hx : 4 ≤ x.val) : emb4 σ x = x := by
  classical
  exact Equiv.Perm.viaEmbedding_apply_of_notMem σ _ x (by
    rintro ⟨y, rfl⟩
    have h1 := y.isLt
    have h2 : (ι4 y).val = y.val := rfl
    omega)

theorem emb4_apply (σ : Perm (Fin 4)) (x : Fin 4) : emb4 σ (ι4 x) = ι4 (σ x) := by
  classical
  exact Equiv.Perm.viaEmbedding_apply σ _ x

theorem sign_emb4 (σ : Perm (Fin 4)) : sign (emb4 σ) = sign σ := by
  let _ : DecidablePred (fun x => x ∈ Set.range ι4) := fun x => Classical.propDecidable _
  exact sign_extendDomain σ (Equiv.ofInjective ι4 ι4.injective)

theorem emb4_swap (i j : Fin 4) : emb4 (swap i j) = swap (ι4 i) (ι4 j) := by
  apply Equiv.ext
  intro x
  by_cases hx : x.val < 4
  · obtain ⟨y, rfl⟩ : ∃ y : Fin 4, ι4 y = x := ⟨⟨x.val, hx⟩, rfl⟩
    rw [emb4_apply]
    by_cases h1 : y = i
    · subst h1; simp
    · by_cases h2 : y = j
      · subst h2; simp
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
          Equiv.swap_apply_of_ne_of_ne (fun h => h1 (ι4.injective h))
            (fun h => h2 (ι4.injective h))]
  · have hx' : 4 ≤ x.val := by omega
    rw [emb4_apply_of_ge _ _ hx']
    symm
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have h1 : (ι4 i).val = x.val := congrArg Fin.val h.symm
      have h2 : (ι4 i).val = i.val := rfl
      have := i.isLt
      omega
    · intro h
      have h1 : (ι4 j).val = x.val := congrArg Fin.val h.symm
      have h2 : (ι4 j).val = j.val := rfl
      have := j.isLt
      omega

@[expose] noncomputable def AA : Subgroup S7 := (alternatingGroup (Fin 4)).map emb4

@[expose] def XX : Subgroup S7 := Subgroup.zpowers (swap 4 5 * swap 5 6)

@[expose] def tt : S7 := swap 0 1 * swap 4 5

theorem mem_AA_iff {x : S7} : x ∈ AA ↔ ∃ σ ∈ alternatingGroup (Fin 4), emb4 σ = x :=
  Iff.rfl

theorem AA_fix : ∀ a ∈ AA, ∀ i : Fin 7, 4 ≤ i.val → a i = i := by
  rintro _ ⟨σ, -, rfl⟩ i hi
  exact emb4_apply_of_ge σ i hi

theorem XX_fix : ∀ x ∈ XX, ∀ i : Fin 7, i.val < 4 → x i = i := by
  let L : Subgroup S7 :=
    { carrier := {y | ∀ i : Fin 7, i.val < 4 → y i = i}
      one_mem' := fun i _ => rfl
      mul_mem' := fun {a b} ha hb i hi => by
        rw [Equiv.Perm.mul_apply, hb i hi, ha i hi]
      inv_mem' := fun {a} ha i hi => by
        have := ha i hi
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact this.symm }
  have hle : XX ≤ L := by
    rw [XX, Subgroup.zpowers_le]
    exact c3_fix
  exact fun x hx => hle hx

theorem AA_inf_XX : AA ⊓ XX = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hA, hX⟩
  apply Equiv.ext
  intro i
  by_cases hi : i.val < 4
  · exact XX_fix y hX i hi
  · exact AA_fix y hA i (by omega)

theorem AA_comm_XX : ∀ a ∈ AA, ∀ x ∈ XX, a * x = x * a := by
  intro a ha x hx
  apply Equiv.Perm.Disjoint.commute
  intro i
  by_cases hi : i.val < 4
  · right; exact XX_fix x hx i hi
  · left; exact AA_fix a ha i (by omega)

end VType

section VType2

open scoped Pointwise

theorem card_sup_of_le_normalizer' {G : Type*} [Group G] (S Z : Subgroup G)
    (hZ : Z ≤ normalizer (S : Set G)) (hd : Disjoint S Z) :
    Nat.card ↥(S ⊔ Z) = Nat.card ↥S * Nat.card ↥Z := by
  have hcoe : ((S ⊔ Z : Subgroup G) : Set G) = (S : Set G) * (Z : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S Z hZ
  have hc : (S.subgroupOf (S ⊔ Z)).IsComplement' (Z.subgroupOf (S ⊔ Z)) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hx hx'
      exact Subtype.ext (Subgroup.disjoint_def.mp hd hx hx')
    · apply Set.eq_univ_of_forall
      intro x
      have hx : (x : G) ∈ ((S ⊔ Z : Subgroup G) : Set G) := x.2
      rw [hcoe] at hx
      obtain ⟨s, hs, z, hz, hsz⟩ := hx
      exact ⟨⟨s, Subgroup.mem_sup_left hs⟩, hs, ⟨z, Subgroup.mem_sup_right hz⟩, hz, Subtype.ext hsz⟩
  have h := hc.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at h
  exact h.symm

theorem mem_sup_of_commute' {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
          refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
          have := hc h₂ hh₂ k₁ hk₁
          calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
            _ = h₁ * (h₂ * k₁) * k₂ := by rw [this]
            _ = h₁ * h₂ * (k₁ * k₂) := by group
        inv_mem' := by
          rintro _ ⟨h, hh, k, hk, rfl⟩
          refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
          exact Commute.mul_inv (hc h hh k hk) }
    have hle : H ⊔ K ≤ S :=
      sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
        (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
    exact hle hx
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)

theorem emb4_comm_f0 (σ : Perm (Fin 4)) : emb4 σ * f0 = f0 * emb4 σ := by
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases hx : 4 ≤ x.val
  · left; exact emb4_apply_of_ge σ x hx
  · right
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; rw [h] at hx; simp at hx
    · intro h; rw [h] at hx; simp at hx

theorem tt_eq : tt = emb4 (swap 0 1) * f0 := by
  rw [emb4_swap]
  rfl

theorem tt_sq : tt * tt = 1 := by decide +kernel

theorem tt_inv : tt⁻¹ = tt := inv_eq_of_mul_eq_one_right tt_sq

theorem tt_even : sign tt = 1 := by decide +kernel

theorem Vsub_le_AA : Vsub ≤ AA := by
  apply klein_le
  · refine ⟨swap 0 2 * swap 1 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    rw [map_mul, emb4_swap, emb4_swap]
    decide +kernel
  · refine ⟨swap 0 1 * swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel), ?_⟩
    rw [map_mul, emb4_swap, emb4_swap]
    decide +kernel

theorem tt_conj_AA : ∀ a ∈ AA, tt * a * tt⁻¹ ∈ AA := by
  rintro _ ⟨σ, hσ, rfl⟩
  refine ⟨swap 0 1 * σ * (swap 0 1)⁻¹, ?_, ?_⟩
  · refine Equiv.Perm.mem_alternatingGroup.mpr ?_
    have h1 := Equiv.Perm.mem_alternatingGroup.mp hσ
    have h2 : sign (swap 0 1 * σ * (swap 0 1)⁻¹) = sign σ := by
      simp [sign_mul, mul_comm]
    rw [h2]
    exact h1
  · have hcomm := emb4_comm_f0 σ
    have h3 : f0 * emb4 σ * f0⁻¹ = emb4 σ := by
      rw [← hcomm]
      group
    calc emb4 (swap 0 1 * σ * (swap 0 1)⁻¹)
        = emb4 (swap 0 1) * emb4 σ * (emb4 (swap 0 1))⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = emb4 (swap 0 1) * (f0 * emb4 σ * f0⁻¹) * (emb4 (swap 0 1))⁻¹ := by rw [h3]
      _ = tt * emb4 σ * tt⁻¹ := by rw [tt_eq]; group

end VType2

section VType3

theorem tt_conj_c3 : tt * (swap 4 5 * swap 5 6) * tt⁻¹ = (swap 4 5 * swap 5 6)⁻¹ := by
  decide +kernel

theorem tt_conj_XX : ∀ x ∈ XX, tt * x * tt⁻¹ ∈ XX := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : tt * (swap 4 5 * swap 5 6) ^ k * tt⁻¹ = (tt * (swap 4 5 * swap 5 6) * tt⁻¹) ^ k := by
    simp
  rw [h1, tt_conj_c3]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) k

theorem tt_mem_normalizer_AA : tt ∈ normalizer (AA : Set S7) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact tt_conj_AA h
  · intro hh
    have := tt_conj_AA _ hh
    have e : tt * (tt * h * tt⁻¹) * tt⁻¹ = h := by
      rw [tt_inv]
      calc tt * (tt * h * tt) * tt = (tt * tt) * h * (tt * tt) := by group
        _ = h := by rw [tt_sq]; group
    rw [e] at this
    exact this

theorem tt_mem_normalizer_XX : tt ∈ normalizer (XX : Set S7) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact tt_conj_XX h
  · intro hh
    have := tt_conj_XX _ hh
    have e : tt * (tt * h * tt⁻¹) * tt⁻¹ = h := by
      rw [tt_inv]
      calc tt * (tt * h * tt) * tt = (tt * tt) * h * (tt * tt) := by group
        _ = h := by rw [tt_sq]; group
    rw [e] at this
    exact this

theorem tt_not_mem_AA : tt ∉ AA := by
  intro h
  have := AA_fix tt h 4 (by decide)
  exact absurd this (by decide +kernel)

theorem AA_inf_zpowers_tt : Disjoint AA (Subgroup.zpowers tt) := by
  rw [Subgroup.disjoint_def]
  intro y hyA hyt
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyt
  have hk : (tt ^ k = 1) ∨ (tt ^ k = tt) := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul]
      have : tt ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact tt_sq
      rw [this, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul]
      have : tt ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact tt_sq
      rw [this, one_zpow, one_mul]
  rcases hk with h | h
  · exact h
  · exact absurd (h ▸ hyA) tt_not_mem_AA

theorem card_AA : Nat.card AA = 12 := by
  have h1 : Nat.card AA = Nat.card (alternatingGroup (Fin 4)) :=
    (Nat.card_congr (Subgroup.equivMapOfInjective _ emb4 emb4_injective).toEquiv).symm
  rw [h1, nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card]
  decide

theorem card_zpowers_tt : Nat.card (Subgroup.zpowers tt) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact tt_sq) (by decide +kernel)

theorem card_AA_sup_tt : Nat.card ↥(AA ⊔ Subgroup.zpowers tt) = 24 := by
  rw [card_sup_of_le_normalizer' AA (Subgroup.zpowers tt)
    (Subgroup.zpowers_le.mpr tt_mem_normalizer_AA) AA_inf_zpowers_tt, card_AA, card_zpowers_tt]

end VType3

section VType4

theorem f0_mul_self : f0 * f0 = 1 := by rw [← pow_two]; exact f0_sq

@[expose] noncomputable def w4 (σ : Perm (Fin 4)) : S7 := if sign σ = 1 then 1 else f0

theorem w4_mul (σ τ : Perm (Fin 4)) : w4 (σ * τ) = w4 σ * w4 τ := by
  unfold w4
  rw [sign_mul]
  rcases Int.units_eq_one_or (sign σ) with h1 | h1 <;>
    rcases Int.units_eq_one_or (sign τ) with h2 | h2 <;>
    simp [h1, h2, f0_mul_self]

theorem sign_w4 (σ : Perm (Fin 4)) : sign (w4 σ) = sign σ := by
  unfold w4
  rcases Int.units_eq_one_or (sign σ) with h1 | h1
  · simp [h1]
  · simp [h1, f0_isSwap.sign_eq]

theorem w4_apply_of_lt (σ : Perm (Fin 4)) (x : Fin 7) (hx : x.val < 4) : w4 σ x = x := by
  unfold w4
  split_ifs
  · rfl
  · apply Equiv.swap_apply_of_ne_of_ne
    · intro h; rw [h] at hx; simp at hx
    · intro h; rw [h] at hx; simp at hx

theorem emb4_comm_w4 (σ τ : Perm (Fin 4)) : emb4 σ * w4 τ = w4 τ * emb4 σ := by
  unfold w4
  split_ifs
  · simp
  · exact emb4_comm_f0 σ

@[expose] noncomputable def Phi4 : Perm (Fin 4) →* S7 where
  toFun σ := emb4 σ * w4 σ
  map_one' := by simp [w4]
  map_mul' σ τ := by
    simp only [map_mul, w4_mul]
    calc emb4 σ * emb4 τ * (w4 σ * w4 τ) = emb4 σ * (emb4 τ * w4 σ) * w4 τ := by group
      _ = emb4 σ * (w4 σ * emb4 τ) * w4 τ := by rw [emb4_comm_w4 τ σ]
      _ = emb4 σ * w4 σ * (emb4 τ * w4 τ) := by group

theorem Phi4_injective : Function.Injective Phi4 := by
  intro σ τ h
  apply Equiv.ext
  intro x
  have hx : (ι4 x).val < 4 := by simp [ι4]
  have h1 := congrArg (fun f : S7 => f (ι4 x)) h
  simp only [Phi4, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.mul_apply] at h1
  rw [w4_apply_of_lt σ _ hx, w4_apply_of_lt τ _ hx, emb4_apply, emb4_apply] at h1
  exact ι4.injective h1

theorem Phi4_mem (σ : Perm (Fin 4)) : Phi4 σ ∈ AA ⊔ Subgroup.zpowers tt := by
  show emb4 σ * w4 σ ∈ _
  unfold w4
  by_cases hs : sign σ = 1
  · simp only [hs, ↓reduceIte, mul_one]
    exact Subgroup.mem_sup_left ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hs, rfl⟩
  · have hs' : sign σ = -1 := by
      rcases Int.units_eq_one_or (sign σ) with h | h
      · exact absurd h hs
      · exact h
    have hne : (-1 : ℤˣ) ≠ 1 := by decide
    have hif : (if sign σ = 1 then (1 : S7) else f0) = f0 := by simp [hs']
    rw [hif]
    have h1 : emb4 σ * f0 = emb4 (σ * swap 0 1) * tt := by
      rw [tt_eq, map_mul]
      calc emb4 σ * f0 = emb4 σ * (emb4 (swap 0 1) * emb4 (swap 0 1)) * f0 := by
            rw [← map_mul, Equiv.swap_mul_self, map_one, mul_one]
        _ = emb4 σ * emb4 (swap 0 1) * (emb4 (swap 0 1) * f0) := by group
    rw [h1]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨σ * swap 0 1, ?_, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers tt))
    refine Equiv.Perm.mem_alternatingGroup.mpr ?_
    rw [sign_mul, hs', sign_swap (by decide)]
    rfl

theorem AAt_equiv : Nonempty (↥(AA ⊔ Subgroup.zpowers tt) ≃* Perm (Fin 4)) := by
  have : Nonempty (Perm (Fin 4) ≃* ↥(AA ⊔ Subgroup.zpowers tt)) := by
    refine nonempty_mulEquiv_of_injective_of_card Phi4 Phi4_injective _ ?_ ?_
    · rintro _ ⟨σ, rfl⟩
      exact Phi4_mem σ
    · rw [card_AA_sup_tt]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
  obtain ⟨e⟩ := this
  exact ⟨e.symm⟩

end VType4

section VType5

theorem ι3_val (x : Fin 3) : (ι3 x).val = x.val + 4 := rfl

theorem emb3_apply (σ : Perm (Fin 3)) (x : Fin 3) : emb3 σ (ι3 x) = ι3 (σ x) := by
  classical
  exact Equiv.Perm.viaEmbedding_apply σ _ x

theorem emb3_apply_of_ge' (σ : Perm (Fin 3)) (x : Fin 7) (hx : x.val < 4) : emb3 σ x = x :=
  emb3_apply_of_lt σ x hx

theorem sign_emb3 (σ : Perm (Fin 3)) : sign (emb3 σ) = sign σ := by
  let _ : DecidablePred (fun x => x ∈ Set.range ι3) := fun x => Classical.propDecidable _
  exact sign_extendDomain σ (Equiv.ofInjective ι3 ι3.injective)

theorem emb3_swap (i j : Fin 3) : emb3 (swap i j) = swap (ι3 i) (ι3 j) := by
  apply Equiv.ext
  intro x
  by_cases hx : 4 ≤ x.val
  · obtain ⟨y, rfl⟩ : ∃ y : Fin 3, ι3 y = x := ⟨⟨x.val - 4, by omega⟩, by apply Fin.ext; simp [ι3_val]; omega⟩
    rw [emb3_apply]
    by_cases h1 : y = i
    · subst h1; simp
    · by_cases h2 : y = j
      · subst h2; simp
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2,
          Equiv.swap_apply_of_ne_of_ne (fun h => h1 (ι3.injective h))
            (fun h => h2 (ι3.injective h))]
  · have hx' : x.val < 4 := by omega
    rw [emb3_apply_of_lt _ x hx']
    symm
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have h1 : (ι3 i).val = x.val := congrArg Fin.val h.symm
      rw [ι3_val] at h1
      omega
    · intro h
      have h1 : (ι3 j).val = x.val := congrArg Fin.val h.symm
      rw [ι3_val] at h1
      omega

@[expose] noncomputable def w3 (σ : Perm (Fin 3)) : S7 := if sign σ = 1 then 1 else swap 0 1

theorem w3_mul (σ τ : Perm (Fin 3)) : w3 (σ * τ) = w3 σ * w3 τ := by
  unfold w3
  rw [sign_mul]
  rcases Int.units_eq_one_or (sign σ) with h1 | h1 <;>
    rcases Int.units_eq_one_or (sign τ) with h2 | h2 <;>
    simp [h1, h2, Equiv.swap_mul_self]

theorem w3_apply_of_ge (σ : Perm (Fin 3)) (x : Fin 7) (hx : 2 ≤ x.val) : w3 σ x = x := by
  unfold w3
  split_ifs
  · rfl
  · apply Equiv.swap_apply_of_ne_of_ne
    · intro h; rw [h] at hx; simp at hx
    · intro h; rw [h] at hx; simp at hx

theorem emb3_comm_w3 (σ τ : Perm (Fin 3)) : emb3 σ * w3 τ = w3 τ * emb3 σ := by
  unfold w3
  split_ifs
  · simp
  · apply Equiv.Perm.Disjoint.commute
    intro x
    by_cases hx : x.val < 4
    · left; exact emb3_apply_of_lt σ x hx
    · right
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h; rw [h] at hx; simp at hx
      · intro h; rw [h] at hx; simp at hx

@[expose] noncomputable def Phi3 : Perm (Fin 3) →* S7 where
  toFun σ := emb3 σ * w3 σ
  map_one' := by simp [w3]
  map_mul' σ τ := by
    simp only [map_mul, w3_mul]
    calc emb3 σ * emb3 τ * (w3 σ * w3 τ) = emb3 σ * (emb3 τ * w3 σ) * w3 τ := by group
      _ = emb3 σ * (w3 σ * emb3 τ) * w3 τ := by rw [emb3_comm_w3 τ σ]
      _ = emb3 σ * w3 σ * (emb3 τ * w3 τ) := by group

theorem Phi3_injective : Function.Injective Phi3 := by
  intro σ τ h
  apply Equiv.ext
  intro x
  have hx : 2 ≤ (ι3 x).val := by rw [ι3_val]; omega
  have h1 := congrArg (fun f : S7 => f (ι3 x)) h
  simp only [Phi3, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.Perm.mul_apply] at h1
  rw [w3_apply_of_ge σ _ hx, w3_apply_of_ge τ _ hx, emb3_apply, emb3_apply] at h1
  exact ι3.injective h1

theorem Phi3_swap_mem : ∀ x y : Fin 3, x ≠ y → Phi3 (swap x y) ∈ XX ⊔ Subgroup.zpowers tt := by
  intro x y hxy
  have hsw : Phi3 (swap x y) = swap (ι3 x) (ι3 y) * swap 0 1 := by
    show emb3 (swap x y) * w3 (swap x y) = _
    rw [emb3_swap]
    unfold w3
    rw [sign_swap hxy]
    have : (-1 : ℤˣ) ≠ 1 := by decide
    simp [this]
  rw [hsw]
  have hX : ∀ a : ℕ, (swap 4 5 * swap 5 6 : S7) ^ a * tt ∈ XX ⊔ Subgroup.zpowers tt := fun a =>
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) a))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers tt))
  fin_cases x <;> fin_cases y
  · exact absurd rfl hxy
  · have key : swap (ι3 0) (ι3 1) * swap 0 1 ∈ XX ⊔ Subgroup.zpowers tt := by
      have : swap (ι3 0) (ι3 1) * swap 0 1 = (swap 4 5 * swap 5 6 : S7) ^ 0 * tt := by
        decide +kernel
      rw [this]; exact hX 0
    exact key
  · have key : swap (ι3 0) (ι3 2) * swap 0 1 ∈ XX ⊔ Subgroup.zpowers tt := by
      have : swap (ι3 0) (ι3 2) * swap 0 1 = (swap 4 5 * swap 5 6 : S7) ^ 1 * tt := by
        decide +kernel
      rw [this]; exact hX 1
    exact key
  · have key : swap (ι3 1) (ι3 0) * swap 0 1 ∈ XX ⊔ Subgroup.zpowers tt := by
      have : swap (ι3 1) (ι3 0) * swap 0 1 = (swap 4 5 * swap 5 6 : S7) ^ 0 * tt := by
        decide +kernel
      rw [this]; exact hX 0
    exact key
  · exact absurd rfl hxy
  · have key : swap (ι3 1) (ι3 2) * swap 0 1 ∈ XX ⊔ Subgroup.zpowers tt := by
      have : swap (ι3 1) (ι3 2) * swap 0 1 = (swap 4 5 * swap 5 6 : S7) ^ 2 * tt := by
        decide +kernel
      rw [this]; exact hX 2
    exact key
  · have key : swap (ι3 2) (ι3 0) * swap 0 1 ∈ XX ⊔ Subgroup.zpowers tt := by
      have : swap (ι3 2) (ι3 0) * swap 0 1 = (swap 4 5 * swap 5 6 : S7) ^ 1 * tt := by
        decide +kernel
      rw [this]; exact hX 1
    exact key
  · have key : swap (ι3 2) (ι3 1) * swap 0 1 ∈ XX ⊔ Subgroup.zpowers tt := by
      have : swap (ι3 2) (ι3 1) * swap 0 1 = (swap 4 5 * swap 5 6 : S7) ^ 2 * tt := by
        decide +kernel
      rw [this]; exact hX 2
    exact key
  · exact absurd rfl hxy

theorem Phi3_mem (σ : Perm (Fin 3)) : Phi3 σ ∈ XX ⊔ Subgroup.zpowers tt := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · rw [map_one]; exact Subgroup.one_mem _
  · intro f x y hxy ih
    rw [map_mul]
    exact Subgroup.mul_mem _ (Phi3_swap_mem x y hxy) ih

theorem XX_inf_zpowers_tt : Disjoint XX (Subgroup.zpowers tt) := by
  rw [Subgroup.disjoint_def]
  intro y hyX hyt
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyt
  have hk : (tt ^ k = 1) ∨ (tt ^ k = tt) := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul]
      have : tt ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact tt_sq
      rw [this, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul]
      have : tt ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact tt_sq
      rw [this, one_zpow, one_mul]
  rcases hk with h | h
  · exact h
  · have := XX_fix tt (h ▸ hyX) 0 (by decide)
    exact absurd this (by decide +kernel)

theorem card_XX : Nat.card XX = 3 := by
  rw [XX, Nat.card_zpowers]
  exact c3_order

theorem card_XX_sup_tt : Nat.card ↥(XX ⊔ Subgroup.zpowers tt) = 6 := by
  rw [card_sup_of_le_normalizer' XX (Subgroup.zpowers tt)
    (Subgroup.zpowers_le.mpr tt_mem_normalizer_XX) XX_inf_zpowers_tt, card_XX, card_zpowers_tt]

theorem XXt_equiv : Nonempty (↥(XX ⊔ Subgroup.zpowers tt) ≃* Perm (Fin 3)) := by
  have : Nonempty (Perm (Fin 3) ≃* ↥(XX ⊔ Subgroup.zpowers tt)) := by
    refine nonempty_mulEquiv_of_injective_of_card Phi3 Phi3_injective _ ?_ ?_
    · rintro _ ⟨σ, rfl⟩
      exact Phi3_mem σ
    · rw [card_XX_sup_tt]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
  obtain ⟨e⟩ := this
  exact ⟨e.symm⟩

end VType5

section VType6

open scoped Pointwise

theorem mem_Vsub_iff {x : S7} : x ∈ Vsub ↔
    x = 1 ∨ x = r ^ 2 ∨ x = s * r ∨ x = r ^ 2 * (s * r) := mem_klein

theorem Vsub_fix : ∀ v ∈ Vsub, ∀ i : Fin 7, 4 ≤ i.val → v i = i := by
  intro v hv
  rw [mem_Vsub_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide +kernel

@[expose] def V3list : List (Perm (Fin 4)) :=
  [swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2]

theorem V3_conj : ∀ σ : Perm (Fin 4), ∀ π ∈ V3list, σ * π * σ⁻¹ ∈ V3list := by
  unfold V3list
  decide +kernel

theorem emb4_V3 : ∀ π ∈ V3list, emb4 π ∈ Vsub := by
  intro π hπ
  simp only [V3list, List.mem_cons, List.not_mem_nil, or_false] at hπ
  rcases hπ with rfl | rfl | rfl
  · rw [map_mul, emb4_swap, emb4_swap, mem_Vsub_iff]
    right; left; decide +kernel
  · rw [map_mul, emb4_swap, emb4_swap, mem_Vsub_iff]
    right; right; left; decide +kernel
  · rw [map_mul, emb4_swap, emb4_swap, mem_Vsub_iff]
    right; right; right; decide +kernel

theorem Vsub_elt : ∀ v ∈ Vsub, v = 1 ∨ ∃ π ∈ V3list, emb4 π = v := by
  intro v hv
  rw [mem_Vsub_iff] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · left; rfl
  · right
    refine ⟨swap 0 2 * swap 1 3, by simp [V3list], ?_⟩
    rw [map_mul, emb4_swap, emb4_swap]; decide +kernel
  · right
    refine ⟨swap 0 1 * swap 2 3, by simp [V3list], ?_⟩
    rw [map_mul, emb4_swap, emb4_swap]; decide +kernel
  · right
    refine ⟨swap 0 3 * swap 1 2, by simp [V3list], ?_⟩
    rw [map_mul, emb4_swap, emb4_swap]; decide +kernel

theorem emb4_conj_Vsub (σ : Perm (Fin 4)) : ∀ v ∈ Vsub, emb4 σ * v * (emb4 σ)⁻¹ ∈ Vsub := by
  intro v hv
  rcases Vsub_elt v hv with rfl | ⟨π, hπ, rfl⟩
  · have : emb4 σ * 1 * (emb4 σ)⁻¹ = 1 := by group
    rw [this]; exact Subgroup.one_mem _
  · have h1 : emb4 σ * emb4 π * (emb4 σ)⁻¹ = emb4 (σ * π * σ⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [h1]
    exact emb4_V3 _ (V3_conj σ π hπ)

theorem emb4_mem_normalizer (σ : Perm (Fin 4)) : emb4 σ ∈ normalizer (Vsub : Set S7) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact fun hh => emb4_conj_Vsub σ h hh
  · intro hh
    have := emb4_conj_Vsub σ⁻¹ _ hh
    rw [map_inv] at this
    have e : (emb4 σ)⁻¹ * (emb4 σ * h * (emb4 σ)⁻¹) * (emb4 σ)⁻¹⁻¹ = h := by group
    rw [e] at this
    exact this

theorem commute_mem_normalizer_Vsub (x : S7) (hx : ∀ v ∈ Vsub, v * x = x * v) :
    x ∈ normalizer (Vsub : Set S7) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have e : ∀ v : S7, v * x = x * v → x * v * x⁻¹ = v := fun v hv => by
    calc x * v * x⁻¹ = (v * x) * x⁻¹ := by rw [hv]
      _ = v := by group
  constructor
  · intro hh
    rw [e h (hx h hh)]
    exact hh
  · intro hh
    have h1 := hx _ hh
    have : h = x * h * x⁻¹ := by
      calc h = x⁻¹ * ((x * h * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [h1]
        _ = x * h * x⁻¹ := by group
    rw [this]
    exact hh

end VType6

section VType7

open scoped Pointwise

theorem commute_mem_normalizer (V : Subgroup S7) (x : S7) (hx : ∀ v ∈ V, v * x = x * v) :
    x ∈ normalizer (V : Set S7) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have e : ∀ v : S7, v * x = x * v → x * v * x⁻¹ = v := fun v hv => by
    calc x * v * x⁻¹ = (v * x) * x⁻¹ := by rw [hv]
      _ = v := by group
  constructor
  · intro hh
    rw [e h (hx h hh)]
    exact hh
  · intro hh
    have h1 := hx _ hh
    have : h = x * h * x⁻¹ := by
      calc h = x⁻¹ * ((x * h * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [h1]
        _ = x * h * x⁻¹ := by group
    rw [this]
    exact hh

theorem Vsub_comm_f0 : ∀ v ∈ Vsub, v * f0 = f0 * v := by
  intro v hv
  apply Equiv.Perm.Disjoint.commute
  intro i
  by_cases hi : 4 ≤ i.val
  · left; exact Vsub_fix v hv i hi
  · right
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; rw [h] at hi; simp at hi
    · intro h; rw [h] at hi; simp at hi

theorem f0_mem_normalizer_Vsub : f0 ∈ normalizer (Vsub : Set S7) :=
  commute_mem_normalizer Vsub f0 Vsub_comm_f0

theorem XX_comm_Vsub : ∀ x ∈ XX, ∀ v ∈ Vsub, v * x = x * v := by
  intro x hx v hv
  apply Equiv.Perm.Disjoint.commute
  intro i
  by_cases hi : 4 ≤ i.val
  · left; exact Vsub_fix v hv i hi
  · right; exact XX_fix x hx i (by omega)

theorem XX_le_normalizer_Vsub : XX ≤ normalizer (Vsub : Set S7) := fun x hx =>
  commute_mem_normalizer Vsub x (fun v hv => XX_comm_Vsub x hx v hv)

theorem AA_le_normalizer_Vsub : AA ≤ normalizer (Vsub : Set S7) := by
  rintro _ ⟨σ, -, rfl⟩
  exact emb4_mem_normalizer σ

theorem tt_mem_normalizer_Vsub : tt ∈ normalizer (Vsub : Set S7) := by
  rw [tt_eq]
  exact Subgroup.mul_mem _ (emb4_mem_normalizer _) f0_mem_normalizer_Vsub

theorem AA_le_A7 : AA ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.mpr
    (by rw [sign_emb4]; exact Equiv.Perm.mem_alternatingGroup.mp hσ)

theorem XX_le_A7 : XX ≤ alternatingGroup (Fin 7) := by
  rw [XX, Subgroup.zpowers_le]
  exact Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)

theorem tt_mem_A7 : tt ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.mpr tt_even

theorem gen_le_N : (AA ⊔ XX) ⊔ Subgroup.zpowers tt ≤
    normalizer (Vsub : Set S7) ⊓ alternatingGroup (Fin 7) := by
  refine le_inf ?_ ?_
  · exact sup_le (sup_le AA_le_normalizer_Vsub XX_le_normalizer_Vsub)
      (Subgroup.zpowers_le.mpr tt_mem_normalizer_Vsub)
  · exact sup_le (sup_le AA_le_A7 XX_le_A7) (Subgroup.zpowers_le.mpr tt_mem_A7)

theorem XX_le_normalizer_AA : XX ≤ normalizer (AA : Set S7) := fun x hx =>
  commute_mem_normalizer AA x (fun a ha => AA_comm_XX a ha x hx)

theorem disjoint_zpowers_tt (K : Subgroup S7) (hK : tt ∉ K) : Disjoint K (Subgroup.zpowers tt) := by
  rw [Subgroup.disjoint_def]
  intro y hyK hyt
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyt
  have hk : (tt ^ k = 1) ∨ (tt ^ k = tt) := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul]
      have : tt ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact tt_sq
      rw [this, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul]
      have : tt ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, pow_two]; exact tt_sq
      rw [this, one_zpow, one_mul]
  rcases hk with h | h
  · exact h
  · exact absurd (h ▸ hyK) hK

theorem card_AA_sup_XX : Nat.card ↥(AA ⊔ XX) = 36 := by
  rw [card_sup_of_le_normalizer' AA XX XX_le_normalizer_AA (disjoint_iff.mpr AA_inf_XX), card_AA,
    card_XX]

theorem XX_mem_decomp : ∀ x ∈ XX, x = 1 ∨ x = swap 4 5 * swap 5 6 ∨ x = (swap 4 5 * swap 5 6) ^ 2 := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : (swap 4 5 * swap 5 6 : S7) ^ (k % (orderOf (swap 4 5 * swap 5 6 : S7) : ℤ)) =
      (swap 4 5 * swap 5 6 : S7) ^ k := zpow_mod_orderOf _ _
  rw [c3_order] at h1
  rw [← h1]
  have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h | h | h <;> rw [h]
  · left; rfl
  · right; left; rfl
  · right; right; rw [zpow_ofNat]

theorem tt_not_mem_AA_sup_XX : tt ∉ AA ⊔ XX := by
  intro h
  obtain ⟨a, ha, x, hx, hax⟩ := (mem_sup_of_commute' AA_comm_XX).mp h
  have hx4 : 4 ≤ (x 4).val ∧ 4 ≤ (x 5).val := by
    rcases XX_mem_decomp x hx with rfl | rfl | rfl <;> decide +kernel
  have h4 : tt 4 = x 4 := by
    rw [hax, Equiv.Perm.mul_apply]
    exact AA_fix a ha _ hx4.1
  have h5 : tt 5 = x 5 := by
    rw [hax, Equiv.Perm.mul_apply]
    exact AA_fix a ha _ hx4.2
  have key : ∀ y ∈ [(1 : S7), swap 4 5 * swap 5 6, (swap 4 5 * swap 5 6) ^ 2],
      tt 4 = y 4 → tt 5 = y 5 → False := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl <;> decide +kernel
  have hmem : x ∈ [(1 : S7), swap 4 5 * swap 5 6, (swap 4 5 * swap 5 6) ^ 2] := by
    rcases XX_mem_decomp x hx with rfl | rfl | rfl <;> simp
  exact key x hmem h4 h5

theorem tt_mem_normalizer_sup : tt ∈ normalizer ((AA ⊔ XX : Subgroup S7) : Set S7) :=
  Subgroup.inf_normalizer_le_normalizer_sup AA XX ⟨tt_mem_normalizer_AA, tt_mem_normalizer_XX⟩

theorem card_gen : Nat.card ↥((AA ⊔ XX) ⊔ Subgroup.zpowers tt) = 72 := by
  rw [card_sup_of_le_normalizer' (AA ⊔ XX) (Subgroup.zpowers tt)
    (Subgroup.zpowers_le.mpr tt_mem_normalizer_sup)
    (disjoint_zpowers_tt _ tt_not_mem_AA_sup_XX), card_AA_sup_XX, card_zpowers_tt]

end VType7

section VType8

open scoped Pointwise

@[expose] def s0 : Set.powersetCard (Fin 7) 3 :=
  ⟨{4, 5, 6}, by show ({4, 5, 6} : Finset (Fin 7)).card = 3; decide⟩

theorem card_stab_s0 : Nat.card (MulAction.stabilizer (Perm (Fin 7)) s0) = 144 := by
  have : MulAction.IsPretransitive (Perm (Fin 7)) (Set.powersetCard (Fin 7) 3) :=
    Set.powersetCard.isPretransitive
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (Perm (Fin 7)) s0)
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ (Perm (Fin 7)) s0, Set.ncard_univ,
    Set.powersetCard.card] at h1
  have h2 : Nat.card (Perm (Fin 7)) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
  have h3 : Nat.card (Fin 7) = 7 := by simp
  have h4 : Nat.choose 7 3 = 35 := by decide
  rw [h2, h3, h4] at h1
  omega

theorem rsq_moves : ∀ j : Fin 7, j.val < 4 → (r ^ 2) j ≠ j := by decide +kernel

theorem r2_mem_Vsub : r ^ 2 ∈ Vsub := mem_klein.mpr (Or.inr (Or.inl rfl))

theorem N_Vsub_fix_ge : ∀ x ∈ normalizer (Vsub : Set S7), ∀ i : Fin 7, 4 ≤ i.val → 4 ≤ (x i).val := by
  intro x hx i hi
  by_contra hlt
  push Not at hlt
  have hw : x⁻¹ * r ^ 2 * x ∈ Vsub := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) (r ^ 2)).mp r2_mem_Vsub
    simpa using this
  have h1 := Vsub_fix _ hw i hi
  simp only [Equiv.Perm.mul_apply] at h1
  have h2 : (r ^ 2) (x i) = x i := by
    have := congrArg x h1
    simpa using this
  exact rsq_moves (x i) hlt h2

theorem N_Vsub_le_stab :
    normalizer (Vsub : Set S7) ≤ MulAction.stabilizer (Perm (Fin 7)) s0 := by
  intro x hx
  rw [MulAction.mem_stabilizer_iff]
  apply Subtype.ext
  show x • ({4, 5, 6} : Finset (Fin 7)) = {4, 5, 6}
  have hsub : x • ({4, 5, 6} : Finset (Fin 7)) ⊆ {4, 5, 6} := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_smul_finset.mp hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    have hi4 : 4 ≤ i.val := by rcases hi with rfl | rfl | rfl <;> decide
    have hxi : 4 ≤ (x i).val := N_Vsub_fix_ge x hx i hi4
    have hxi' := (x i).isLt
    simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.Perm.smul_def]
    have : (x i) = 4 ∨ (x i) = 5 ∨ (x i) = 6 := by
      rcases Nat.lt_or_ge (x i).val 5 with h | h
      · left; apply Fin.ext; simp; omega
      · rcases Nat.lt_or_ge (x i).val 6 with h' | h'
        · right; left; apply Fin.ext; simp; omega
        · right; right; apply Fin.ext; simp; omega
    exact this
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_smul_finset])

theorem card_inf_stab :
    Nat.card ↥(MulAction.stabilizer (Perm (Fin 7)) s0 ⊓ alternatingGroup (Fin 7)) = 72 := by
  have hs : swap (0 : Fin 7) 1 ∈ MulAction.stabilizer (Perm (Fin 7)) s0 := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    show (swap (0 : Fin 7) 1) • ({4, 5, 6} : Finset (Fin 7)) = {4, 5, 6}
    decide
  have h := card_inf_alternating _ hs (sign_swap (by decide))
  rw [card_stab_s0] at h
  omega

theorem N_Vsub_eq :
    normalizer (Vsub : Set S7) ⊓ alternatingGroup (Fin 7) = (AA ⊔ XX) ⊔ Subgroup.zpowers tt := by
  symm
  apply Subgroup.eq_of_le_of_card_ge gen_le_N
  rw [card_gen]
  have hle : normalizer (Vsub : Set S7) ⊓ alternatingGroup (Fin 7) ≤
      MulAction.stabilizer (Perm (Fin 7)) s0 ⊓ alternatingGroup (Fin 7) :=
    inf_le_inf_right _ N_Vsub_le_stab
  have := Subgroup.card_le_of_le hle
  rw [card_inf_stab] at this
  exact this

end VType8

section Shape

open scoped Pointwise

@[expose] def ShapeF (U : Subgroup S7) : Prop :=
  Nonempty (↥(normalizer (U : Set S7) ⊓ alternatingGroup (Fin 7)) ≃* Perm (Fin 4)) ∨
    ∃ (A X : Subgroup S7) (t : S7),
      normalizer (U : Set S7) ⊓ alternatingGroup (Fin 7) = (A ⊔ X) ⊔ Subgroup.zpowers t ∧
      U ≤ A ∧ A ⊓ X = ⊥ ∧ (∀ a ∈ A, ∀ x ∈ X, a * x = x * a) ∧
      (∀ a ∈ A, t * a * t⁻¹ ∈ A) ∧ (∀ x ∈ X, t * x * t⁻¹ ∈ X) ∧
      Nonempty (↥A ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (↥(A ⊔ Subgroup.zpowers t) ≃* Perm (Fin 4)) ∧
      Nonempty (↥(X ⊔ Subgroup.zpowers t) ≃* Perm (Fin 3))

theorem ShapeF_Vsub : ShapeF Vsub :=
  Or.inr ⟨AA, XX, tt, N_Vsub_eq, Vsub_le_AA, AA_inf_XX, AA_comm_XX, tt_conj_AA, tt_conj_XX,
    ⟨(Subgroup.equivMapOfInjective _ emb4 emb4_injective).symm⟩, AAt_equiv, XXt_equiv⟩

theorem ShapeF_Wsub : ShapeF Wsub := Or.inl N_Wsub_equiv

theorem mem_map_conj_iff (c : S7) (U : Subgroup S7) (y : S7) :
    y ∈ U.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * y * c ∈ U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    show c⁻¹ * (c * x * c⁻¹) * c ∈ U
    have : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rw [this]
    exact hx
  · intro h
    exact ⟨c⁻¹ * y * c, h, by show c * (c⁻¹ * y * c) * c⁻¹ = y; group⟩

theorem normalizer_map_conj (c : S7) (U : Subgroup S7) :
    normalizer ((U.map (MulAut.conj c).toMonoidHom : Subgroup S7) : Set S7) =
      (normalizer (U : Set S7)).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [mem_map_conj_iff, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h k
    have := h (c * k * c⁻¹)
    simp only [mem_map_conj_iff] at this
    have e1 : c⁻¹ * (c * k * c⁻¹) * c = k := by group
    have e2 : c⁻¹ * (y * (c * k * c⁻¹) * y⁻¹) * c =
        (c⁻¹ * y * c) * k * (c⁻¹ * y * c)⁻¹ := by group
    rw [e1, e2] at this
    exact this
  · intro h k
    simp only [mem_map_conj_iff]
    have := h (c⁻¹ * k * c)
    have e2 : c⁻¹ * (y * k * y⁻¹) * c =
        (c⁻¹ * y * c) * (c⁻¹ * k * c) * (c⁻¹ * y * c)⁻¹ := by group
    rw [e2]
    exact this

theorem inf_A7_map_conj (c : S7) (K : Subgroup S7) :
    (K.map (MulAut.conj c).toMonoidHom) ⊓ alternatingGroup (Fin 7) =
      (K ⊓ alternatingGroup (Fin 7)).map (MulAut.conj c).toMonoidHom := by
  ext y
  rw [Subgroup.mem_inf, mem_map_conj_iff, mem_map_conj_iff, Subgroup.mem_inf]
  have h : c⁻¹ * y * c ∈ alternatingGroup (Fin 7) ↔ y ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.mem_alternatingGroup, sign_conj_eq]
  rw [h]

end Shape

section Shape2

theorem ShapeF_conj (c : S7) (U : Subgroup S7) (h : ShapeF U) :
    ShapeF (U.map (MulAut.conj c).toMonoidHom) := by
  have hφ : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hN : normalizer ((U.map (MulAut.conj c).toMonoidHom : Subgroup S7) : Set S7) ⊓
      alternatingGroup (Fin 7) =
      (normalizer (U : Set S7) ⊓ alternatingGroup (Fin 7)).map (MulAut.conj c).toMonoidHom := by
    rw [normalizer_map_conj, inf_A7_map_conj]
  rcases h with ⟨⟨e⟩⟩ | ⟨A, X, t, hN', hUA, hAX, hcomm, htA, htX, ⟨eA⟩, ⟨eAt⟩, ⟨eXt⟩⟩
  · left
    exact ⟨(MulEquiv.subgroupCongr hN).trans
      ((Subgroup.equivMapOfInjective _ _ hφ).symm.trans e)⟩
  · right
    refine ⟨A.map (MulAut.conj c).toMonoidHom, X.map (MulAut.conj c).toMonoidHom,
      (MulAut.conj c).toMonoidHom t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hN, hN', Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers]
    · exact Subgroup.map_mono hUA
    · rw [← Subgroup.map_inf_eq A X _ hφ, hAX, Subgroup.map_bot]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← map_mul, hcomm a ha x hx]
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨t * a * t⁻¹, htA a ha, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨t * x * t⁻¹, htX x hx, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · exact ⟨(Subgroup.equivMapOfInjective A _ hφ).symm.trans eA⟩
    · have heq : A.map (MulAut.conj c).toMonoidHom ⊔
          Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) =
          (A ⊔ Subgroup.zpowers t).map (MulAut.conj c).toMonoidHom := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      exact ⟨(MulEquiv.subgroupCongr heq).trans
        ((Subgroup.equivMapOfInjective _ _ hφ).symm.trans eAt)⟩
    · have heq : X.map (MulAut.conj c).toMonoidHom ⊔
          Subgroup.zpowers ((MulAut.conj c).toMonoidHom t) =
          (X ⊔ Subgroup.zpowers t).map (MulAut.conj c).toMonoidHom := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      exact ⟨(MulEquiv.subgroupCongr heq).trans
        ((Subgroup.equivMapOfInjective _ _ hφ).symm.trans eXt)⟩

theorem ShapeF_of_conj (c : S7) (U : Subgroup S7)
    (h : ShapeF (U.map (MulAut.conj c).toMonoidHom)) : ShapeF U := by
  have := ShapeF_conj c⁻¹ _ h
  have e : (U.map (MulAut.conj c).toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom = U := by
    rw [Subgroup.map_map]
    have : (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj c).toMonoidHom = MonoidHom.id S7 := by
      ext x
      simp [MulAut.conj_apply]
    rw [this, Subgroup.map_id]
  rw [e] at this
  exact this

theorem shapeF_of_four (U : Subgroup S7) (hU : U ≤ alternatingGroup (Fin 7))
    (hsq : ∀ x ∈ U, x * x = 1) (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hcard : Nat.card U = 4) : ShapeF U := by
  obtain ⟨c, hc | hc⟩ := classify_four U hU hsq hcomm hcard
  · exact ShapeF_of_conj c U (hc ▸ ShapeF_Vsub)
  · exact ShapeF_of_conj c U (hc ▸ ShapeF_Wsub)

end Shape2

end CFSG.GH74.GLS.IVK.A7
