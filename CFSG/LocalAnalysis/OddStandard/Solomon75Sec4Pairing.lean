module

public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataLift

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem eq_top_of_index_le_two_of_closure_odd {G : Type*} [Group G] [Finite G] {S : Set G}
    (hS : closure S = ⊤) (hodd : ∀ g ∈ S, Odd (orderOf g)) {Y : Subgroup G}
    (hY : Y.index ≤ 2) : Y = ⊤ := by
  have hpos : 0 < Y.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  rcases (by omega : Y.index = 1 ∨ Y.index = 2) with h1 | h2
  · exact Subgroup.index_eq_one.1 h1
  · have hnorm : Y.Normal := Subgroup.normal_of_index_eq_two h2
    rw [eq_top_iff, ← hS, Subgroup.closure_le]
    intro g hg
    obtain ⟨m, hm⟩ := hodd g hg
    have hpow : g ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one g
    have hg2 : g = (g ^ (m + 1)) ^ 2 := by
      calc g = g ^ (2 * m + 1) * g := by rw [hpow, one_mul]
        _ = (g ^ (m + 1)) ^ 2 := by rw [← pow_succ, ← pow_mul]; congr 1; ring
    rw [hg2]
    have := Subgroup.pow_index_mem Y (g ^ (m + 1))
    rwa [h2] at this

theorem commutator_three_cycles {α : Type*} [DecidableEq α] {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ⁅swap a b * swap b c, swap a b * swap b d⁆ = swap a b * swap c d := by
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hbc.symm
  have := hbd.symm
  have := hcd.symm
  ext x
  rw [commutatorElement_def]
  simp only [mul_inv_rev, swap_inv, Perm.mul_apply]
  by_cases hx1 : x = a
  · subst hx1
    simp [swap_apply_def, *]
  by_cases hx2 : x = b
  · subst hx2
    simp [swap_apply_def, *]
  by_cases hx3 : x = c
  · subst hx3
    simp [swap_apply_def, *]
  by_cases hx4 : x = d
  · subst hx4
    simp [swap_apply_def, *]
  simp [swap_apply_def, *]

theorem sign_swap_mul_swap_of_ne {α : Type*} [DecidableEq α] [Fintype α] {a b c : α}
    (hab : a ≠ b) (hbc : b ≠ c) : sign (swap a b * swap b c) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hbc]
  decide

theorem mul_swap_comm_of_fixed {α : Type*} [DecidableEq α] {σ : Perm α} {a b : α}
    (ha : σ a = a) (hb : σ b = b) : σ * swap a b = swap a b * σ := by
  have h : σ * swap a b * σ⁻¹ = swap a b := by
    rw [← swap_apply_apply, ha, hb]
  calc σ * swap a b = σ * swap a b * σ⁻¹ * σ := by group
    _ = swap a b * σ := by rw [h]

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem CoverSetup.comm_mem_center (C : CoverSetup n K) {x y : K}
    (h : C.ρ x * C.ρ y = C.ρ y * C.ρ x) : ⁅x, y⁆ ∈ center K := by
  rw [← C.ρ_eq_one_iff, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.2 h

theorem CoverSetup.center_eq_of_ne_one (C : CoverSetup n K) {c₀ c₁ : K} (h₀ : c₀ ∈ center K)
    (h₁ : c₁ ∈ center K) (hne₀ : c₀ ≠ 1) (hne₁ : c₁ ≠ 1) : c₀ = c₁ := by
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : center K)).1 C.center_card
  have e₀ : (⟨c₀, h₀⟩ : center K) = z := hz _ (fun h => hne₀ (congrArg Subtype.val h))
  have e₁ : (⟨c₁, h₁⟩ : center K) = z := hz _ (fun h => hne₁ (congrArg Subtype.val h))
  exact congrArg Subtype.val (e₀.trans e₁.symm)

structure CoverSetup.Induces (C : CoverSetup n K) (α : MulAut K) (σ : Perm (Fin n)) : Prop where
  map_ρ : ∀ x, C.ρ (α x) = σ * C.ρ x * σ⁻¹

theorem CoverSetup.induces_conj (C : CoverSetup n K) (s : K) :
    C.Induces (MulAut.conj s) (C.ρ s) :=
  ⟨fun x => by simp [MulAut.conj_apply, map_mul, map_inv]⟩

theorem CoverSetup.Induces.conj_mul {C : CoverSetup n K} {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) (x : K) : C.Induces (MulAut.conj x * α) (C.ρ x * σ) :=
  ⟨fun y => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h.map_ρ]
    group⟩

@[expose] def fixSub (α : MulAut K) : Subgroup K where
  carrier := {x | α x = x}
  mul_mem' := fun {x y} hx hy => by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_mul, hx, hy]
  one_mem' := map_one α
  inv_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [map_inv, hx]

theorem mem_fixSub {α : MulAut K} {x : K} : x ∈ fixSub α ↔ α x = x := Iff.rfl

theorem fixSub_conj (s : K) : fixSub (MulAut.conj s) = centralizer ({s} : Set K) := by
  ext x
  rw [mem_fixSub, mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have : s * x * s⁻¹ * s = x * s := by rw [h]
    simpa using this.symm
  · intro h
    rw [← h]
    group

theorem CoverSetup.Induces.apply_mul_inv_mem_center {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) {x : K} (hx : C.ρ x * σ = σ * C.ρ x) :
    α x * x⁻¹ ∈ center K := by
  rw [← C.ρ_eq_one_iff, map_mul, map_inv, h.map_ρ]
  have : σ * C.ρ x * σ⁻¹ = C.ρ x := by rw [← hx]; group
  rw [this, mul_inv_cancel]

@[expose] def CoverSetup.Induces.commHom {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (H : Subgroup K)
    (hH : ∀ x ∈ H, C.ρ x * σ = σ * C.ρ x) : H →* center K where
  toFun x := ⟨α x * (x : K)⁻¹, h.apply_mul_inv_mem_center (hH x x.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have hy := mem_center_iff.1 (h.apply_mul_inv_mem_center (hH y y.2)) (x : K)⁻¹
    change α ((x : K) * y) * ((x : K) * y)⁻¹ = (α x * (x : K)⁻¹) * (α y * (y : K)⁻¹)
    calc α ((x : K) * y) * ((x : K) * y)⁻¹
        = α x * ((α y * (y : K)⁻¹) * (x : K)⁻¹) := by rw [map_mul]; group
      _ = α x * ((x : K)⁻¹ * (α y * (y : K)⁻¹)) := by rw [hy]
      _ = (α x * (x : K)⁻¹) * (α y * (y : K)⁻¹) := by group

theorem CoverSetup.Induces.commHom_apply {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (H : Subgroup K)
    (hH : ∀ x ∈ H, C.ρ x * σ = σ * C.ρ x) (x : H) :
    ((h.commHom H hH x : center K) : K) = α x * (x : K)⁻¹ := rfl

theorem CoverSetup.Induces.ker_commHom {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (H : Subgroup K)
    (hH : ∀ x ∈ H, C.ρ x * σ = σ * C.ρ x) :
    (h.commHom H hH).ker = (fixSub α).subgroupOf H := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_fixSub]
  constructor
  · intro hx
    have h1 : α x * (x : K)⁻¹ = 1 := congrArg Subtype.val hx
    exact mul_inv_eq_one.1 h1
  · intro hx
    apply Subtype.ext
    show α x * (x : K)⁻¹ = 1
    rw [hx]
    group

theorem CoverSetup.Induces.index_fixSub_le_two {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (H : Subgroup K)
    (hH : ∀ x ∈ H, C.ρ x * σ = σ * C.ρ x) :
    ((fixSub α).subgroupOf H).index ≤ 2 := by
  rw [← h.ker_commHom H hH, Subgroup.index_ker]
  have hdvd : Nat.card (h.commHom H hH).range ∣ 2 := by
    have := Subgroup.card_subgroup_dvd_card (h.commHom H hH).range
    rwa [C.center_card] at this
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem CoverSetup.Induces.commutator_le_fixSub {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) (H : Subgroup K)
    (hH : ∀ x ∈ H, C.ρ x * σ = σ * C.ρ x) : ⁅H, H⁆ ≤ fixSub α := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : h.commHom H hH ⁅(⟨a, ha⟩ : H), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (Subtype.ext
      (mem_center_iff.1 (h.commHom H hH ⟨b, hb⟩).2 (h.commHom H hH ⟨a, ha⟩ : K)))
  have h2 : ((h.commHom H hH ⁅(⟨a, ha⟩ : H), ⟨b, hb⟩⁆ : center K) : K) = 1 := by
    rw [h1]; rfl
  rw [h.commHom_apply] at h2
  exact mul_inv_eq_one.1 h2

theorem CoverSetup.Induces.apply_eq_of_dbl_fixed {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : σ a = a) (hb : σ b = b) (hc : σ c = c) (hd : σ d = d) {x : K}
    (hx : C.ρ x = swap a b * swap c d) : α x = x := by
  obtain ⟨u, hu⟩ := C.exists_ρ_eq (sign_swap_mul_swap_of_ne hab hbc)
  obtain ⟨v, hv⟩ := C.exists_ρ_eq (sign_swap_mul_swap_of_ne hab hbd)
  have hσab := mul_swap_comm_of_fixed ha hb
  have hσbc := mul_swap_comm_of_fixed hb hc
  have hσbd := mul_swap_comm_of_fixed hb hd
  have hσu : C.ρ u * σ = σ * C.ρ u := by
    rw [hu, mul_assoc, ← hσbc, ← mul_assoc, ← hσab, mul_assoc]
  have hσv : C.ρ v * σ = σ * C.ρ v := by
    rw [hv, mul_assoc, ← hσbd, ← mul_assoc, ← hσab, mul_assoc]
  have hcu := h.apply_mul_inv_mem_center hσu
  have hcv := h.apply_mul_inv_mem_center hσv
  set c₁ := α u * u⁻¹ with hc₁
  set c₂ := α v * v⁻¹ with hc₂
  have hαu : α u = u * c₁ := by
    rw [mem_center_iff.1 hcu u, hc₁]; group
  have hαv : α v = v * c₂ := by
    rw [mem_center_iff.1 hcv v, hc₂]; group
  set x' := ⁅u, v⁆ with hx'
  have hρx' : C.ρ x' = C.ρ x := by
    rw [hx', map_commutatorElement, hu, hv, hx, commutator_three_cycles hab hac had hbc hbd hcd]
  have hwc : x'⁻¹ * x ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, hρx', inv_mul_cancel]
  have hαx' : α x' = x' := by
    rw [hx', map_commutatorElement, hαu, hαv]
    exact CFSG.SectionRank.commutatorElement_mul_mem_center u v hcu hcv
  have hαw : α (x'⁻¹ * x) = x'⁻¹ * x := by
    have hρw : C.ρ (α (x'⁻¹ * x)) = 1 := by
      rw [h.map_ρ, (C.ρ_eq_one_iff).2 hwc]; group
    have hαwc : α (x'⁻¹ * x) ∈ center K := (C.ρ_eq_one_iff).1 hρw
    by_cases h1 : x'⁻¹ * x = 1
    · rw [h1, map_one]
    · exact C.center_eq_of_ne_one hαwc hwc (fun h2 => h1 (α.injective (by rw [h2, map_one]))) h1
  have hxx : x = x' * (x'⁻¹ * x) := by group
  calc α x = α (x' * (x'⁻¹ * x)) := by rw [← hxx]
    _ = x' * (x'⁻¹ * x) := by rw [map_mul, hαx', hαw]
    _ = x := by rw [← hxx]

theorem CoverSetup.Induces.apply_eq_of_dbl_swapped {C : CoverSetup n K} {α : MulAut K}
    {σ : Perm (Fin n)} (h : C.Induces α σ) {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : σ a = b) (hb : σ b = a) (hc : σ c = d) (hd : σ d = c) {x : K}
    (hx : C.ρ x = swap a b * swap c d) : α x = x := by
  have h' := h.conj_mul x⁻¹
  have := hab.symm
  have := hac.symm
  have := had.symm
  have := hbc.symm
  have := hbd.symm
  have := hcd.symm
  have hρ : C.ρ x⁻¹ = swap a b * swap c d := by
    rw [map_inv, hx, mul_inv_rev, swap_inv, swap_inv]
    ext y
    by_cases h1 : y = a
    · subst h1
      simp [Perm.mul_apply, swap_apply_def, *]
    by_cases h2 : y = b
    · subst h2
      simp [Perm.mul_apply, swap_apply_def, *]
    by_cases h3 : y = c
    · subst h3
      simp [Perm.mul_apply, swap_apply_def, *]
    by_cases h4 : y = d
    · subst h4
      simp [Perm.mul_apply, swap_apply_def, *]
    simp [Perm.mul_apply, swap_apply_def, *]
  rw [hρ] at h'
  have e1 : (swap a b * swap c d * σ) a = a := by
    simp [Perm.mul_apply, swap_apply_def, *]
  have e2 : (swap a b * swap c d * σ) b = b := by
    simp [Perm.mul_apply, swap_apply_def, *]
  have e3 : (swap a b * swap c d * σ) c = c := by
    simp [Perm.mul_apply, swap_apply_def, *]
  have e4 : (swap a b * swap c d * σ) d = d := by
    simp [Perm.mul_apply, swap_apply_def, *]
  have key := h'.apply_eq_of_dbl_fixed hab hac had hbc hbd hcd e1 e2 e3 e4 hx
  simp only [MulAut.mul_apply, MulAut.conj_apply, inv_inv] at key
  calc α x = x * (x⁻¹ * α x * x) * x⁻¹ := by group
    _ = x := by rw [key]; group

end AhatData

end CFSG.OddStandard.Solomon75
