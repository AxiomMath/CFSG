module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.UnitaryBlocks
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

section Generic

theorem isPGroup_three_of_pow_three {G : Type*} [Group G] (H : Subgroup G)
    (hH : ∀ x ∈ H, x ^ 3 = 1) : IsPGroup 3 H :=
  fun x => ⟨1, by simpa [Subtype.ext_iff] using hH x x.2⟩

theorem not_isCyclic_of_two_cubes {A : Type*} [Group A] [Finite A] {x y : A} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) : ¬ IsCyclic A := by
  classical
  intro hc
  have := Fintype.ofFinite A
  have hle := IsCyclic.card_pow_eq_one_le (α := A) (n := 3) (by norm_num)
  have hsub : ({1, x, x ^ 2, y} : Finset A) ⊆ Finset.univ.filter fun a : A => a ^ 3 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · exact hx
    · rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]
    · exact hy
  have hy1 : y ≠ 1 := fun e => hyx (e ▸ Subgroup.one_mem _)
  have hyx' : y ≠ x := fun e => hyx (e ▸ Subgroup.mem_zpowers _)
  have hyx2 : y ≠ x ^ 2 := fun e => hyx (e ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have hx2 : x ^ 2 ≠ 1 := by
    intro e
    apply hx1
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
      _ = 1 := by rw [hx, e]; simp
  have hx3 : x ≠ x ^ 2 := by
    intro e
    apply hx1
    have : x * x = x * 1 := by rw [mul_one, ← pow_two]; exact e.symm
    exact mul_left_cancel this
  have hcard : ({1, x, x ^ 2, y} : Finset A).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hyx2.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx3, hyx'.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx1.symm, hx2.symm, hy1.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem injective_subgroupMap_hypProj {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    {r ε : ℕ} (A : Subgroup (hypSU h r ε)) (hA : A ⊓ hypScalars h r ε = ⊥) :
    Function.Injective ((hypProj h r ε).subgroupMap A) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (hypProj h r ε) (x : hypSU h r ε) = 1 := by
    have := congrArg Subtype.val hx
    simpa using this
  have h2 : (x : hypSU h r ε) ∈ A ⊓ hypScalars h r ε :=
    ⟨x.2, by rw [← ker_hypProj]; exact h1⟩
  rw [hA, Subgroup.mem_bot] at h2
  exact Subtype.ext h2

theorem commutator_sup_self {G : Type*} [Group G] {U₁ U₂ : Subgroup G} (h₁ : ⁅U₁, U₁⁆ = U₁)
    (h₂ : ⁅U₂, U₂⁆ = U₂) : ⁅U₁ ⊔ U₂, U₁ ⊔ U₂⁆ = U₁ ⊔ U₂ := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  · refine sup_le ?_ ?_
    · calc U₁ = ⁅U₁, U₁⁆ := h₁.symm
        _ ≤ ⁅U₁ ⊔ U₂, U₁ ⊔ U₂⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc U₂ = ⁅U₂, U₂⁆ := h₂.symm
        _ ≤ ⁅U₁ ⊔ U₂, U₁ ⊔ U₂⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem commutator_range_self {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (ρ : G →* H) : ⁅ρ.range, ρ.range⁆ = ρ.range := by
  have := Group.IsPerfect.range ρ
  exact Subgroup.commutator_eq_self

end Generic

section Field

variable {f : ℕ} {K : Type} [Field K]

theorem exists_finset_card_four (h : UnitaryFieldData 2 f K) :
    ∃ s : Finset K, s.card = 4 := by
  have := h.finite
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, h.card]
  have h4 : 4 ≤ Fintype.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by have := h.one_le; omega)
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by simpa using h4)
  exact ⟨t, ht⟩

theorem exists_unit_cube_root (h : UnitaryFieldData 2 f K) : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have := h.finite
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul]
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 2) 1 f
    simpa using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨ω, ?_, ?_⟩
  · rw [← hω]
    exact pow_orderOf_eq_one ω
  · intro e
    rw [e, orderOf_one] at hω
    omega

end Field

section Nodes

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r ε : ℕ} {a₁ a₂ : ℕ}
  (ha₁ : a₁ + 2 ≤ r) (ha₂ : a₂ + 2 ≤ r)

include h in
theorem isPerfect_sl_two : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
  CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four h)

@[expose] noncomputable def nodePair : Subgroup (hypSU h r ε) :=
  (nodeHom (ε := ε) h a₁ ha₁).range ⊔ (nodeHom (ε := ε) h a₂ ha₂).range

theorem isPerfect_nodePair : ⁅nodePair (ε := ε) h ha₁ ha₂, nodePair (ε := ε) h ha₁ ha₂⁆ =
    nodePair (ε := ε) h ha₁ ha₂ := by
  have := isPerfect_sl_two h
  exact commutator_sup_self (commutator_range_self _) (commutator_range_self _)

theorem nodePair_le_flagStabilizer {I : Set ℕ} (hI : I ⊆ Set.Icc 1 r) (hI₁ : a₁ + 1 ∉ I)
    (hI₂ : a₂ + 1 ∉ I) :
    nodePair (ε := ε) h ha₁ ha₂ ≤ flagStabilizer h r ε I := by
  have key : ∀ (a : ℕ) (ha : a + 2 ≤ r), a + 1 ∉ I →
      (nodeHom (ε := ε) h a ha).range ≤ flagStabilizer h r ε I := by
    rintro a ha haI _ ⟨A, rfl⟩
    rw [mem_flagStabilizer]
    intro i hi
    exact nodeHom_smul_hypFlag h a ha A (fun e => haI (e ▸ hi)) (hI hi).2
  exact sup_le (key a₁ ha₁ hI₁) (key a₂ ha₂ hI₂)

noncomputable def nodeΦ : Kˣ × Kˣ →* hypSU h r ε :=
  ((nodeHom (ε := ε) h a₁ ha₁).comp dgHom).noncommCoprod
    ((nodeHom (ε := ε) h a₂ ha₂).comp dgHom)
    (fun u v => commute_nodeHom_dgHom h ha₁ ha₂ u v)

theorem nodeΦ_apply (u v : Kˣ) : nodeΦ (ε := ε) h ha₁ ha₂ (u, v) =
    nodeHom h a₁ ha₁ (dgHom u) * nodeHom h a₂ ha₂ (dgHom v) := by
  simp [nodeΦ]

@[expose] def nodeEntry (a : ℕ) (u : Kˣ) (k : ℕ) : K :=
  if k = a then (u : K) else if k = a + 1 then ((u⁻¹ : Kˣ) : K) else 1

theorem nodeEntry_self (a : ℕ) (u : Kˣ) : nodeEntry a u a = (u : K) := by
  simp [nodeEntry]

theorem nodeEntry_succ (a : ℕ) (u : Kˣ) : nodeEntry a u (a + 1) = ((u⁻¹ : Kˣ) : K) := by
  simp [nodeEntry]

theorem nodeEntry_of_ne {a k : ℕ} (u : Kˣ) (h1 : k ≠ a) (h2 : k ≠ a + 1) :
    nodeEntry a u k = (1 : K) := by
  simp [nodeEntry, h1, h2]

theorem nodeΦ_inl (u v : Kˣ) (k : Fin r) :
    (((nodeΦ (ε := ε) h ha₁ ha₂ (u, v) : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl k) (.inl k) =
      nodeEntry a₁ u k * nodeEntry a₂ v k := by
  rw [nodeΦ_apply, Subgroup.coe_mul, Units.val_mul,
    mul_apply_self_of_isDiag (isDiag_nodeHom_dgHom h a₁ ha₁ u) (isDiag_nodeHom_dgHom h a₂ ha₂ v),
    nodeHom_dgHom_inl, nodeHom_dgHom_inl]
  rfl

theorem nodeΦ_inr_inl (u v : Kˣ) (k : Fin ε) :
    (((nodeΦ (ε := ε) h ha₁ ha₂ (u, v) : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) (.inr (.inl k)) (.inr (.inl k)) = 1 := by
  rw [nodeΦ_apply, Subgroup.coe_mul, Units.val_mul,
    mul_apply_self_of_isDiag (isDiag_nodeHom_dgHom h a₁ ha₁ u) (isDiag_nodeHom_dgHom h a₂ ha₂ v),
    nodeHom_inr_inl, nodeHom_inr_inl, mul_one]

include ha₂ in
theorem eq_one_of_nodeEntry (hlt : a₁ < a₂) {u v : Kˣ}
    (hc : ∀ k : Fin r, nodeEntry a₁ u k * nodeEntry a₂ v k = 1) : u = 1 ∧ v = 1 := by
  have h1 : nodeEntry a₁ u a₁ * nodeEntry a₂ v a₁ = 1 := hc ⟨a₁, by omega⟩
  have h2 : nodeEntry a₁ u (a₂ + 1) * nodeEntry a₂ v (a₂ + 1) = 1 := hc ⟨a₂ + 1, by omega⟩
  rw [nodeEntry_self, nodeEntry_of_ne (a := a₂) v (by omega) (by omega), mul_one] at h1
  rw [nodeEntry_succ, nodeEntry_of_ne (a := a₁) u (by omega) (by omega), one_mul] at h2
  refine ⟨Units.ext h1, ?_⟩
  have : (v⁻¹ : Kˣ) = 1 := Units.ext h2
  simpa using this

@[expose] noncomputable def nodeA : Subgroup (hypSU h r ε) :=
  ((powMonoidHom 3 : Kˣ →* Kˣ).ker.prod (powMonoidHom 3 : Kˣ →* Kˣ).ker).map
    (nodeΦ (ε := ε) h ha₁ ha₂)

theorem mem_nodeA_iff {g : hypSU h r ε} : g ∈ nodeA (ε := ε) h ha₁ ha₂ ↔
    ∃ u v : Kˣ, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ nodeΦ (ε := ε) h ha₁ ha₂ (u, v) = g := by
  simp only [nodeA, Subgroup.mem_map, Subgroup.mem_prod, MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
    exact ⟨u, v, hu, hv, rfl⟩
  · rintro ⟨u, v, hu, hv, rfl⟩
    exact ⟨(u, v), ⟨hu, hv⟩, rfl⟩

theorem nodeA_le_nodePair : nodeA (ε := ε) h ha₁ ha₂ ≤ nodePair h ha₁ ha₂ := by
  intro g hg
  obtain ⟨u, v, -, -, rfl⟩ := (mem_nodeA_iff h ha₁ ha₂).mp hg
  rw [nodeΦ_apply]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

theorem isPGroup_nodeA : IsPGroup 3 (nodeA (ε := ε) h ha₁ ha₂) := by
  refine isPGroup_three_of_pow_three _ fun g hg => ?_
  obtain ⟨u, v, hu, hv, rfl⟩ := (mem_nodeA_iff h ha₁ ha₂).mp hg
  rw [← map_pow]
  have : ((u, v) : Kˣ × Kˣ) ^ 3 = 1 := by
    ext <;> simp [hu, hv]
  rw [this, map_one]

theorem nodeΦ_injective (hlt : a₁ < a₂) : Function.Injective (nodeΦ (ε := ε) h ha₁ ha₂) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨u, v⟩ hz
  have key : ∀ k : Fin r, nodeEntry a₁ u k * nodeEntry a₂ v k = 1 := fun k => by
    rw [← nodeΦ_inl h ha₁ ha₂ u v k, hz]
    simp
  obtain ⟨hu, hv⟩ := eq_one_of_nodeEntry ha₂ hlt key
  subst hu hv
  rfl

theorem not_isCyclic_nodeA (hlt : a₁ < a₂) : ¬ IsCyclic (nodeA (ε := ε) h ha₁ ha₂) := by
  obtain ⟨ω, hω3, hω1⟩ := exists_unit_cube_root h
  have := h.finite
  have hmem : ∀ u v : Kˣ, u ^ 3 = 1 → v ^ 3 = 1 → nodeΦ (ε := ε) h ha₁ ha₂ (u, v) ∈
      nodeA (ε := ε) h ha₁ ha₂ := fun u v hu hv => (mem_nodeA_iff h ha₁ ha₂).mpr ⟨u, v, hu, hv, rfl⟩
  have hinj := nodeΦ_injective (ε := ε) h ha₁ ha₂ hlt
  refine not_isCyclic_of_two_cubes
    (x := ⟨nodeΦ (ε := ε) h ha₁ ha₂ (ω, 1), hmem ω 1 hω3 (one_pow 3)⟩)
    (y := ⟨nodeΦ (ε := ε) h ha₁ ha₂ (1, ω), hmem 1 ω (one_pow 3) hω3⟩) ?_ ?_ ?_ ?_
  · apply Subtype.ext
    show nodeΦ (ε := ε) h ha₁ ha₂ (ω, 1) ^ 3 = 1
    rw [← map_pow]
    have : ((ω, 1) : Kˣ × Kˣ) ^ 3 = 1 := by ext <;> simp [hω3]
    rw [this, map_one]
  · apply Subtype.ext
    show nodeΦ (ε := ε) h ha₁ ha₂ (1, ω) ^ 3 = 1
    rw [← map_pow]
    have : ((1, ω) : Kˣ × Kˣ) ^ 3 = 1 := by ext <;> simp [hω3]
    rw [this, map_one]
  · intro e
    have := hinj (a₁ := (ω, 1)) (a₂ := 1) (by simpa using congrArg Subtype.val e)
    exact hω1 (congrArg Prod.fst this)
  · intro hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hm' : nodeΦ (ε := ε) h ha₁ ha₂ ((ω, 1) ^ m) = nodeΦ (ε := ε) h ha₁ ha₂ (1, ω) := by
      rw [map_zpow]
      exact congrArg Subtype.val hm
    have := congrArg Prod.snd (hinj hm')
    simp at this
    exact hω1 this.symm

theorem node_scalar_trivial (hlt : a₁ < a₂) (hr : ¬ (r = 3 ∧ ε = 0)) {u v : Kˣ} (hu : u ^ 3 = 1)
    (hz : nodeΦ (ε := ε) h ha₁ ha₂ (u, v) ∈ hypScalars h r ε) :
    u = 1 ∧ v = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_entry hz
  have E : ∀ k : Fin r, nodeEntry a₁ u k * nodeEntry a₂ v k = c := fun k => by
    rw [← nodeΦ_inl h ha₁ ha₂ u v k, hc]
    simp
  have hc1 : (c : K) = 1 := by
    by_cases hε : 0 < ε
    · have := hc (.inr (.inl ⟨0, hε⟩)) (.inr (.inl ⟨0, hε⟩))
      rw [nodeΦ_inr_inl] at this
      simpa using this.symm
    · have hε0 : ε = 0 := by omega
      by_cases hadj : a₁ + 1 < a₂
      · have h1 : nodeEntry a₁ u a₁ * nodeEntry a₂ v a₁ = c := E ⟨a₁, by omega⟩
        have h2 : nodeEntry a₁ u (a₁ + 1) * nodeEntry a₂ v (a₁ + 1) = c :=
          E ⟨a₁ + 1, by omega⟩
        rw [nodeEntry_self, nodeEntry_of_ne (a := a₂) v (by omega) (by omega), mul_one] at h1
        rw [nodeEntry_succ, nodeEntry_of_ne (a := a₂) v (by omega) (by omega), mul_one] at h2
        have hu' : (u⁻¹ : Kˣ) = u := Units.ext (h2.trans h1.symm)
        have hu2 : u ^ 2 = 1 := by
          calc u ^ 2 = u * u := by rw [pow_two]
            _ = u * u⁻¹ := by rw [hu']
            _ = 1 := mul_inv_cancel u
        have : u = 1 := by
          calc u = u ^ 3 * (u ^ 2)⁻¹ := by group
            _ = 1 := by rw [hu, hu2]; simp
        rw [← h1, this]
        simp
      · have hadj' : a₂ = a₁ + 1 := by omega
        by_cases ha0 : 1 ≤ a₁
        · have h1 : nodeEntry a₁ u 0 * nodeEntry a₂ v 0 = c := E ⟨0, by omega⟩
          rw [nodeEntry_of_ne (a := a₁) u (by omega) (by omega),
            nodeEntry_of_ne (a := a₂) v (by omega) (by omega), mul_one] at h1
          exact h1.symm
        · have h4 : 4 ≤ r := by
            by_contra hcon
            exact hr ⟨by omega, hε0⟩
          have h1 : nodeEntry a₁ u 3 * nodeEntry a₂ v 3 = c := E ⟨3, by omega⟩
          rw [nodeEntry_of_ne (a := a₁) u (by omega) (by omega),
            nodeEntry_of_ne (a := a₂) v (by omega) (by omega), mul_one] at h1
          exact h1.symm
  have hc1' : c = 1 := Units.ext hc1
  exact eq_one_of_nodeEntry ha₂ hlt fun k => by rw [E k, hc1']; rfl

theorem nodeA_inf_scalars (hlt : a₁ < a₂) (hr : ¬ (r = 3 ∧ ε = 0)) :
    nodeA (ε := ε) h ha₁ ha₂ ⊓ hypScalars h r ε = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg, hz⟩
  obtain ⟨u, v, hu, hv, rfl⟩ := (mem_nodeA_iff h ha₁ ha₂).mp hg
  obtain ⟨rfl, rfl⟩ := node_scalar_trivial h ha₁ ha₂ hlt hr hu hz
  rw [Subgroup.mem_bot]
  exact map_one _

include ha₁ ha₂ in
theorem exists_node_witness {I : Set ℕ} (hI : I ⊆ Set.Icc 1 r) (hlt : a₁ < a₂)
    (hI₁ : a₁ + 1 ∉ I) (hI₂ : a₂ + 1 ∉ I) (hr : ¬ (r = 3 ∧ ε = 0)) :
    ∃ V : Subgroup (hypSU h r ε), V ≤ flagStabilizer h r ε I ∧ ⁅V, V⁆ = V ∧
      ∃ A : Subgroup (hypSU h r ε), A ≤ V ∧ IsPGroup 3 A ∧ ¬ IsCyclic A ∧
        A ⊓ hypScalars h r ε = ⊥ :=
  ⟨nodePair h ha₁ ha₂, nodePair_le_flagStabilizer h ha₁ ha₂ hI hI₁ hI₂,
    isPerfect_nodePair h ha₁ ha₂, nodeA (ε := ε) h ha₁ ha₂, nodeA_le_nodePair h ha₁ ha₂,
    isPGroup_nodeA h ha₁ ha₂, not_isCyclic_nodeA h ha₁ ha₂ hlt,
    nodeA_inf_scalars h ha₁ ha₂ hlt hr⟩

end Nodes

end CFSG.HardMathSupport.Curtis.UnitaryLevi
