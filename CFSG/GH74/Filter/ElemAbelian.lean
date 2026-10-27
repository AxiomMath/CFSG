module

public import CFSG.GH74.Filter.Witness

public section

namespace CFSG.GH74.Filter

open Subgroup
open scoped IsMulCommutative commutatorElement

section Commuting

variable {G : Type*} [Group G]

noncomputable def elem2PowHom {C : Type*} [CommGroup C] {r : ℕ} (v : Fin r → C)
    (hv : ∀ i, v i ^ 2 = 1) : (Fin r → Multiplicative (ZMod 2)) →* C where
  toFun a := ∏ i, v i ^ (Multiplicative.toAdd (a i)).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.mul_apply, toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add]

theorem exists_injective_of_commuting_involutions {r : ℕ} (u : Fin r → G)
    (hsq : ∀ i, u i ^ 2 = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    ∃ f : (Fin r → Multiplicative (ZMod 2)) →* G, Function.Injective f := by
  set C := Subgroup.closure (Set.range u)
  have : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcomm i j)
  let v : Fin r → C := fun i => ⟨u i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hv : ∀ i, v i ^ 2 = 1 := fun i => Subtype.ext (by simpa [v] using hsq i)
  let φ : (Fin r → Multiplicative (ZMod 2)) →* G := C.subtype.comp (elem2PowHom v hv)
  have hφ : ∀ a, φ a = (List.ofFn fun i => u i ^ (Multiplicative.toAdd (a i)).val).prod := by
    intro a
    simp only [φ, MonoidHom.comp_apply, elem2PowHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
    rfl
  refine ⟨φ, ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker, hφ] at ha
  rw [Subgroup.mem_bot]
  by_contra hne
  refine hker (fun i => Multiplicative.toAdd (a i)) (fun h0 => hne ?_) ha
  funext i
  exact Multiplicative.toAdd.injective (congrFun h0 i)

theorem card_pi_zmod_two (r : ℕ) : Nat.card (Fin r → Multiplicative (ZMod 2)) = 2 ^ r := by
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem not_gen4_of_commuting_involutions {r : ℕ} (hr : 5 ≤ r) (u : Fin r → G)
    (hsq : ∀ i, u i ^ 2 = 1) (hcomm : ∀ i j, Commute (u i) (u j))
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1) :
    ¬ Gen4 G := by
  obtain ⟨f, hf⟩ := exists_injective_of_commuting_involutions u hsq hcomm hker
  refine not_gen4_of_injective f hf (fun a b => mul_comm a b) (fun a => ?_) ?_
  · funext i
    rw [Pi.pow_apply, Pi.one_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    generalize Multiplicative.toAdd (a i) = z
    revert z
    decide
  · rw [card_pi_zmod_two]
    exact Nat.pow_lt_pow_right (by norm_num) hr

end Commuting

section Section

variable {G : Type*} [Group G]

theorem not_gen4_of_section_involutions [Finite G] {r : ℕ} (hr : 5 ≤ r) (N : Subgroup G)
    (x : Fin r → G) (hnorm : ∀ i, x i ∈ Subgroup.normalizer (N : Set G)) (hsq : ∀ i, x i ^ 2 ∈ N)
    (hcomm : ∀ i j, ⁅x i, x j⁆ ∈ N)
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 → (List.ofFn fun i => x i ^ (a i : ℕ)).prod ∉ N) :
    ¬ Gen4 G := by
  set Q : Subgroup G := Subgroup.closure ((N : Set G) ∪ Set.range x) with hQ
  have hNQ : N ≤ Q := fun n hn => Subgroup.subset_closure (Or.inl hn)
  have hxQ : ∀ i, x i ∈ Q := fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hQnorm : Q ≤ Subgroup.normalizer (N : Set G) := by
    rw [hQ, Subgroup.closure_le]
    rintro y (hy | ⟨i, rfl⟩)
    · exact Subgroup.le_normalizer hy
    · exact hnorm i
  have hN : (N.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNQ).2 hQnorm
  let y : Fin r → Q := fun i => ⟨x i, hxQ i⟩
  let π : Q →* Q ⧸ N.subgroupOf Q := QuotientGroup.mk' _
  let z : Fin r → Q ⧸ N.subgroupOf Q := fun i => π (y i)
  have hmem : ∀ q : Q, π q = 1 ↔ (q : G) ∈ N := fun q => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hz2 : ∀ i, z i ^ 2 = 1 := fun i => by
    show π (y i) ^ 2 = 1
    rw [← map_pow, hmem]
    exact hsq i
  have hzc : ∀ i j, Commute (z i) (z j) := fun i j => by
    show π (y i) * π (y j) = π (y j) * π (y i)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    change (x i * x j)⁻¹ * (x j * x i) ∈ N
    have hg : (x i * x j)⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
      Subgroup.inv_mem _ (Subgroup.mul_mem _ (hnorm i) (hnorm j))
    have hc : (⁅x i, x j⁆)⁻¹ ∈ N := Subgroup.inv_mem _ (hcomm i j)
    have h1 := (Subgroup.mem_normalizer_iff.1 hg _).1 hc
    have heq : (x i * x j)⁻¹ * (x j * x i) =
        (x i * x j)⁻¹ * ⁅x i, x j⁆⁻¹ * ((x i * x j)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact h1
  have key : ∀ (g : G) (hg : g ∈ Subgroup.closure ((N : Set G) ∪ Set.range x)),
      π ⟨g, hg⟩ ∈ Subgroup.closure (Set.range z) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | ⟨i, rfl⟩
      · have h1 : π ⟨g, Subgroup.subset_closure (Or.inl hg)⟩ = 1 := (hmem _).2 hg
        rw [h1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨i, rfl⟩
    | one =>
      have h1 : π ⟨1, Subgroup.one_mem _⟩ = 1 := map_one π
      rw [h1]
      exact Subgroup.one_mem _
    | mul g h hg hh ihg ihh =>
      have h1 : π ⟨g * h, Subgroup.mul_mem _ hg hh⟩ = π ⟨g, hg⟩ * π ⟨h, hh⟩ := map_mul π ⟨g, hg⟩ ⟨h, hh⟩
      rw [h1]
      exact Subgroup.mul_mem _ ihg ihh
    | inv g hg ihg =>
      have h1 : π ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ = (π ⟨g, hg⟩)⁻¹ := map_inv π ⟨g, hg⟩
      rw [h1]
      exact Subgroup.inv_mem _ ihg
  have hgen : Subgroup.closure (Set.range z) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Q) a
    exact key q.1 q.2
  have hcommA : IsMulCommutative (Subgroup.closure (Set.range z)) :=
    Subgroup.isMulCommutative_closure (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hzc i j)
  have hAcomm : ∀ a b : Q ⧸ N.subgroupOf Q, a * b = b * a := fun a b => by
    have ha : a ∈ Subgroup.closure (Set.range z) := hgen ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.closure (Set.range z) := hgen ▸ Subgroup.mem_top b
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Subgroup.closure (Set.range z)) ⟨b, hb⟩)
  have hAsq : ∀ a : Q ⧸ N.subgroupOf Q, a ^ 2 = 1 := fun a => by
    have ha : a ∈ Subgroup.closure (Set.range z) := hgen ▸ Subgroup.mem_top a
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact hz2 i
    | one => exact one_pow 2
    | mul g h hg hh ihg ihh =>
      rw [(show Commute g h from hAcomm g h).mul_pow, ihg, ihh, one_mul]
    | inv g hg ihg => rw [inv_pow, ihg, inv_one]
  have hkerA : ∀ a : Fin r → Fin 2, a ≠ 0 →
      (List.ofFn fun i => z i ^ (a i : ℕ)).prod ≠ 1 := by
    intro a ha h1
    apply hker a ha
    have h2 : π (List.ofFn fun i => y i ^ (a i : ℕ)).prod = 1 := by
      rw [map_list_prod, List.map_ofFn]
      simpa [Function.comp_def, z, map_pow] using h1
    have h3 := (hmem _).1 h2
    have h4 : ((List.ofFn fun i => y i ^ (a i : ℕ)).prod : Q).1 =
        (List.ofFn fun i => x i ^ (a i : ℕ)).prod := by
      simp [Function.comp_def, y]
    rwa [h4] at h3
  obtain ⟨f, hf⟩ := exists_injective_of_commuting_involutions z hz2 hzc hkerA
  have hAfin : Finite (Q ⧸ N.subgroupOf Q) := inferInstance
  have hcard : 2 ^ 4 < Nat.card (Q ⧸ N.subgroupOf Q) := by
    have := Nat.card_le_card_of_injective f hf
    rw [card_pi_zmod_two] at this
    exact lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hr) this
  exact not_gen4_of_surjection Q.subtype π (QuotientGroup.mk'_surjective _) hAcomm hAsq hcard
    (by rw [Subgroup.ker_subtype]; exact bot_le)

theorem not_gen4_of_central_involution_section [Finite G] {r : ℕ} (hr : 5 ≤ r) (t : G)
    (ht : t ^ 2 = 1) (x : Fin r → G) (hc : ∀ i, Commute t (x i))
    (hsq : ∀ i, x i ^ 2 = 1 ∨ x i ^ 2 = t) (hcomm : ∀ i j, ⁅x i, x j⁆ = 1 ∨ ⁅x i, x j⁆ = t)
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 →
      (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1 ∧ (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ t) :
    ¬ Gen4 G := by
  have hN : ∀ y : G, y ∈ Subgroup.zpowers t ↔ y = 1 ∨ y = t := fun y => by
    constructor
    · rintro ⟨k, rfl⟩
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · left
        obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := ⟨k / 2, by omega⟩
        show t ^ (2 * m) = 1
        rw [zpow_mul, zpow_two, ← sq, ht, one_zpow]
      · right
        obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
        show t ^ (2 * m + 1) = t
        rw [zpow_add_one, zpow_mul, zpow_two, ← sq, ht, one_zpow, one_mul]
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hconj : ∀ g : G, Commute t g → ∀ n ∈ Subgroup.zpowers t, g * n * g⁻¹ = n := by
    rintro g hg _ ⟨k, rfl⟩
    show g * t ^ k * g⁻¹ = t ^ k
    have hk : Commute (t ^ k) g := hg.zpow_left k
    rw [← hk.eq, mul_assoc, mul_inv_cancel, mul_one]
  refine not_gen4_of_section_involutions hr (Subgroup.zpowers t) x (fun i => ?_) (fun i => ?_)
    (fun i j => ?_) (fun a ha hmem => ?_)
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj _ (hc i) h hh]
      exact hh
    · intro hh
      have e : (x i)⁻¹ * (x i * h * (x i)⁻¹) * ((x i)⁻¹)⁻¹ = h := by group
      have h2 := hconj ((x i)⁻¹) (hc i).inv_right _ hh
      rw [e] at h2
      rw [h2]
      exact hh
  · rw [hN]
    exact hsq i
  · rw [hN]
    exact hcomm i j
  · rw [hN] at hmem
    rcases hmem with h | h
    · exact (hker a ha).1 h
    · exact (hker a ha).2 h

theorem not_gen4_of_central_section_mul [Finite G] {r : ℕ} (hr : 5 ≤ r) (t : G) (ht : t ^ 2 = 1)
    (x : Fin r → G) (hc : ∀ i, x i * t = t * x i) (hsq : ∀ i, x i * x i = 1 ∨ x i * x i = t)
    (hcomm : ∀ i j, x i * x j = x j * x i ∨ x i * x j = t * (x j * x i))
    (hker : ∀ a : Fin r → Fin 2, a ≠ 0 →
      (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ 1 ∧ (List.ofFn fun i => x i ^ (a i : ℕ)).prod ≠ t) :
    ¬ Gen4 G := by
  refine not_gen4_of_central_involution_section hr t ht x (fun i => (hc i).symm)
    (fun i => by rw [sq]; exact hsq i) (fun i j => ?_) hker
  rcases hcomm i j with h | h
  · left
    rw [commutatorElement_def, h]
    group
  · right
    rw [commutatorElement_def, h]
    group

end Section

end CFSG.GH74.Filter
