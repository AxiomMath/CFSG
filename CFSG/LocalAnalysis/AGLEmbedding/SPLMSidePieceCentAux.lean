module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideOrbit
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.AGLEmbedding.SPLMSide

open Subgroup

variable {Y : Type} [Group Y]

theorem mul_pow_eq_prod_conj (x u : Y) (n : ℕ) :
    (x * u) ^ n = ((List.range n).map fun i => u ^ i * x * (u ^ i)⁻¹).prod * u ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, List.prod_range_succ, pow_succ]
    group

theorem pow_not_mem_normalizer_of_pow_eq_one {p : ℕ} (hp : p.Prime) {Λ : Subgroup Y} {u : Y}
    (hu : u ^ p = 1) (hn : u ∉ normalizer (Λ : Set Y)) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    u ^ k ∉ normalizer (Λ : Set Y) := by
  intro hk
  have hcop : k.Coprime (orderOf u) := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hu) with h | h
    · rw [h]
      exact Nat.coprime_one_right k
    · rw [h]
      exact (Nat.coprime_of_lt_prime (by omega) hkp hp).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact hn (hm ▸ pow_mem hk m)

theorem prod_conj_eq_mul {p : ℕ} (hp : p.Prime) (u x : Y) :
    ((List.range p).map fun i => u ^ i * x * (u ^ i)⁻¹).prod =
      x * ((List.range (p - 1)).map fun i => u ^ (i + 1) * x * (u ^ (i + 1))⁻¹).prod := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  simp only [pow_zero, one_mul, inv_one, mul_one, Nat.add_sub_cancel]
  rfl

theorem not_mem_centralizer_of_isSolvable_centralizer {u : Y}
    (hsolv : Group.IsSolvable ↥(centralizer ({u} : Set Y))) {Λ : Subgroup Y}
    (hΛ : CFSG.IsComponent Λ) : u ∉ centralizer (Λ : Set Y) := by
  intro hu
  have hle : Λ ≤ centralizer ({u} : Set Y) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hu a ha)
  have : Group.IsSolvable Λ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have : Nontrivial Λ := CFSG.LocalCores.isQuasisimple_nontrivial hΛ.1
  have : Group.IsPerfect Λ := hΛ.1.1
  exact Group.IsPerfect.not_isSolvable Λ inferInstance

theorem isSolvable_of_odd_card_ker {X : Type} [Group X] [Finite X] {Z : Type} [Group Z]
    (f : X →* Z) {S : Subgroup Z} (hS : Group.IsSolvable S) (hfS : f.range ≤ S)
    (hodd : Odd (Nat.card f.ker)) : Group.IsSolvable X := by
  have : Group.IsSolvable f.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsSolvable f.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hfS)
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

variable [Finite Y]

theorem commute_conj_of_not_mem_normalizer {Λ : Subgroup Y} (hΛ : CFSG.IsComponent Λ) {g : Y}
    (hg : g ∉ normalizer (Λ : Set Y)) {a b : Y} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    Commute (g * a * g⁻¹) b := by
  have hΛg : CFSG.IsComponent (Λ.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv _ hΛ
  have hne : Λ.map (MulAut.conj g).toMonoidHom ≠ Λ := fun h =>
    hg (mem_normalizer_of_map_conj_eq h)
  exact (commute_of_ne hΛ hΛg hne b hb (g * a * g⁻¹) ⟨a, ha, rfl⟩).symm

theorem commute_conj_pow {p : ℕ} (hp : p.Prime) {Λ : Subgroup Y} (hΛ : CFSG.IsComponent Λ)
    {u : Y} (hu : u ^ p = 1) (hn : u ∉ normalizer (Λ : Set Y)) {i j : ℕ} (hij : i < j)
    (hjp : j < p) {a b : Y} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    Commute (u ^ j * a * (u ^ j)⁻¹) (u ^ i * b * (u ^ i)⁻¹) := by
  have h := (commute_conj_of_not_mem_normalizer hΛ (pow_not_mem_normalizer_of_pow_eq_one hp hu hn
    (k := j - i) (by omega) (by omega)) ha hb).conj (u ^ i)
  have e : u ^ j = u ^ i * u ^ (j - i) := by rw [← pow_add]; congr 1; omega
  rw [e]
  convert h using 1
  group

theorem prod_conj_mul {p : ℕ} (hp : p.Prime) {Λ : Subgroup Y} (hΛ : CFSG.IsComponent Λ)
    {u : Y} (hu : u ^ p = 1) (hn : u ∉ normalizer (Λ : Set Y)) {a b : Y} (ha : a ∈ Λ)
    (hb : b ∈ Λ) {n : ℕ} (hnp : n ≤ p) :
    ((List.range n).map fun i => u ^ i * (a * b) * (u ^ i)⁻¹).prod =
      ((List.range n).map fun i => u ^ i * a * (u ^ i)⁻¹).prod *
        ((List.range n).map fun i => u ^ i * b * (u ^ i)⁻¹).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih (by omega)]
    have hc : Commute (u ^ n * a * (u ^ n)⁻¹)
        ((List.range n).map fun i => u ^ i * b * (u ^ i)⁻¹).prod := by
      refine Commute.list_prod_right _ _ fun w hw => ?_
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact commute_conj_pow hp hΛ hu hn (List.mem_range.mp hi) (by omega) ha hb
    have e : u ^ n * (a * b) * (u ^ n)⁻¹ = (u ^ n * a * (u ^ n)⁻¹) * (u ^ n * b * (u ^ n)⁻¹) := by
      group
    rw [e, mul_assoc, ← mul_assoc _ (u ^ n * a * (u ^ n)⁻¹), ← hc.eq]
    simp only [mul_assoc]

theorem commute_prod_conj_succ {p : ℕ} (hp : p.Prime) {Λ : Subgroup Y}
    (hΛ : CFSG.IsComponent Λ) {u : Y} (hu : u ^ p = 1) (hn : u ∉ normalizer (Λ : Set Y))
    {a x : Y} (ha : a ∈ Λ) (hx : x ∈ Λ) :
    Commute a ((List.range (p - 1)).map fun i => u ^ (i + 1) * x * (u ^ (i + 1))⁻¹).prod := by
  refine Commute.list_prod_right _ _ fun w hw => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  have hi' := List.mem_range.mp hi
  exact (commute_conj_of_not_mem_normalizer hΛ
    (pow_not_mem_normalizer_of_pow_eq_one hp hu hn (k := i + 1) (by omega) (by omega)) hx ha).symm

theorem mem_normalizer_of_isSolvable_centralizer {p : ℕ} (hp : p.Prime) {u : Y} (hu : u ^ p = 1)
    (hsolv : Group.IsSolvable ↥(centralizer ({u} : Set Y))) {Λ : Subgroup Y}
    (hΛ : CFSG.IsComponent Λ) : u ∈ normalizer (Λ : Set Y) := by
  by_contra hn
  have hδ : ∀ x : Y, (x * u) ^ p = ((List.range p).map fun i => u ^ i * x * (u ^ i)⁻¹).prod :=
    fun x => by rw [mul_pow_eq_prod_conj, hu, mul_one]
  let δ : Λ →* Y :=
    { toFun := fun x => ((x : Y) * u) ^ p
      map_one' := by simp [hu]
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul, hδ]
        exact prod_conj_mul hp hΛ hu hn x.2 y.2 le_rfl }
  have hrange : δ.range ≤ centralizer ({u} : Set Y) := by
    rintro _ ⟨x, rfl⟩
    have hx : Commute (((x : Y) * u) ^ p) (x : Y) := by
      rw [hδ, prod_conj_eq_mul hp]
      exact ((Commute.refl (x : Y)).mul_right
        (commute_prod_conj_succ hp hΛ hu hn x.2 x.2)).symm
    have hxu : Commute (((x : Y) * u) ^ p) ((x : Y) * u) := (Commute.self_pow _ _).symm
    have hcu : Commute (((x : Y) * u) ^ p) u := by
      have := hx.inv_right.mul_right hxu
      rwa [inv_mul_cancel_left] at this
    exact mem_centralizer_singleton_iff.mpr hcu.eq
  have hker : ∀ x ∈ δ.ker, ∀ a : Λ, a * x = x * a := by
    intro x hx a
    have h1 : ((x : Y) * u) ^ p = 1 := hx
    rw [hδ, prod_conj_eq_mul hp] at h1
    have hQ := commute_prod_conj_succ hp hΛ hu hn a.2 x.2
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    rw [eq_inv_of_mul_eq_one_left h1]
    exact hQ.inv_right.eq
  have : Group.IsSolvable δ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hrange)
  have : Group.IsSolvable δ.ker := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (hker b b.2 a)
  have : Group.IsSolvable Λ := Group.isSolvable_of_ker_le_range δ.ker.subtype δ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have : Nontrivial Λ := CFSG.LocalCores.isQuasisimple_nontrivial hΛ.1
  have : Group.IsPerfect Λ := hΛ.1.1
  exact Group.IsPerfect.not_isSolvable Λ inferInstance

end CFSG.AGLEmbedding.SPLMSide
