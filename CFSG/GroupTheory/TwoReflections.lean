module

public import CFSG.GroupTheory.SteinbergBSInvolutoryInvertedCount
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.GroupTheory

open scoped Pointwise

variable {E : Type*} [Group E]

theorem commute_pow_of_conj_eq_inv {H : Type*} [Group H] {α ρ : H} (hα : α * α = 1)
    (hαρ : α * ρ * α = ρ⁻¹) {m : ℕ} (hm : ρ ^ (2 * m) = 1) :
    α * ρ ^ m = ρ ^ m * α := by
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have hconj : (α * ρ * α) ^ m = α * ρ ^ m * α := by
    simpa [hαinv] using (conj_pow (a := α) (b := ρ) (i := m))
  have hpow2 : (ρ ^ m) * (ρ ^ m) = 1 := by
    rw [← pow_add, show m + m = 2 * m by omega, hm]
  have hfix : α * ρ ^ m * α = ρ ^ m := by
    rw [← hconj, hαρ, inv_pow]
    exact inv_eq_of_mul_eq_one_right hpow2
  have h := congrArg (fun f => f * α) hfix
  simpa [mul_assoc, hα] using h

theorem card_zpowers_sup_zpowers {G : Type*} [Group G] [Finite G] {a b : G} {r : ℕ}
    (hcomm : Commute a b) (ha : orderOf a = r) (hb : orderOf b = r)
    (hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.zpowers b) = r ^ 2 ∧
      ∀ x ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b,
        ∀ y ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b, x * y = y * x := by
  classical
  set H := Subgroup.zpowers a with hH
  set K := Subgroup.zpowers b with hK
  have hHa : Nat.card H = r := by rw [hH, Nat.card_zpowers, ha]
  have hKb : Nat.card K = r := by rw [hK, Nat.card_zpowers, hb]
  have hpt : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h := by
    intro h hh k hk
    rw [hH] at hh
    rw [hK] at hk
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact hcomm.zpow_zpow i j
  have hnorm : H ≤ Subgroup.normalizer (K : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective])
    rintro _ ⟨k, hk, rfl⟩
    change h * (k : G) * h⁻¹ ∈ K
    rw [hpt h hh k hk]
    simpa using hk
  have hEeq : (↑(H ⊔ K) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H K hnorm
  have hbij : Function.Bijective
      (fun p : ↥H × ↥K => (⟨(p.1 : G) * (p.2 : G),
        Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(H ⊔ K))) := by
    constructor
    · rintro ⟨x1, y1⟩ ⟨x2, y2⟩ heq
      have h : (x1 : G) * (y1 : G) = (x2 : G) * (y2 : G) := congrArg Subtype.val heq
      have hmem : (x2 : G)⁻¹ * (x1 : G) ∈ H ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.inv_mem x2.2) x1.2, ?_⟩
        have h2 : (x2 : G)⁻¹ * (x1 : G) = (y2 : G) * (y1 : G)⁻¹ := by
          calc (x2 : G)⁻¹ * (x1 : G)
              = (x2 : G)⁻¹ * ((x1 : G) * (y1 : G)) * (y1 : G)⁻¹ := by group
            _ = (x2 : G)⁻¹ * ((x2 : G) * (y2 : G)) * (y1 : G)⁻¹ := by rw [h]
            _ = (y2 : G) * (y1 : G)⁻¹ := by group
        rw [h2]
        exact K.mul_mem y2.2 (K.inv_mem y1.2)
      rw [hinf, Subgroup.mem_bot] at hmem
      have hx : x1 = x2 := by
        refine Subtype.ext ?_
        have := congrArg (fun z : G => (x2 : G) * z) hmem
        simpa [mul_assoc] using this
      have hy : y1 = y2 := by
        refine Subtype.ext ?_
        have hx' : (x1 : G) = (x2 : G) := congrArg Subtype.val hx
        exact mul_left_cancel (hx' ▸ h)
      rw [hx, hy]
    · intro z
      have hz : (z : G) ∈ (H : Set G) * (K : Set G) := by
        rw [← hEeq]
        exact z.2
      obtain ⟨h, hh, k, hk, hkeq⟩ := hz
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hkeq⟩
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hHa, hKb, pow_two]
  ·
    haveI : IsCyclic ↥H := hH ▸ Subgroup.isCyclic_zpowers a
    haveI : IsCyclic ↥K := hK ▸ Subgroup.isCyclic_zpowers b
    have hEcent : H ⊔ K ≤ Subgroup.centralizer (H : Set G) :=
      sup_le (Subgroup.le_centralizer H)
        (fun k hk => Subgroup.mem_centralizer_iff.mpr (fun h hh => hpt h hh k hk))
    have hHcent : H ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mpr hEcent
    have hKcent : K ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mpr (sup_le
        (fun h hh => Subgroup.mem_centralizer_iff.mpr
          (fun k hk => (hpt h hh k hk).symm))
        (Subgroup.le_centralizer K))
    have habel : H ⊔ K ≤ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) :=
      sup_le hHcent hKcent
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (habel hx) y hy).symm

theorem inverted_zpowers_of_inv {G : Type*} [Group G] {x y : G} (h : x * y * x⁻¹ = y⁻¹) :
    ∀ z ∈ Subgroup.zpowers y, x * z * x⁻¹ = z⁻¹ := by
  intro z hz
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← conj_zpow (a := x) (b := y) (i := k), h]
  exact inv_zpow y k

theorem mem_normalizer_zpowers_of_conj_eq {G : Type*} [Group G] {x y : G}
    (h : x * y * x⁻¹ = y) : x ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (x * y * x⁻¹) = Subgroup.zpowers y
  rw [h]

theorem mem_normalizer_zpowers_of_inv {G : Type*} [Group G] {x y : G}
    (h : x * y * x⁻¹ = y⁻¹) : x ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (x * y * x⁻¹) = Subgroup.zpowers y
  rw [h, Subgroup.zpowers_inv]

