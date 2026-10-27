module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarOver

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

structure SecR (m : ℕ) (R : Subgroup (Perm (Fin (m + 3)))) : Prop where
  le : R ≤ fixSub (fourSet (m + 3))ᶜ
  comm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r
  trans : ∀ i ∈ fourSet (m + 3), ∀ j ∈ fourSet (m + 3), ∃ r ∈ R, r i = j
  three_le : 3 ≤ m
  pow_four : ∀ r ∈ R, r ^ 4 = 1

namespace SecR

variable {m : ℕ} {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)
include hR

theorem support_le {r : Perm (Fin (m + 3))} (hr : r ∈ R) : r.support.card ≤ 4 := by
  by_cases h1 : r = 1
  · subst h1; simp
  · rw [support_eq_of_transitive hR.le hR.comm hR.trans hr h1, card_fourSet (by have := hR.three_le; omega)]

theorem not_isSwap {r : Perm (Fin (m + 3))} (hr : r ∈ R) : ¬ r.IsSwap := by
  intro hsw
  have h2 := card_support_eq_two.2 hsw
  have h1 : r ≠ 1 := fun h => by rw [h] at h2; simp at h2
  rw [support_eq_of_transitive hR.le hR.comm hR.trans hr h1, card_fourSet (by have := hR.three_le; omega)] at h2
  omega

theorem fix_tail {r : Perm (Fin (m + 3))} (hr : r ∈ R) {i : Fin (m + 3)} (hi : 4 ≤ (i : ℕ)) :
    r i = i :=
  hR.le hr i (by simp [mem_fourSet]; omega)

theorem comm_fixSub {r s : Perm (Fin (m + 3))} (hr : r ∈ R) (hs : s ∈ fixSub (fourSet (m + 3))) :
    r * s = s * r :=
  comm_fixSub_compl (hR.le hr) hs

theorem tau_mem_fixSub : OverData.tau m ∈ fixSub (fourSet (m + 3)) := by
  have h3 := hR.three_le
  intro i hi
  rw [mem_fourSet] at hi
  refine swap_apply_of_ne_of_ne (fun h => ?_) (fun h => ?_)
  · have := congrArg Fin.val h; simp at this; omega
  · have := congrArg Fin.val h; simp at this; omega

end SecR

@[expose] noncomputable def secP {G : Type*} [Group G] {z : G} {m : ℕ} (O : OverData G z m)
    (R : Subgroup (Perm (Fin (m + 3)))) : Subgroup G := R.map O.φ

section Core

variable {G : Type*} [Group G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

include hR in
theorem eq_one_of_isConj_z_mul (hm : 10 ≤ m) {p : G} (hp : p ∈ secP O R) (hc : IsConj z (z * p)) :
    p = 1 := by
  obtain ⟨r, hr, rfl⟩ := hp
  have := O.eq_one_of_isConj_mul (hR.fix_tail hr (by simp; omega))
    (hR.fix_tail hr (by simp; omega))
    (by have := hR.support_le hr; omega) (hR.not_isSwap hr) hc
  rw [this, map_one]

include hR in
theorem eq_one_of_isConj_d_mul (hm : 10 ≤ m) {γ : Perm (Fin (m + 3))}
    (hγ : γ ∈ fixSub (fourSet (m + 3))) {p : G} (hp : p ∈ secP O R)
    (hc : IsConj z (O.φ (γ * OverData.tau m * γ⁻¹) * p)) : p = 1 := by
  obtain ⟨r, hr, rfl⟩ := hp
  apply eq_one_of_isConj_z_mul O hR hm ⟨r, hr, rfl⟩
  have hgr : O.φ γ⁻¹ * O.φ r * O.φ γ = O.φ r := by
    rw [← map_mul, ← map_mul]
    congr 1
    have := hR.comm_fixSub hr hγ
    calc γ⁻¹ * r * γ = γ⁻¹ * (r * γ) := by group
      _ = γ⁻¹ * (γ * r) := by rw [this]
      _ = r := by group
  have h2 : IsConj (O.φ (γ * OverData.tau m * γ⁻¹) * O.φ r) (z * O.φ r) := by
    refine isConj_iff.2 ⟨O.φ γ⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, O.φ_tau]
    calc (O.φ γ)⁻¹ * (O.φ γ * z * (O.φ γ)⁻¹ * O.φ r) * (O.φ γ)⁻¹⁻¹ =
        z * ((O.φ γ)⁻¹ * O.φ r * O.φ γ) := by group
      _ = z * O.φ r := by rw [← map_inv, hgr]
  exact hc.trans h2

include hR in
theorem exists_of_comm_P {x : Perm (Fin (m + 3))} (hx : O.φ x ∈ centralizer (secP O R : Set G)) :
    ∃ r ∈ R, ∃ s ∈ fixSub (fourSet (m + 3)), x = r * s := by
  have hxR : ∀ r ∈ R, x * r = r * x := by
    intro r hr
    have := mem_centralizer_iff.1 hx (O.φ r) ⟨r, hr, rfl⟩
    exact (O.φ_comm_iff.1 this).symm
  exact exists_mul_of_mem_centralizer hR.le hR.comm hR.trans
    (by rw [card_fourSet (by have := hR.three_le; omega)]; omega) hxR

include hR in
theorem exists_of_cent_z {g : G} (hgP : g ∈ centralizer (secP O R : Set G))
    (hgz : g * z = z * g) :
    ∃ r ∈ R, ∃ s ∈ fixSub (fourSet (m + 3)), s * OverData.tau m = OverData.tau m * s ∧
      g = O.φ r * O.φ s := by
  obtain ⟨x, rfl, hxτ⟩ := O.exists_of_mem_centralizer_z (mem_centralizer_singleton_iff.2 hgz)
  obtain ⟨r, hr, s, hs, rfl⟩ := exists_of_comm_P O hR hgP
  refine ⟨r, hr, s, hs, ?_, by rw [map_mul]⟩
  have hrτ : r * OverData.tau m = OverData.tau m * r := hR.comm_fixSub hr hR.tau_mem_fixSub
  calc s * OverData.tau m = r⁻¹ * (r * s * OverData.tau m) := by group
    _ = r⁻¹ * (OverData.tau m * (r * s)) := by rw [hxτ]
    _ = r⁻¹ * (OverData.tau m * r) * s := by group
    _ = r⁻¹ * (r * OverData.tau m) * s := by rw [hrτ]
    _ = OverData.tau m * s := by group

include hR in
theorem exists_of_cent_d {γ : Perm (Fin (m + 3))} {g : G}
    (hgP : g ∈ centralizer (secP O R : Set G))
    (hgd : g ∈ centralizer ({O.φ (γ * OverData.tau m * γ⁻¹)} : Set G)) :
    ∃ r ∈ R, ∃ s ∈ fixSub (fourSet (m + 3)), g = O.φ r * O.φ s := by
  obtain ⟨x, rfl⟩ := O.exists_eq_φ (O.centralizer_φ_conj_le γ hgd)
  obtain ⟨r, hr, s, hs, rfl⟩ := exists_of_comm_P O hR hgP
  exact ⟨r, hr, s, hs, by rw [map_mul]⟩

end Core

end CFSG.OddStandard.AltStdSec
