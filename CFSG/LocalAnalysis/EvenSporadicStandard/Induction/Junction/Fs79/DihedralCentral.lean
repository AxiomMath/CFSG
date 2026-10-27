module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.DihedralLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.IndexTwoCommutator

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup DihedralGroup
open scoped commutatorElement

section

variable {S : Type} [Group S] {r s w₁ u : S}

theorem commutator_pow_mul (hw₁ : w₁ ∈ center S) (hu : u ∈ center S)
    (hrel : s * r * s⁻¹ = w₁ * r⁻¹) (k : ℕ) : ⁅r ^ k * u, s⁆ = (r ^ 2 * w₁⁻¹) ^ k := by
  have hw : ∀ g : S, Commute w₁ g := fun g => (Subgroup.mem_center_iff.1 hw₁ g).symm
  have hu' : u * s * u⁻¹ = s := by
    rw [← Subgroup.mem_center_iff.1 hu s, mul_inv_cancel_right]
  have h1 : s * r ^ k * s⁻¹ = w₁ ^ k * (r ^ k)⁻¹ := by
    rw [← conj_pow, hrel, (hw r⁻¹).mul_pow, inv_pow]
  have h2 : s * (r ^ k)⁻¹ * s⁻¹ = r ^ k * (w₁ ^ k)⁻¹ := by
    have : s * (r ^ k)⁻¹ * s⁻¹ = (s * r ^ k * s⁻¹)⁻¹ := by group
    rw [this, h1]
    group
  calc ⁅r ^ k * u, s⁆ = r ^ k * (u * s * u⁻¹) * (r ^ k)⁻¹ * s⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]
        group
    _ = r ^ k * (s * (r ^ k)⁻¹ * s⁻¹) := by rw [hu']; group
    _ = r ^ k * r ^ k * (w₁ ^ k)⁻¹ := by rw [h2]; group
    _ = (r ^ 2 * w₁⁻¹) ^ k := by
        rw [(hw (r ^ 2)).symm.inv_right.mul_pow, inv_pow, ← pow_mul, mul_comm 2 k, pow_mul, sq]

theorem conj_eq_inv_of_rel (hw₁ : w₁ ∈ center S) (hrel : s * r * s⁻¹ = w₁ * r⁻¹) :
    s * (r ^ 2 * w₁⁻¹) * s⁻¹ = (r ^ 2 * w₁⁻¹)⁻¹ := by
  have hw : ∀ g : S, Commute w₁ g := fun g => (Subgroup.mem_center_iff.1 hw₁ g).symm
  have h2 : s * r ^ 2 * s⁻¹ = (w₁ * r⁻¹) ^ 2 := by rw [← hrel, conj_pow]
  have h3 : s * w₁⁻¹ * s⁻¹ = w₁⁻¹ := by
    rw [Subgroup.mem_center_iff.1 ((center S).inv_mem hw₁) s, mul_inv_cancel_right]
  calc s * (r ^ 2 * w₁⁻¹) * s⁻¹ = (s * r ^ 2 * s⁻¹) * (s * w₁⁻¹ * s⁻¹) := by group
    _ = (w₁ * r⁻¹) ^ 2 * w₁⁻¹ := by rw [h2, h3]
    _ = w₁ * (w₁ * (r⁻¹) ^ 2 * w₁⁻¹) := by rw [(hw r⁻¹).mul_pow]; simp only [sq, mul_assoc]
    _ = (r ^ 2 * w₁⁻¹)⁻¹ := by
        rw [(hw ((r⁻¹) ^ 2)).eq, mul_inv_cancel_right, mul_inv_rev, inv_inv, inv_pow]

end

section NoCase

variable {S : Type} [Group S] {n : ℕ} {φ : S →* DihedralGroup n}

theorem comap_rotations_comm [NeZero n] {r : S} (hr : φ r = DihedralGroup.r 1)
    (hker : φ.ker ≤ center S) {a b : S} (ha : a ∈ (rotations n).comap φ)
    (hb : b ∈ (rotations n).comap φ) : a * b = b * a := by
  obtain ⟨i, hi⟩ := exists_pow_mul_mem_ker hr ha
  obtain ⟨j, hj⟩ := exists_pow_mul_mem_ker hr hb
  have cent : ∀ g ∈ center S, ∀ x : S, Commute g x :=
    fun g hg x => (Subgroup.mem_center_iff.1 hg x).symm
  have ha' : a = r ^ i * ((r ^ i)⁻¹ * a) := by group
  have hb' : b = r ^ j * ((r ^ j)⁻¹ * b) := by group
  have h1 : Commute (r ^ i) (r ^ j) := Commute.pow_pow_self r i j
  have h2 : Commute (r ^ i) ((r ^ j)⁻¹ * b) := (cent _ (hker hj) _).symm
  have h3 : Commute ((r ^ i)⁻¹ * a) (r ^ j) := cent _ (hker hi) _
  have h4 : Commute ((r ^ i)⁻¹ * a) ((r ^ j)⁻¹ * b) := cent _ (hker hi) _
  have := ((h1.mul_right h2).mul_left (h3.mul_right h4))
  rw [← ha', ← hb'] at this
  exact this

variable [Finite S] [NeZero n]

theorem not_mem_commutator_aux {r s w₁ z : S} (hr : φ r = DihedralGroup.r 1) (hs : φ s = sr 0)
    (hn : 4 ∣ n) (hrn : r ^ n = 1) (hker : φ.ker ≤ center S)
    (hker2 : ∀ x ∈ φ.ker, x ^ 2 = 1) (hw₁ : w₁ ∈ φ.ker) (hrel : s * r * s⁻¹ = w₁ * r⁻¹)
    (hz : z ∈ φ.ker) (hz1 : z ≠ 1) : z ∉ commutator S := by
  intro hzc
  obtain ⟨C, hC⟩ : ∃ C : Subgroup S, C = (rotations n).comap φ := ⟨_, rfl⟩
  have hmemC : ∀ x, x ∈ C ↔ φ x ∈ rotations n := fun x => by rw [hC]; rfl
  obtain ⟨w, hwdef⟩ : ∃ w : S, w = r ^ 2 * w₁⁻¹ := ⟨_, rfl⟩
  have hcov : ∀ x : S, x ∈ C ∨ s⁻¹ * x ∈ C := by
    intro x
    simpa only [hC] using mem_comap_rotations_or hs x
  have hcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    comap_rotations_comm hr hker (hC ▸ ha) (hC ▸ hb)
  have hrC : r ∈ C := (hmemC r).2 (mem_rotations.2 ⟨1, hr⟩)
  have hw₁C : w₁ ∈ C :=
    (hmemC w₁).2 (mem_rotations.2 ⟨0, by rw [MonoidHom.mem_ker.1 hw₁, one_def]⟩)
  have hwC : w ∈ C := hwdef ▸ C.mul_mem (C.pow_mem hrC 2) (C.inv_mem hw₁C)
  have hsw : s * w * s⁻¹ = w⁻¹ := hwdef ▸ conj_eq_inv_of_rel (hker hw₁) hrel
  have hnorm : (zpowers w).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    rw [← conj_zpow]
    refine zpow_mem ?_ k
    rcases hcov g with hg | hg
    · rw [hcomm g hg w hwC, mul_inv_cancel_right]
      exact mem_zpowers w
    · have hcw := hcomm _ hg w hwC
      have hconj : g * w * g⁻¹ = s * w * s⁻¹ :=
        calc g * w * g⁻¹ = s * ((s⁻¹ * g) * w * (s⁻¹ * g)⁻¹) * s⁻¹ := by group
          _ = s * w * s⁻¹ := by rw [hcw]; group
      rw [hconj, hsw]
      exact inv_mem (mem_zpowers w)
  have hM : ∀ c ∈ C, ⁅c, s⁆ ∈ zpowers w := by
    intro c hc
    obtain ⟨k, hk⟩ := exists_pow_mul_mem_ker hr (hC ▸ hc)
    have hc' : c = r ^ k * ((r ^ k)⁻¹ * c) := by group
    rw [hc', commutator_pow_mul (hker hw₁) (hker hk) hrel k, ← hwdef]
    exact Subgroup.npow_mem_zpowers w k
  have hle := commutator_le_of_forall_commutator_mem (zpowers w) hcomm hcov hM
  have hzw := hle hzc
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hzw)
  have hw : ∀ g : S, Commute w₁ g := fun g => (Subgroup.mem_center_iff.1 (hker hw₁) g).symm
  have hwk : w ^ k = r ^ (2 * k) * (w₁ ^ k)⁻¹ := by
    rw [hwdef, (hw (r ^ 2)).symm.inv_right.mul_pow, inv_pow, ← pow_mul]
  have hφw : φ (w ^ k) = 1 := by rw [hk]; exact MonoidHom.mem_ker.1 hz
  rw [hwk, map_mul, map_inv, map_pow, map_pow, MonoidHom.mem_ker.1 hw₁, one_pow, inv_one,
    mul_one, hr, r_one_pow, one_def] at hφw
  have hdvd : n ∣ 2 * k := (ZMod.natCast_eq_zero_iff (2 * k) n).1 (DihedralGroup.r.inj hφw)
  have h4 : 4 ∣ 2 * k := hn.trans hdvd
  obtain ⟨t, ht⟩ := hdvd
  obtain ⟨j, hj⟩ : 2 ∣ k := by omega
  have h1 : r ^ (2 * k) = 1 := by rw [ht, pow_mul, hrn, one_pow]
  have h2 : w₁ ^ k = 1 := by rw [hj, pow_mul, hker2 w₁ hw₁, one_pow]
  apply hz1
  rw [← hk, hwk, h1, h2]
  simp

end NoCase

end CFSG.EvenSporadicStandard.Induction.Junction
