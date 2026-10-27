module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem mem_zSeries_iff {n : ℕ} {T : Subgroup G} {x : G} :
    x ∈ zSeries n T ↔ ∃ h : x ∈ T,
      (⟨x, h⟩ : ↥T) ∈ Subgroup.upperCentralSeries ↥T n := by
  rw [zSeries, Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, hux⟩
    refine ⟨hux ▸ u.2, ?_⟩
    have heq : (⟨x, hux ▸ u.2⟩ : ↥T) = u := Subtype.ext hux.symm
    rwa [heq]
  · rintro ⟨hx, hu⟩
    exact ⟨⟨x, hx⟩, hu, rfl⟩

theorem y4_zSeries_zero (T : Subgroup G) : zSeries 0 T = ⊥ := by
  rw [zSeries, Subgroup.upperCentralSeries_zero, Subgroup.map_bot]

theorem y4_zSeries_one (T : Subgroup G) : zSeries 1 T = cen T := by
  ext x
  rw [mem_zSeries_iff, Subgroup.upperCentralSeries_one, cen, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hxT, hcent⟩
    refine ⟨hxT, fun y hy => ?_⟩
    have h := Subgroup.mem_center_iff.mp hcent (⟨y, hy⟩ : ↥T)
    simpa using h
  · rintro ⟨hxT, hcomm⟩
    refine ⟨hxT, Subgroup.mem_center_iff.mpr fun v => ?_⟩
    exact Subtype.ext (by simpa using hcomm (v : G) v.2)

theorem y4_mem_zSeries_succ (n : ℕ) (T : Subgroup G) (x : G) :
    x ∈ zSeries (n + 1) T ↔ x ∈ T ∧ ∀ y ∈ T, ⁅x, y⁆ ∈ zSeries n T := by
  rw [mem_zSeries_iff]
  constructor
  · rintro ⟨hxT, hmem⟩
    refine ⟨hxT, fun y hy => ?_⟩
    have h := Subgroup.mem_upperCentralSeries_succ_iff.mp hmem (⟨y, hy⟩ : ↥T)
    have h' := Subgroup.mem_map_of_mem T.subtype h
    simpa [zSeries, map_commutatorElement] using h'
  · rintro ⟨hxT, hcomm⟩
    refine ⟨hxT, Subgroup.mem_upperCentralSeries_succ_iff.mpr fun v => ?_⟩
    obtain ⟨h1, h2⟩ := mem_zSeries_iff.mp (hcomm (v : G) v.2)
    have heq : (⁅(⟨x, hxT⟩ : ↥T), v⁆) = (⟨⁅x, (v : G)⁆, h1⟩ : ↥T) := by
      ext
      simp [commutatorElement_def]
    rwa [heq]

theorem y4_conj_zSeries (n : ℕ) {T : Subgroup G} {y x : G} (hy : y ∈ normalizer (T : Set G))
    (hx : x ∈ zSeries n T) : y * x * y⁻¹ ∈ zSeries n T := by
  revert x
  induction n with
  | zero =>
    intro x hx
    rw [y4_zSeries_zero] at hx ⊢
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx]
    group
  | succ n ih =>
    intro x hx
    rw [y4_mem_zSeries_succ] at hx ⊢
    obtain ⟨hxT, hcomm⟩ := hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hy x).mp hxT, fun u hu => ?_⟩
    have hyinv : y⁻¹ ∈ normalizer (T : Set G) := (normalizer (T : Set G)).inv_mem hy
    have hu' : y⁻¹ * u * y ∈ T := by
      simpa using (Subgroup.mem_normalizer_iff.mp hyinv u).mp hu
    have h1 := ih (hcomm (y⁻¹ * u * y) hu')
    convert h1 using 1
    rw [commutatorElement_def]
    group

theorem y4_conj_omega1 {U : Subgroup G} {y x : G} (hy : ∀ u ∈ U, y * u * y⁻¹ ∈ U)
    (hx : x ∈ omega1 U) : y * x * y⁻¹ ∈ omega1 U := by
  rw [omega1] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem u hu =>
    exact Subgroup.subset_closure
      ⟨hy u hu.1, by rw [conj_pow, hu.2, mul_one, mul_inv_cancel]⟩
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

theorem y4_conj_cen {U : Subgroup G} {y x : G} (hy : y ∈ normalizer (U : Set G))
    (hx : x ∈ cen U) : y * x * y⁻¹ ∈ cen U := by
  rw [cen, Subgroup.mem_inf] at hx ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hy x).mp hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro u hu
  have hyinv : y⁻¹ ∈ normalizer (U : Set G) := (normalizer (U : Set G)).inv_mem hy
  have hu' : y⁻¹ * u * y ∈ U := by
    simpa using (Subgroup.mem_normalizer_iff.mp hyinv u).mp hu
  have hcomm := hx.2 (y⁻¹ * u * y) hu'
  have h := congrArg (fun z => y * z * y⁻¹) hcomm
  rw [show y * ((y⁻¹ * u * y) * x) * y⁻¹ = u * (y * x * y⁻¹) by group,
    show y * (x * (y⁻¹ * u * y)) * y⁻¹ = (y * x * y⁻¹) * u by group] at h
  exact h

@[expose] def y4Zmod (Q N : Subgroup G) (hN : Q ≤ normalizer (N : Set G)) : Subgroup G where
  carrier := {x | x ∈ Q ∧ ∀ y ∈ Q, ⁅x, y⁆ ∈ N}
  mul_mem' := by
    rintro x₁ x₂ ⟨hx₁Q, hx₁⟩ ⟨hx₂Q, hx₂⟩
    refine ⟨Q.mul_mem hx₁Q hx₂Q, fun y hy => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    have h1 : x₁ * ⁅x₂, y⁆ * x₁⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hN hx₁Q) ⁅x₂, y⁆).mp (hx₂ y hy)
    exact N.mul_mem h1 (hx₁ y hy)
  one_mem' := by
    refine ⟨Q.one_mem, fun y hy => ?_⟩
    rw [commutatorElement_one_left]
    exact N.one_mem
  inv_mem' := by
    rintro x ⟨hxQ, hx⟩
    refine ⟨Q.inv_mem hxQ, fun y hy => ?_⟩
    have h1 : x⁻¹ * ⁅y, x⁆ * x ∈ N := by
      have hconj : x⁻¹ * ⁅x, y⁆⁻¹ * x ∈ N := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (hN (Q.inv_mem hxQ)) ⁅x, y⁆⁻¹).mp
            (N.inv_mem (hx y hy))
      rw [show ⁅y, x⁆ = ⁅x, y⁆⁻¹ by rw [← commutatorElement_inv]]
      exact hconj
    rwa [commutatorElement_inv_left]

theorem y4_mem_Zmod {Q N : Subgroup G} (hN : Q ≤ normalizer (N : Set G)) (x : G) :
    x ∈ y4Zmod Q N hN ↔ x ∈ Q ∧ ∀ y ∈ Q, ⁅x, y⁆ ∈ N := Iff.rfl

theorem y4_conj_Zmod {Q N : Subgroup G} (hN : Q ≤ normalizer (N : Set G)) {y x : G}
    (hyQ : y ∈ normalizer (Q : Set G)) (hyN : y ∈ normalizer (N : Set G))
    (hx : x ∈ y4Zmod Q N hN) : y * x * y⁻¹ ∈ y4Zmod Q N hN := by
  rw [y4_mem_Zmod] at hx ⊢
  obtain ⟨hxQ, hx⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp hyQ x).mp hxQ, fun w hw => ?_⟩
  have hyinvQ : y⁻¹ ∈ normalizer (Q : Set G) := (normalizer (Q : Set G)).inv_mem hyQ
  have hw' : y⁻¹ * w * y ∈ Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp hyinvQ w).mp hw
  have hcom : ⁅x, y⁻¹ * w * y⁆ ∈ N := hx (y⁻¹ * w * y) hw'
  have hconj : y * ⁅x, y⁻¹ * w * y⁆ * y⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp hyN ⁅x, y⁻¹ * w * y⁆).mp hcom
  convert hconj using 1
  rw [commutatorElement_def]
  group

end CFSG.OddStandard.HigherRank.YamadaG23
