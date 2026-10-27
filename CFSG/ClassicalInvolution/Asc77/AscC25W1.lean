module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
public import CFSG.ClassicalInvolution.Asc77.AscT7TStar2
public import CFSG.ClassicalInvolution.AschTight.S1916Basic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace C25W

section ZStar

variable {G : Type} [Group G] [Finite G]

theorem mem_zStarOf_iff (H : Subgroup G) {x : G} :
    x ∈ zStarOf H ↔ x ∈ H ∧ ∀ y ∈ H, x⁻¹ * y⁻¹ * x * y ∈ oddCoreOf H := by
  unfold zStarOf
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h.2, fun y hy => ?_⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff] at hh
    have h1 := hh (QuotientGroup.mk (⟨y, hy⟩ : ↥H))
    rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) (⟨y, hy⟩ : ↥H), ← map_mul,
      ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp [mul_assoc]⟩
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk'_apply (classicalInvolutionOddCore ↥H) y, ← map_mul, ← map_mul,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp (hc (y : G) y.2)
    have hwv' : (w : G) = x⁻¹ * (y : G)⁻¹ * x * y := hwv
    have : (y * (⟨x, hx⟩ : ↥H))⁻¹ * ((⟨x, hx⟩ : ↥H) * y) = w := by
      apply Subtype.ext
      rw [hwv']
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
    rw [this]
    exact hw

theorem conj_mem_zStarOf_conjSub (H : Subgroup G) (c : G) {x : G} (hx : x ∈ zStarOf H) :
    c * x * c⁻¹ ∈ zStarOf (conjSub c H) := by
  rw [mem_zStarOf_iff] at hx ⊢
  obtain ⟨hxH, hxc⟩ := hx
  refine ⟨mem_conjSub_iff.mpr (by simpa [mul_assoc] using hxH), fun y hy => ?_⟩
  have hy' : c⁻¹ * y * c ∈ H := mem_conjSub_iff.mp hy
  have h1 := hxc (c⁻¹ * y * c) hy'
  have h2 : oddCoreOf (conjSub c H) = conjSub c (oddCoreOf H) := Thompson.oddCoreOf_conjSub_eq c H
  rw [h2]
  refine mem_conjSub_iff.mpr ?_
  have e : c⁻¹ * ((c * x * c⁻¹)⁻¹ * y⁻¹ * (c * x * c⁻¹) * y) * c =
      x⁻¹ * (c⁻¹ * y * c)⁻¹ * x * (c⁻¹ * y * c) := by group
  rw [e]
  exact h1

theorem centralizer_conj (c a : G) :
    Subgroup.centralizer ({c * a * c⁻¹} : Set G) =
      conjSub c (Subgroup.centralizer ({a} : Set G)) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, mem_conjSub_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * x) * c := by rw [h]
      _ = a * (c⁻¹ * x * c) := by group
  · intro h
    calc x * (c * a * c⁻¹) = c * ((c⁻¹ * x * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = (c * a * c⁻¹) * x := by group

theorem mem_zStarOf_centralizer_conj_iff {z a c : G} (hcz : c * z * c⁻¹ = z) :
    z ∈ zStarOf (Subgroup.centralizer ({c * a * c⁻¹} : Set G)) ↔
      z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) := by
  constructor
  · intro h
    have h1 := conj_mem_zStarOf_conjSub (Subgroup.centralizer ({c * a * c⁻¹} : Set G)) c⁻¹ h
    have hcz' : c⁻¹ * z * c⁻¹⁻¹ = z := by
      calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ := by rw [hcz]
        _ = z := by group
    rw [hcz', centralizer_conj c a, ← conjSub_mul] at h1
    simpa using h1
  · intro h
    have h1 := conj_mem_zStarOf_conjSub (Subgroup.centralizer ({a} : Set G)) c h
    rw [hcz, ← centralizer_conj c a] at h1
    exact h1

end ZStar

section Powers

variable {G : Type} [Group G] [Finite G]

theorem mem_zStarOf_of_pow {z x : G} (hxz : x * z = z * x) {k : ℕ}
    (h : z ∈ zStarOf (Subgroup.centralizer ({x ^ k} : Set G))) :
    z ∈ zStarOf (Subgroup.centralizer ({x} : Set G)) := by
  refine T7T.mem_zStarOf_of_le ?_ h (Subgroup.mem_centralizer_singleton_iff.mpr hxz.symm)
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  exact ((Commute.pow_right (show Commute y x from hy) k).eq)

theorem good_of_mem_zpowers {z x : G} (hz : z ∈ Subgroup.zpowers x) :
    z ∈ zStarOf (Subgroup.centralizer ({x} : Set G)) := by
  have hzC : z ∈ Subgroup.centralizer ({x} : Set G) := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.zpow_left (Commute.refl x) k).eq
  refine T7T.mem_zStarOf_of_le ?_ (T7T.mem_zStarOf_centralizer_self z) hzC
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  exact (Commute.zpow_right (show Commute y x from hy) k).eq

end Powers

section Sylow

variable {G : Type} [Group G] [Finite G]

open CFSG.ClassicalInvolution.Disconnected.AschTight.S1916 in
theorem exists_conj_ge_sylow {S : Sylow 2 G} {H : Subgroup G} (hSH : (S : Subgroup G) ≤ H)
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTH : T ≤ H) :
    ∃ c ∈ H, ∀ t ∈ T, c⁻¹ * t * c ∈ (S : Subgroup G) := by
  obtain ⟨V, hV, hTV⟩ := IsSylow2In.exists_ge hT2 hTH
  have hS : IsSylow2In (S : Subgroup G) H := isSylow2In_of_le S hSH
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥H) (sylowOf hV) (sylowOf hS)
  rw [coe_sylowOf, coe_sylowOf] at hx
  have hVx : conjSub (x : G) V ≤ H := by
    have := conjSub_mono (n := (x : G)) hV.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have h1 : (conjSub (x : G) V).subgroupOf H = (S : Subgroup G).subgroupOf H := by
    have e : (conjSub (x : G) V).subgroupOf H = conjSub x (V.subgroupOf H) := by
      ext y
      rw [Subgroup.mem_subgroupOf, mem_conjSub_iff, mem_conjSub_iff, Subgroup.mem_subgroupOf]
      simp
    rw [e]
    exact hx
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rw [inf_eq_left.mpr hVx, inf_eq_left.mpr hSH] at h2
  refine ⟨(x : G)⁻¹, H.inv_mem x.2, fun t ht => ?_⟩
  have h3 : (x : G) * t * (x : G)⁻¹ ∈ conjSub (x : G) V :=
    mem_conjSub_iff.mpr (by simpa [mul_assoc] using hTV ht)
  rw [h2] at h3
  simpa [mul_assoc] using h3

end Sylow

end C25W

end CFSG.ClassicalInvolution.Asc77
