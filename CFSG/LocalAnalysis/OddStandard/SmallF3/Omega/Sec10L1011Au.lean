module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def sec1011_conjAut (Y : Subgroup G) (m : G) (hm : m ∈ normalizer (Y : Set G)) :
    MulAut ↥Y :=
  Y.normalizerMonoidHom ⟨m, hm⟩

theorem sec1011_conjAut_apply (Y : Subgroup G) {m : G} (hm : m ∈ normalizer (Y : Set G))
    (y : ↥Y) : ((sec1011_conjAut Y m hm y : ↥Y) : G) = m * y * m⁻¹ := by
  rfl

theorem sec1011_conjAut_mem {H Y : Subgroup G} {m : G} (hmH : m ∈ H)
    (hm : m ∈ normalizer (Y : Set G)) : sec1011_conjAut Y m hm ∈ autIn H Y := by
  unfold autIn sec1011_conjAut
  exact Subgroup.mem_map.mpr ⟨⟨m, hm⟩, by simpa [Subgroup.mem_subgroupOf] using hmH, rfl⟩

theorem sec1011_exists_conjAut {H Y : Subgroup G} {α : MulAut ↥Y} (hα : α ∈ autIn H Y) :
    ∃ m ∈ H, ∃ hm : m ∈ normalizer (Y : Set G), α = sec1011_conjAut Y m hm := by
  unfold autIn at hα
  obtain ⟨⟨m, hm⟩, hmH, rfl⟩ := Subgroup.mem_map.mp hα
  exact ⟨m, by simpa [Subgroup.mem_subgroupOf] using hmH, hm, rfl⟩

theorem sec1011_conjAut_mul {Y : Subgroup G} {m n : G} (hm : m ∈ normalizer (Y : Set G))
    (hn : n ∈ normalizer (Y : Set G)) :
    sec1011_conjAut Y (m * n) ((normalizer (Y : Set G)).mul_mem hm hn) =
      sec1011_conjAut Y m hm * sec1011_conjAut Y n hn := by
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  rw [sec1011_conjAut_apply]
  show _ = ((sec1011_conjAut Y m hm (sec1011_conjAut Y n hn y) : ↥Y) : G)
  rw [sec1011_conjAut_apply, sec1011_conjAut_apply]
  group

theorem sec1011_conjAut_pow {Y : Subgroup G} {m : G} (hm : m ∈ normalizer (Y : Set G))
    (k : ℕ) :
    sec1011_conjAut Y (m ^ k) ((normalizer (Y : Set G)).pow_mem hm k) =
      sec1011_conjAut Y m hm ^ k := by
  unfold sec1011_conjAut
  have h : (⟨m ^ k, (normalizer (Y : Set G)).pow_mem hm k⟩ : ↥(normalizer (Y : Set G))) =
      (⟨m, hm⟩ : ↥(normalizer (Y : Set G))) ^ k := by
    ext
    simp
  rw [h, map_pow]

theorem sec1011_mem_autIn_inf_centralizer {H Y : Subgroup G} {S : Set G}
    (hS : S ⊆ (Y : Set G)) {α : MulAut ↥Y} :
    α ∈ autIn (H ⊓ centralizer S) Y ↔
      α ∈ autIn H Y ∧ ∀ y : ↥Y, (y : G) ∈ S → α y = y := by
  constructor
  · intro hα
    obtain ⟨m, hm, hmN, rfl⟩ := sec1011_exists_conjAut hα
    obtain ⟨hmH, hmC⟩ := Subgroup.mem_inf.mp hm
    refine ⟨sec1011_conjAut_mem hmH hmN, fun y hy => ?_⟩
    apply Subtype.ext
    rw [sec1011_conjAut_apply]
    have hc : (y : G) * m = m * y := Subgroup.mem_centralizer_iff.mp hmC y hy
    rw [← hc]
    exact mul_inv_cancel_right _ _
  · rintro ⟨hα, hfix⟩
    obtain ⟨m, hmH, hmN, rfl⟩ := sec1011_exists_conjAut hα
    refine sec1011_conjAut_mem (Subgroup.mem_inf.mpr ⟨hmH, ?_⟩) hmN
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h2 := congrArg Subtype.val (hfix ⟨s, hS hs⟩ hs)
    rw [sec1011_conjAut_apply] at h2
    calc s * m = (m * s * m⁻¹) * m := by rw [h2]
      _ = m * s := by group

theorem sec1011_mem_conjClassIn_iff {H Y : Subgroup G} (hH : H ≤ normalizer (Y : Set G))
    {x : ↥Y} {y : G} :
    y ∈ conjClassIn H (x : G) ↔ ∃ α ∈ autIn H Y, y = ((α x : ↥Y) : G) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨sec1011_conjAut Y h (hH hh), sec1011_conjAut_mem hh (hH hh),
      (sec1011_conjAut_apply Y (hH hh) x).symm⟩
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨m, hm, hmN, rfl⟩ := sec1011_exists_conjAut hα
    exact ⟨m, hm, (sec1011_conjAut_apply Y hmN x).symm⟩

end CFSG.OddStandard.SmallF3.Omega
