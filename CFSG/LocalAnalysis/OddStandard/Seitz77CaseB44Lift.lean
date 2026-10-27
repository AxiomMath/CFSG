module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.OddStandard.Seitz77.CaseB45 CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Lift

theorem exists_mem_perfectResidualOf_lift {G L : Type*} [Group G] [Finite G] [Group L]
    {A : Subgroup G} (q : ↥A →* L) (hq : Function.Surjective q) {Λ : Subgroup L}
    (hΛ : ⁅Λ, Λ⁆ = Λ) {Ω : Subgroup G} (hΩ : ∀ a : ↥A, q a ∈ Λ → (a : G) ∈ Ω) {l : L}
    (hl : l ∈ Λ) : ∃ a : ↥A, q a = l ∧ (a : G) ∈ perfectResidualOf Ω := by
  let Hq : Subgroup ↥A := Λ.comap q
  let f : ↥Hq →* ↥Λ := (q.comp Hq.subtype).codRestrict Λ (fun x => x.2)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, ha⟩ := hq (y : L)
    have haHq : a ∈ Hq := by
      show q a ∈ Λ
      rw [ha]
      exact y.2
    exact ⟨⟨a, haHq⟩, Subtype.ext ha⟩
  have : Group.IsPerfect ↥Λ := Subgroup.isPerfect_iff.mpr hΛ
  have hmap := finite_perfectResidual_surjects_to_perfect_image f hf
  have hmem : (⟨l, hl⟩ : ↥Λ) ∈ Subgroup.map f (perfectResidual ↥Hq) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxl⟩ := hmem
  refine ⟨(x : ↥A), congrArg Subtype.val hxl, ?_⟩
  let Q : Subgroup G := (perfectResidual ↥Hq).map (A.subtype.comp Hq.subtype)
  have hQperf : ⁅Q, Q⁆ = Q := by
    show ⁅(perfectResidual ↥Hq).map (A.subtype.comp Hq.subtype),
      (perfectResidual ↥Hq).map (A.subtype.comp Hq.subtype)⁆ = _
    rw [← Subgroup.map_commutator,
      Subgroup.isPerfect_iff.mp (finite_perfectResidual_isPerfect (G := ↥Hq))]
  have hQΩ : Q ≤ Ω := by
    rintro _ ⟨y, -, rfl⟩
    exact hΩ (y : ↥A) y.2
  exact le_perfectResidualOf_of_perfect hQΩ hQperf ⟨x, hx, rfl⟩

end Lift

section Perfect

theorem mem_center_of_commutator_mem_center {K : Type*} [Group K]
    (hK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) {g : K}
    (h : ∀ y : K, ⁅g, y⁆ ∈ Subgroup.center K) : g ∈ Subgroup.center K := by
  have hg2 : g ∈ Subgroup.upperCentralSeries K 2 := by
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    rw [Subgroup.upperCentralSeries_one]
    exact h y
  have hz : ⁅zpowers g, (⊤ : Subgroup K)⁆ ≤ center K := by
    rw [Subgroup.commutator_le]
    intro x hx y _
    have hx2 : x ∈ Subgroup.upperCentralSeries K 2 := (Subgroup.zpowers_le.mpr hg2) hx
    have hxy := (Subgroup.mem_upperCentralSeries_succ_iff.mp hx2) y
    rwa [Subgroup.upperCentralSeries_one] at hxy
  have h2 : ⁅⁅zpowers g, (⊤ : Subgroup K)⁆, (⊤ : Subgroup K)⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc ⁅⁅zpowers g, (⊤ : Subgroup K)⁆, (⊤ : Subgroup K)⁆ ≤ ⁅center K, (⊤ : Subgroup K)⁆ :=
          Subgroup.commutator_mono_left hz
      _ = ⊥ := Subgroup.commutator_center_left _
  have h1 : ⁅⁅(⊤ : Subgroup K), zpowers g⁆, (⊤ : Subgroup K)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (⊤ : Subgroup K) (zpowers g)]
    exact h2
  have h3 : ⁅⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆, zpowers g⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hK] at h3
  exact (Subgroup.commutator_top_left_eq_bot_iff_le_center.mp h3) (Subgroup.mem_zpowers g)

end Perfect

end CFSG.OddStandard.Seitz77
