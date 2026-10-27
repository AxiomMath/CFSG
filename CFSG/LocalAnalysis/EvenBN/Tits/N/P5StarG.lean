module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem mem_sylT_iff {g : G} :
    g ∈ sylT d ↔ ∃ hg : g ∈ centralizer ({d.t} : Set G),
      (d.ρ ⟨g, hg⟩ : Equiv.Perm (Fin 1755)) ∈ Model.parrottU 1 := by
  unfold sylT
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, by simpa [Subgroup.mem_comap, Subgroup.mem_subgroupOf] using h, rfl⟩

theorem sylT_le_centralizer : sylT d ≤ centralizer ({d.t} : Set G) := fun _ hg =>
  (mem_sylT_iff.1 hg).1

theorem sylT_le_M (hd : d.Hyp) : sylT d ≤ d.M := by
  intro g hg
  obtain ⟨hgt, hρ⟩ := mem_sylT_iff.1 hg
  have hS : (d.ρ ⟨g, hgt⟩ : Equiv.Perm (Fin 1755)) ∈ CFSG.Quasithin.twoF4S := by
    rw [Model.twoF4S_eq_closure]; exact hρ
  have hN : (d.ρ ⟨g, hgt⟩ : Equiv.Perm (Fin 1755)) ∈
      normalizer (Model.hatE : Set (Equiv.Perm (Fin 1755))) :=
    Model.twoF4H_le_normalizer_hatE (Model.twoF4S_le_twoF4H hS)
  exact (hd.mem_normalizer_tSup_iff (X := Model.hatE) Data.s56_hatE_le_titsD hgt).2 hN

theorem sylT_le_CMt (hd : d.Hyp) : sylT d ≤ CMt d := fun _ hg =>
  mem_inf.2 ⟨sylT_le_M hd hg, sylT_le_centralizer hg⟩

theorem t_mem_sylT (hd : d.Hyp) : d.t ∈ sylT d := by
  rw [mem_sylT_iff]
  refine ⟨mem_centralizer_singleton_iff.2 rfl, ?_⟩
  rw [hd.ρ_t]
  exact one_mem _

theorem pv2_mem_sylT (hd : d.Hyp) : d.pv 2 ∈ sylT d := by
  have h2D : Model.parrottV 2 ∈ titsD := (Model.parrottV_mem_titsD_iff (by norm_num)).2 (by decide)
  have hmem : d.pv 2 ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem _)
  rw [mem_sylT_iff]
  refine ⟨hmem, ?_⟩
  have := hd.ρ_lift h2D
  have e : (d.ρ ⟨d.pv 2, hmem⟩ : Equiv.Perm (Fin 1755)) = Model.parrottV 2 := hd.ρ_lift h2D
  rw [e]
  exact Subgroup.subset_closure ⟨2, by simp, rfl⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
