module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinHyps

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem le_cent_piGen (hzc : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ u : G,
    IsUniqueInvolution L u → ∀ x ∈ piGen π, x * u = u * x) :
    conjSub g (piGen π) ≤ Subgroup.centralizer (piGen π : Set G) := by
  rw [← S.fam_gen]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨x, rfl⟩ := hL
  have hLΩ : conjSub (x : G) K ∈ CoreAssembly.conjClass K₀ := fam_subset S.hos.graph S.hK ⟨x, rfl⟩
  have hu := S.hz.conj (x : G)
  have hβ := S.hos.mem_beta_of_centralizes S.hπ S.hH1 hLΩ hu
    (hzc _ ⟨x, rfl⟩ _ hu)
  exact S.hos.beta_le_centralizer hβ

theorem false_of_cent (hzc : ∀ L ∈ fam K (conjSub g (piGen π)), ∀ u : G,
    IsUniqueInvolution L u → ∀ x ∈ piGen π, x * u = u * x) : False := by
  have hX' := S.le_cent_piGen hzc
  have hgen : (⨆ M ∈ π ∪ conjSub g '' π, M) = ⊤ :=
    (graph_17_10 S.hos.graph S.hK S.hπ).generate (iSup_conjClass_eq_top S.hs.gen) g S.hg
  have hN : (⨆ M ∈ π ∪ conjSub g '' π, M) ≤ Subgroup.normalizer (piGen π : Set G) := by
    refine iSup₂_le fun M hM => ?_
    rcases hM with hM | ⟨M₀, hM₀, rfl⟩
    · exact (le_piGen hM).trans Subgroup.le_normalizer
    · have hM' : conjSub g M₀ ≤ conjSub g (piGen π) := by
        rw [← piGen_conj]
        exact le_piGen ⟨M₀, hM₀, rfl⟩
      exact (hM'.trans hX').trans (Subgroup.centralizer_le_normalizer _)
  rw [hgen] at hN
  have hXn : ∀ x : G, conjSub x (piGen π) = piGen π := fun x => by
    ext y
    rw [mem_conjSub_iff]
    have := Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_top x⁻¹)) y
    rw [inv_inv] at this
    exact this.symm
  have hKX : K ≤ piGen π := by
    have h1 : conjSub g⁻¹ (conjSub g K) ≤ conjSub g⁻¹ (piGen π) :=
      conjSub_mono (le_piGen S.hg)
    rwa [conjSub_inv_conjSub, hXn] at h1
  obtain ⟨a, ha, b, hb, hab⟩ := noncomm_of_mem S.hs.hyp S.hK
  exact hab ((Subgroup.mem_centralizer_iff.mp (S.hos.le_centralizer_piGen S.hπ ha)) b
    (hKX hb)).symm

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
