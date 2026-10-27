module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Cent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinTail

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

theorem K_mem_beta : K ∈ betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π :=
  ⟨S.hK, fun _ hM => adj_of_mem_isMaxOrb S.hos.graph S.hπ hM⟩

theorem K'_mem_beta :
    K' ∈ betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π :=
  S.hos.twinSet_subset_beta S.hπ S.hH1 S.hK'

theorem beta_subset_fam :
    betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π ⊆
      fam K (conjSub g (piGen π)) :=
  fun _ hL => S.fam_of_conj_pi (S.hos.beta_subset_conj_image S.hK S.hπ S.hg hL)

theorem false_of_fam_le_beta
    (h : fam K (conjSub g (piGen π)) ⊆
      betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π) : False :=
  S.false_of_cent fun L hL u hu x hx =>
    Subgroup.mem_centralizer_iff.mp (S.hos.beta_le_centralizer (h hL) hu.mem) x hx

theorem map_conj_member {n : ℕ} (J : AEIdent (fam K (conjSub g (piGen π))) n)
    (x : ↥(pSpan (fam K (conjSub g (piGen π))))) (L : Subgroup G) :
    ((conjSub (x : G) L).subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ =
      ((L.subgroupOf (pSpan (fam K (conjSub g (piGen π))))).map J.φ).map
        (MulAut.conj (J.φ x)).toMonoidHom := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hu)
    refine ⟨J.φ (x⁻¹ * u * x), ⟨x⁻¹ * u * x, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩, ?_⟩
    · simpa using hu'
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul,
        map_inv]
      group
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨x * u * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · have := Subgroup.mem_subgroupOf.mp hu
      simpa using conj_mem_conjSub (n := (x : G)) this
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, map_mul,
        map_inv]

theorem pair_le_cent :
    K ≤ Subgroup.centralizer (piGen π : Set G) ∧ K' ≤ Subgroup.centralizer (piGen π : Set G) :=
  ⟨S.hos.beta_le_centralizer S.K_mem_beta, S.hos.beta_le_centralizer S.K'_mem_beta⟩

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
