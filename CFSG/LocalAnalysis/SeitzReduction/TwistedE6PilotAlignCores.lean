module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotAlignTori
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresModel

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin (perfectCore)
open F4Pilot (centralizerPerfectCore centralizerPerfectCore_anti le_centralizerPerfectCore
  normalizer_le_normalizer_centralizerPerfectCore map_centralizerPerfectCore)

local instance twistedE6PilotAlignCoresNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotAlignCoresNeZeroE6 : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotAlignCoresNeZeroE6' : NeZero Tag.E6.rank := ⟨by decide⟩

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {M : Type*} [Group M] {C : Subgroup M}
  (e : L ≃* C)

@[expose] def modelToG (H : Subgroup M) : Subgroup G :=
  UnitaryPilot.modelToG e (H.subgroupOf C)

theorem mem_modelToG {H : Subgroup M} {g : G} :
    g ∈ modelToG e H ↔ ∃ x : C, (x : M) ∈ H ∧ ((e.symm x : L) : G) = g := by
  rw [modelToG, UnitaryPilot.mem_modelToG]
  rfl

theorem symm_mem_modelToG {H : Subgroup M} {x : C} (hx : (x : M) ∈ H) :
    ((e.symm x : L) : G) ∈ modelToG e H :=
  (mem_modelToG e).2 ⟨x, hx, rfl⟩

theorem modelToG_mono {H₁ H₂ : Subgroup M} (h : H₁ ≤ H₂) : modelToG e H₁ ≤ modelToG e H₂ :=
  UnitaryPilot.modelToG_mono e (subgroupOf_mono _ h)

theorem modelToG_le (H : Subgroup M) : modelToG e H ≤ L :=
  UnitaryPilot.modelToG_le e _

theorem modelToG_le_centralizer {H₁ H₂ : Subgroup M} (h : H₁ ≤ centralizer (H₂ : Set M)) :
    modelToG e H₁ ≤ centralizer (modelToG e H₂ : Set G) := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hg
  rw [mem_centralizer_iff]
  intro g' hg'
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hg'
  have hxy : y * x = x * y := Subtype.ext (mem_centralizer_iff.1 (h hx) _ hy)
  rw [← L.coe_mul, ← L.coe_mul, ← map_mul, ← map_mul, hxy]

theorem modelToG_commutator {H₁ H₂ : Subgroup M} (h₁ : H₁ ≤ C) (h₂ : H₂ ≤ C) :
    modelToG e ⁅H₁, H₂⁆ = ⁅modelToG e H₁, modelToG e H₂⁆ := by
  have hsub : ⁅H₁, H₂⁆.subgroupOf C = ⁅H₁.subgroupOf C, H₂.subgroupOf C⁆ := by
    apply map_injective C.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left h₁, inf_of_le_left h₂,
      inf_of_le_left ((commutator_mono h₁ h₂).trans (commutator_le_self _))]
  rw [modelToG, modelToG, modelToG, hsub, UnitaryPilot.modelToG_commutator]

theorem mem_normalizer_modelToG_of_mem_centralizer {t : G} (ht : t ∈ centralizer (L : Set G))
    (H : Subgroup M) : t ∈ normalizer (modelToG e H : Set G) :=
  UnitaryPilot.mem_normalizer_modelToG_of_mem_centralizer e ht _

theorem modelToG_map_conj (H : Subgroup M) (n : C) :
    modelToG e (H.map (MulAut.conj (n : M)).toMonoidHom) =
      (modelToG e H).map (MulAut.conj ((e.symm n : L) : G)).toMonoidHom := by
  have h : (H.map (MulAut.conj (n : M)).toMonoidHom).subgroupOf C =
      (H.subgroupOf C).map (MulAut.conj n).toMonoidHom := by
    ext x
    simp only [mem_subgroupOf, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyC : y ∈ C := by
        have : y = (n : M)⁻¹ * x * n := by rw [← hyx]; group
        rw [this]
        exact mul_mem (mul_mem (inv_mem n.2) x.2) n.2
      refine ⟨⟨y, hyC⟩, hy, Subtype.ext ?_⟩
      rw [coe_mul, coe_mul, coe_inv]
      exact hyx
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  rw [modelToG, modelToG, h, UnitaryPilot.modelToG_map_conj]

end Transport

section Cores

variable {G : Type} [Group G]
  {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}
  (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (A : Subgroup Kˣ)

@[expose] noncomputable def pieceCore (I : Finset (Fin Tag.F4.rank)) : Subgroup G :=
  centralizerPerfectCore (modelToG e (relLeviTorus K A I))

theorem pieceCore_def (I : Finset (Fin Tag.F4.rank)) :
    pieceCore e A I = centralizerPerfectCore (modelToG e (relLeviTorus K A I)) :=
  rfl

theorem le_normalizer_pieceCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (I : Finset (Fin Tag.F4.rank)) : t ∈ normalizer (pieceCore e A I : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

@[expose] noncomputable def neighbourCore (N : F4Pilot.AmalgamNeighbour) : Subgroup G :=
  centralizerPerfectCore (modelToG e (neighbourTorus K A N))

theorem neighbourCore_def (N : F4Pilot.AmalgamNeighbour) :
    neighbourCore e A N = centralizerPerfectCore (modelToG e (neighbourTorus K A N)) :=
  rfl

theorem pieceCore_le_neighbourCore (N : F4Pilot.AmalgamNeighbour) {I : Finset (Fin Tag.F4.rank)}
    (hI : I ⊆ N.nodes) : pieceCore e A I ≤ neighbourCore e A N :=
  centralizerPerfectCore_anti (modelToG_mono e (neighbourTorus_le_relLeviTorus A N hI))

theorem le_normalizer_neighbourCore {t : G} (ht : t ∈ centralizer (L : Set G))
    (N : F4Pilot.AmalgamNeighbour) : t ∈ normalizer (neighbourCore e A N : Set G) :=
  normalizer_le_normalizer_centralizerPerfectCore _
    (mem_normalizer_modelToG_of_mem_centralizer e ht _)

theorem modelToG_perfect {H : Subgroup (ModGL TwistTag.E6.tag K)}
    (hHC : H ≤ graphFixedRootGroup TwistTag.E6 K σ) (hperf : ⁅H, H⁆ = H) :
    ⁅modelToG e H, modelToG e H⁆ = modelToG e H := by
  rw [← modelToG_commutator e hHC hHC, hperf]

section LeviFactors

theorem subsystemGroup_le_centralizer_relLeviTorus {I : Finset (Fin Tag.F4.rank)}
    {J : Set (Fin TwistTag.E6.tag.rank)} (hJ : ∀ i ∈ J, e6IndexToF4 i ∈ I) :
    subsystemGroup TwistTag.E6.tag K J ≤
      centralizer (relLeviTorus K A I : Set (ModGL TwistTag.E6.tag K)) := by
  rw [subsystemGroup_eq_rootSpan]
  refine iSup₂_le fun α hα => rootSubgroup_le_centralizer_relLeviTorus hα.1
    (fun a ha => e6ToF4_eq_zero_of_forall_not_mem_relNodeSet (fun i hi => hα.2 i fun hiJ =>
      hi (mem_relNodeSet.2 (hJ i hiJ))) ha)

end LeviFactors

section Finite

variable [Finite G]

theorem pieceCore_eq (N : F4Pilot.AmalgamNeighbour) {I : Finset (Fin Tag.F4.rank)}
    (hI : I ⊆ N.nodes) :
    pieceCore e A I =
      perfectCore (neighbourCore e A N ⊓ centralizer (modelToG e (relLeviTorus K A I) : Set G)) :=
  F4Pilot.centralizerPerfectCore_eq_of_le (modelToG_mono e (neighbourTorus_le_relLeviTorus A N hI))

theorem neighbourCore_X'_eq_map_conj :
    neighbourCore e A .X' = (neighbourCore e A .X).map (MulAut.conj
      ((e.symm ⟨twistedE6RelWeyl K relWordXPrime, twistedE6RelWeyl_mem σ relWordXPrime⟩ : L) :
        G)).toMonoidHom := by
  rw [neighbourCore, neighbourCore, map_centralizerPerfectCore, ← modelToG_map_conj]
  exact congrArg _ (congrArg _ (map_conj_relWordXPrime_neighbourTorus_X A).symm)

end Finite

end Cores

end CFSG.SeitzReduction.TwistedE6Pilot
