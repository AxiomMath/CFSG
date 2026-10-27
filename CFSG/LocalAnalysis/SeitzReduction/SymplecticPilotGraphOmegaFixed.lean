module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Fixed

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem neighbourCore_inf_centralizer_eq_of_omega {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : RootKindSp e t f k κ) :
    neighbourCore e k ⊓ centralizer ({t} : Set G) = modelToG e (complSp K k) := by
  have hN : t ∈ normalizer (neighbourCore e k : Set G) := le_normalizer_neighbourCore e htC k
  obtain ⟨-, -, hfix⟩ := neighbourCore_omega_facts hset hKc hf hm e htC ht k rfl rfl hκ h hN
  have hq : IsQuasisimple (fixedSubgroup ((neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv
      (isComponent_top_of_lieModel_PSp hfix).1.1
  have hFperf := isPerfect_iff.mp hq.1
  have hmap : (fixedSubgroup ((neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩)).map
      (neighbourCore e k).subtype = neighbourCore e k ⊓ centralizer ({t} : Set G) :=
    map_eqLocus_normalizerMonoidHom_eq hN
  have hperf : ⁅neighbourCore e k ⊓ centralizer ({t} : Set G),
      neighbourCore e k ⊓ centralizer ({t} : Set G)⁆ =
        neighbourCore e k ⊓ centralizer ({t} : Set G) := by
    rw [← hmap, ← Subgroup.map_commutator, hFperf]
  rw [← perfectCore_neighbourCore_inf_centralizer_eq hset hKc hf hm e htC ht k,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]

theorem map_fixedSubgroup_eq_of_comm {m f : ℕ} (hset : SeitzSetting G L)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hm : 2 ≤ m) (e : L ≃* StatedSp (m + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (m + 1)) {κ : Sp2mKind}
    (hκ : κ = .omegaPlus ∨ κ = .omegaMinus) (h : RootKindSp e t f k κ) {P : Type} [Group P]
    (ψ : P ≃* neighbourCore e k) (α : MulAut P)
    (hψ : ∀ x, t * ((ψ x : neighbourCore e k) : G) * t⁻¹ = ((ψ (α x) : neighbourCore e k) : G)) :
    ((fixedSubgroup α).map ψ.toMonoidHom).map (neighbourCore e k).subtype =
      modelToG e (complSp K k) := by
  rw [← neighbourCore_inf_centralizer_eq_of_omega hset hKc hf hm e htC ht k hκ h]
  ext g
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨(ψ x).2, mem_centralizer_singleton_iff.2 ?_⟩
    have hαx : α x = x := hx
    have h1 := hψ x
    rw [hαx] at h1
    change ((ψ x : neighbourCore e k) : G) * t = t * ((ψ x : neighbourCore e k) : G)
    calc ((ψ x : neighbourCore e k) : G) * t =
          t * ((ψ x : neighbourCore e k) : G) * t⁻¹ * t := by rw [h1]
      _ = t * ((ψ x : neighbourCore e k) : G) := by group
  · intro hg
    obtain ⟨hgE, hgt⟩ := mem_inf.1 hg
    refine ⟨⟨g, hgE⟩, ⟨ψ.symm ⟨g, hgE⟩, ?_, MulEquiv.apply_symm_apply ψ _⟩, rfl⟩
    change α (ψ.symm ⟨g, hgE⟩) = ψ.symm ⟨g, hgE⟩
    apply ψ.injective
    apply Subtype.ext
    rw [← hψ, MulEquiv.apply_symm_apply]
    change t * g * t⁻¹ = g
    rw [mem_centralizer_singleton_iff] at hgt
    rw [← hgt, mul_inv_cancel_right]

open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

end Fixed

end CFSG.SeitzReduction.SymplecticPilot
