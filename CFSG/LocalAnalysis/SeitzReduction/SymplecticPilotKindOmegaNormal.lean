module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaIota
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaFixed
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverExists

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus
  commutator_coordinateQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus coe_quadPlus)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_orthogonal_involutions_conjugate_into_semilinear_image)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Conj

variable (k : Type) [Field k] [Finite k]

theorem kOmega_hconj {N f : ℕ} (hN : 4 ≤ N) (hf : 1 ≤ f) (hK : Nat.card k = 2 ^ f) :
    ∀ α : MulAut (matrixProjectiveDerived (reindexQuadraticForm (plusIndexEquiv N) (quadPlus N k))),
      α * α = 1 → ∃ β, β⁻¹ * α * β ∈
        matrixProjectiveImage (reindexQuadraticForm (plusIndexEquiv N) (quadPlus N k)) := by
  have h : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus N k))) .POmegaPlus N 2 f :=
    ⟨⟨Nat.prime_two, hf, hN⟩, k, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  exact ((even_orthogonal_involutions_conjugate_into_semilinear_image
    _ .POmegaPlus (Or.inl rfl) N f h).1 k hK (MulEquiv.refl _)).1

end Conj

section Param


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_kOmegaParam (hset : SeitzSetting G L) {r f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hr : 2 ≤ r) (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (r + 1))
    (h : RootKindSp e t f k .omegaPlus) :
    ∃ (Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃* neighbourCore e k) (σ : K ≃+* K),
      (∀ g, t * ((Φ g : neighbourCore e k) : G) * t⁻¹ =
        ((Φ (kOmegaBetaC K r g) : neighbourCore e k) : G)) ∧
      ∀ x : StatedSp r K, ((Φ (kOmegaIota hr hr3 hKc hf x) : neighbourCore e k) : G) =
        ((e.symm (complSpEquiv k (fieldSp r K σ x)) : L) : G) := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hN : t ∈ normalizer (neighbourCore e k : Set G) := le_normalizer_neighbourCore e htC k
  obtain ⟨hty, hout, hfix⟩ := neighbourCore_omega_facts (m := r) hset hKc hf hr e htC ht k rfl rfl
    (Or.inl rfl) h hN
  have hty' : LieModel (neighbourCore e k) .POmegaPlus (r + 1) 2 f := hty
  obtain ⟨ε₀⟩ := OmegaPilot.nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hty' K hKc
  set π := F4Pilot.omegaProjEquiv (plusIndexEquiv (r + 1)) (quadPlus (r + 1) K)
    (coe_quadPlus (r + 1) K) (kOmega_matrixDerivedScalars_eq_bot K r) with hπ
  have hreg := regular_coordinateQuadPlus (K := K) (n := r + 1) (by omega)
  have hE := commutator_coordinateQuadPlus (K := K) (n := r + 1) (by omega)
  have hθθ : (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ *
      (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (neighbourCore e k : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hout hfix (by omega : 1 ≤ f) hKc
    (by omega : 4 ≤ r + 1) hreg.1 hreg.2 hE (kOmega_hconj K (by omega) (by omega) hKc)
    (kOmega_reindexQuadraticForm_vec K r) (ε₀.trans π)
  set Φ₀ : StatedOmega (StatedQuadPlus (r + 1) K) ≃* neighbourCore e k := π.trans ψ with hΦ₀
  have hΦ₀t : ∀ g, t * ((Φ₀ g : neighbourCore e k) : G) * t⁻¹ =
      ((Φ₀ (kOmegaBetaC K r g) : neighbourCore e k) : G) := by
    intro g
    have h12 : ((neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩) (ψ (π g)) =
        ψ (π (kOmegaBetaC K r g)) :=
      (hψ (π g)).trans (congrArg ψ (F4Pilot.omegaProjEquiv_omegaSymmetryAut _ _ _ _ _ g).symm)
    change t * ((ψ (π g) : neighbourCore e k) : G) * t⁻¹ =
      ((ψ (π (kOmegaBetaC K r g)) : neighbourCore e k) : G)
    rw [← h12, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hfixmap := map_fixedSubgroup_eq_of_comm (m := r) hset hKc hf hr e htC ht k (Or.inl rfl) h
    Φ₀ (kOmegaBetaC K r) hΦ₀t
  set ι := kOmegaIota (k := K) hr hr3 hKc hf with hιdef
  set κ : StatedSp r K →* G := (neighbourCore e k).subtype.comp (Φ₀.toMonoidHom.comp ι) with hκdef
  have hκinj : Function.Injective κ := (neighbourCore e k).subtype_injective.comp
    (Φ₀.injective.comp (kOmegaIota_injective hr hr3 hKc hf))
  have hκr : κ.range = modelToG e (complSp K k) := by
    rw [hκdef, MonoidHom.range_comp, MonoidHom.range_comp, hιdef, range_kOmegaIota, hfixmap]
  set lam : StatedSp r K →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((complSp K k).subtype.comp (complSpEquiv (K := K) k).toMonoidHom)) with hlamdef
  have hlaminj : Function.Injective lam := L.subtype_injective.comp (e.symm.injective.comp
    ((complSp K k).subtype_injective.comp (complSpEquiv (K := K) k).injective))
  have hlamr : lam.range = modelToG e (complSp K k) := by
    rw [hlamdef, MonoidHom.range_comp, MonoidHom.range_comp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (complSpEquiv (K := K) k).surjective, ← MonoidHom.range_eq_map,
      range_subtype]
    rfl
  set δ : MulAut (StatedSp r K) := ((MonoidHom.ofInjective hlaminj).trans
    (MulEquiv.subgroupCongr (hlamr.trans hκr.symm))).trans (MonoidHom.ofInjective hκinj).symm
    with hδdef
  have hκδ : ∀ g, κ (δ g) = lam g := by
    intro g
    have h1 := (MonoidHom.ofInjective hκinj).apply_symm_apply
      (MulEquiv.subgroupCongr (hlamr.trans hκr.symm) (MonoidHom.ofInjective hlaminj g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨s, σ₀, hsσ⟩ := exists_eq_conj_mul_fieldSp hr3 δ
  have hιs : kOmegaBetaC K r (ι s) = ι s := by
    have hmem : ι s ∈ fixedSubgroup (kOmegaBetaC K r) := by
      rw [hιdef, ← range_kOmegaIota hr hr3 hKc hf]
      exact ⟨s, rfl⟩
    exact hmem
  refine ⟨(MulAut.conj (ι s)).trans Φ₀, σ₀⁻¹, fun g => ?_, fun x => ?_⟩
  · change t * ((Φ₀ (ι s * g * (ι s)⁻¹) : neighbourCore e k) : G) * t⁻¹ =
      ((Φ₀ (ι s * kOmegaBetaC K r g * (ι s)⁻¹) : neighbourCore e k) : G)
    have h2 : kOmegaBetaC K r (ι s * g * (ι s)⁻¹) = ι s * kOmegaBetaC K r g * (ι s)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hιs]
    rw [hΦ₀t, h2]
  · have h1 := hκδ (fieldSp r K σ₀⁻¹ x)
    rw [hsσ, MulAut.mul_apply, MulAut.conj_apply, ← MulAut.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, MulAut.one_apply] at h1
    change ((Φ₀ (ι s * ι x * (ι s)⁻¹) : neighbourCore e k) : G) = _
    rw [← map_inv, ← map_mul, ← map_mul]
    exact h1

end Param

end CFSG.SeitzReduction.SymplecticPilot
