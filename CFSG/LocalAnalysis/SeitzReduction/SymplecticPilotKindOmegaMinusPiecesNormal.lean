module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaMinusPiecesIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaCovers
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaFixed

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (reindexQuadraticForm
  reindexVectorEquiv minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus
  commutator_coordinateQuadMinus)
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_orthogonal_involutions_conjugate_into_semilinear_image)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Model

theorem kOmM_nonempty_mulEquiv_of_lieModel {S : Type} [Group S] {N g : ℕ} (hN : 2 ≤ N)
    (hS : LieModel S .POmegaMinus N 2 g) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ g) :
    ∃ (b c : F), (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      Nonempty (S ≃* StatedOmega (StatedQuadMinus N F b c)) := by
  obtain ⟨-, K', _, _, hK', b', c', hirr', ⟨e'⟩⟩ :=
    F4Pilot.statedClassicalModel_of_lieModel_pomega (Or.inr rfl) hS
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  let σ : K' ≃+* F := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hK'.trans hF.symm)
  have hbot : (StatedScalars (Fin (N - 1) ⊕ Fin (N - 1) ⊕ Fin 2) K').subgroupOf
      (StatedOmega (StatedQuadMinus N K' b' c')) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (coe_quadMinus N K' b' c')
      (CFSG.LieType.Universal.Spin.exists_map_ne_zero_of_hypPair _
        (CFSG.ClassicalGroups.Orthogonal.minusPair K' b' c' (⟨0, by omega⟩ : Fin (N - 1))))
  let ψ : StatedOmega (StatedQuadMinus N K' b' c') ≃*
      StatedOmega (StatedQuadMinus N F (σ b') (σ c')) :=
    ((CFSG.Adapters.RankTwoModelTransports.glCongr σ).subgroupMap _).trans
      (MulEquiv.subgroupCongr (CFSG.ClassicalInvolution.Upgrade.map_statedOmega σ
        (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp σ rfl rfl)))
  exact ⟨σ b', σ c', CFSG.ClassicalInvolution.Upgrade.irreducible_map σ hirr',
    ⟨e'.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
      (QuotientGroup.quotientBot.trans ψ))⟩⟩

theorem kOmM_hconj (k : Type) [Field k] [Finite k] {N f : ℕ} (hN : 4 ≤ N) (hf : 1 ≤ f)
    (hK : Nat.card k = 2 ^ f) {b c : k} (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    ∀ α : MulAut (matrixProjectiveDerived (reindexQuadraticForm (minusIndexEquiv N (by omega))
      (quadMinus N k b c))), α * α = 1 → ∃ β, β⁻¹ * α * β ∈
        matrixProjectiveImage (reindexQuadraticForm (minusIndexEquiv N (by omega))
          (quadMinus N k b c)) := by
  have h : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus N k b c))) .POmegaMinus
      N 2 f :=
    ⟨⟨Nat.prime_two, hf, hN⟩, k, inferInstance, inferInstance, hK, b, c, hirr,
      ⟨MulEquiv.refl _⟩⟩
  exact (even_orthogonal_involutions_conjugate_into_semilinear_image
    _ .POmegaMinus (Or.inr rfl) N f h).1 (by omega) k hK b c hirr (MulEquiv.refl _)

end Model

section Param


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_kOmMParam (hset : SeitzSetting G L) {r f : ℕ} (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (k : Fin (r + 1))
    (h : RootKindSp e t f k .omegaMinus) :
    ∃ (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
      (Φ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃* neighbourCore e k) (σ : K ≃+* K),
      (∀ g, t * ((Φ g : neighbourCore e k) : G) * t⁻¹ =
        ((Φ (kOmMBetaC K r b c g) : neighbourCore e k) : G)) ∧
      ∀ x : StatedSp r K, ((Φ (kOmMIota hr3 hirr hKc hf x) : neighbourCore e k) : G) =
        ((e.symm (complSpEquiv k (fieldSp r K σ x)) : L) : G) := by
  have htt : t * t = 1 := by rw [← _root_.sq, ← ht, pow_orderOf_eq_one]
  have hN : t ∈ normalizer (neighbourCore e k : Set G) := le_normalizer_neighbourCore e htC k
  obtain ⟨hty, hout, hfix⟩ := neighbourCore_omega_facts (m := r) hset hKc hf (by omega) e htC ht
    k rfl rfl (Or.inr rfl) h hN
  have hty' : LieModel (neighbourCore e k) .POmegaMinus (r + 1) 2 f := hty
  obtain ⟨b, c, hirr, ⟨ε₀⟩⟩ := kOmM_nonempty_mulEquiv_of_lieModel (by omega) hty' K hKc
  set π := F4Pilot.omegaProjEquiv (minusIndexEquiv (r + 1) (by omega)) (quadMinus (r + 1) K b c)
    (coe_quadMinus (r + 1) K b c) (kOmM_matrixDerivedScalars_eq_bot K r b c) with hπ
  have hreg := regular_coordinateQuadMinus (r + 1) K b c (by omega) hirr
  have hE := commutator_coordinateQuadMinus (r + 1) K b c (by omega) hirr
  have hθθ : (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ *
      (neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (neighbourCore e k : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext htt, map_one]
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comm_symmetryAut hθθ hout hfix (by omega : 1 ≤ f) hKc
    (by omega : 4 ≤ r + 1) hreg.1 hreg.2 hE (kOmM_hconj K (by omega) (by omega) hKc hirr)
    (kOmM_reindexQuadraticForm_vec K r) (ε₀.trans π)
  set Φ₀ : StatedOmega (StatedQuadMinus (r + 1) K b c) ≃* neighbourCore e k := π.trans ψ
    with hΦ₀
  have hΦ₀t : ∀ g, t * ((Φ₀ g : neighbourCore e k) : G) * t⁻¹ =
      ((Φ₀ (kOmMBetaC K r b c g) : neighbourCore e k) : G) := by
    intro g
    have h12 : ((neighbourCore e k).normalizerMonoidHom ⟨t, hN⟩) (ψ (π g)) =
        ψ (π (kOmMBetaC K r b c g)) :=
      (hψ (π g)).trans (congrArg ψ (F4Pilot.omegaProjEquiv_omegaSymmetryAut _ _ _ _ _ g).symm)
    change t * ((ψ (π g) : neighbourCore e k) : G) * t⁻¹ =
      ((ψ (π (kOmMBetaC K r b c g)) : neighbourCore e k) : G)
    rw [← h12, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hfixmap := map_fixedSubgroup_eq_of_comm (m := r) hset hKc hf (by omega) e htC ht k
    (Or.inr rfl) h Φ₀ (kOmMBetaC K r b c) hΦ₀t
  set ι := kOmMIota (k := K) hr3 hirr hKc hf with hιdef
  set κ : StatedSp r K →* G := (neighbourCore e k).subtype.comp (Φ₀.toMonoidHom.comp ι) with hκdef
  have hκinj : Function.Injective κ := (neighbourCore e k).subtype_injective.comp
    (Φ₀.injective.comp (kOmMIota_injective hr3 hirr hKc hf))
  have hκr : κ.range = modelToG e (complSp K k) := by
    rw [hκdef, MonoidHom.range_comp, MonoidHom.range_comp, hιdef, range_kOmMIota, hfixmap]
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
  have hιs : kOmMBetaC K r b c (ι s) = ι s := by
    have hmem : ι s ∈ fixedSubgroup (kOmMBetaC K r b c) := by
      rw [hιdef, ← range_kOmMIota hr3 hirr hKc hf]
      exact ⟨s, rfl⟩
    exact hmem
  refine ⟨b, c, hirr, (MulAut.conj (ι s)).trans Φ₀, σ₀⁻¹, fun g => ?_, fun x => ?_⟩
  · change t * ((Φ₀ (ι s * g * (ι s)⁻¹) : neighbourCore e k) : G) * t⁻¹ =
      ((Φ₀ (ι s * kOmMBetaC K r b c g * (ι s)⁻¹) : neighbourCore e k) : G)
    have h2 : kOmMBetaC K r b c (ι s * g * (ι s)⁻¹) = ι s * kOmMBetaC K r b c g * (ι s)⁻¹ := by
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
