module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCommutantConjugation

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {K V F : Type*} [Field K] [AddCommGroup V] [Module K V] [Group F]

theorem map_mem_normalizer_zpowers (rho : F →* LinearMap.GeneralLinearGroup K V)
    (g n : F) (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers g : Set F)) :
    rho n ∈ Subgroup.normalizer (Subgroup.zpowers (rho g) :
      Set (LinearMap.GeneralLinearGroup K V)) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  rw [MonoidHom.map_zpowers] at h
  have hmap := congrArg (Subgroup.map rho) h
  simp only [MonoidHom.map_zpowers] at hmap
  change Subgroup.zpowers (rho (n * g * n⁻¹)) = Subgroup.zpowers (rho g) at hmap
  change Subgroup.zpowers (rho n * rho g * (rho n)⁻¹) = Subgroup.zpowers (rho g)
  simpa only [map_mul, map_inv] using hmap

@[expose] def cyclicNormalizerCommutantAction
    (rho : F →* LinearMap.GeneralLinearGroup K V) (g : F) :
    Subgroup.normalizer (Subgroup.zpowers g : Set F) →*
      (rationalCommutant (rho g : Module.End K V) ≃ₐ[K]
        rationalCommutant (rho g : Module.End K V)) :=
  invariantSubalgebraAction
    (endomorphismConjugation.comp (rho.comp
      (Subgroup.normalizer (Subgroup.zpowers g : Set F)).subtype))
    (rationalCommutant (rho g : Module.End K V))
    (fun n S hS => normalizer_preserves_rationalCommutant (rho g)
      ⟨rho n.val, map_mem_normalizer_zpowers rho g n.val n.property⟩ S hS)

theorem cyclicNormalizerCommutantAction_mem_ker_iff
    (rho : F →* LinearMap.GeneralLinearGroup K V) (hrho : Function.Injective rho)
    (g : F) (hfield : IsField (rationalCommutant (rho g : Module.End K V)))
    (n : Subgroup.normalizer (Subgroup.zpowers g : Set F)) :
    n ∈ (cyclicNormalizerCommutantAction rho g).ker ↔
      n.val ∈ Subgroup.centralizer ({g} : Set F) := by
  change cyclicNormalizerCommutantAction rho g n = 1 ↔ _
  constructor
  · intro hn
    have hgg : (rho g : Module.End K V) ∈ rationalCommutant (rho g : Module.End K V) :=
      (mem_rationalCommutant_iff _ _).mpr rfl
    have hfix := congrArg (fun e : rationalCommutant (rho g : Module.End K V) ≃ₐ[K]
        rationalCommutant (rho g : Module.End K V) =>
          (e ⟨rho g, hgg⟩ : Module.End K V)) hn
    have h := (endomorphismConjugation_eq_self_iff (rho n.val)
      (rho g : Module.End K V)).mp hfix
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply hrho
    rw [map_mul, map_mul]
    apply Units.ext
    exact h
  · intro hn
    apply AlgEquiv.ext
    intro S
    apply Subtype.ext
    change endomorphismConjugation (rho n.val) S.val = S.val
    have hcomm := congrArg (fun x : F => (rho x : Module.End K V))
      (Subgroup.mem_centralizer_singleton_iff.mp hn)
    have hnS : (rho n.val : Module.End K V) ∈ rationalCommutant (rho g : Module.End K V) :=
      (mem_rationalCommutant_iff _ _).mpr (by
        simpa only [map_mul, Units.val_mul] using hcomm.symm)
    apply (endomorphismConjugation_eq_self_iff (rho n.val) S.val).mpr
    exact congrArg Subtype.val
      (hfield.mul_comm (⟨rho n.val, hnS⟩ : rationalCommutant (rho g : Module.End K V))
        S)

theorem cyclicNormalizerCommutantAction_ker_eq
    (rho : F →* LinearMap.GeneralLinearGroup K V) (hrho : Function.Injective rho)
    (g : F) (hfield : IsField (rationalCommutant (rho g : Module.End K V))) :
    (cyclicNormalizerCommutantAction rho g).ker =
      (Subgroup.centralizer ({g} : Set F)).subgroupOf
        (Subgroup.normalizer (Subgroup.zpowers g : Set F)) := by
  ext n
  exact cyclicNormalizerCommutantAction_mem_ker_iff rho hrho g hfield n

theorem cyclic_normalizer_centralizer_index_dvd_four
    [Finite K] [FiniteDimensional K V] [Nontrivial V]
    (rho : F →* LinearMap.GeneralLinearGroup K V) (hrho : Function.Injective rho)
    (g : F)
    (hirr : ∀ U : Submodule K V,
      (∀ v ∈ U, (rho g : Module.End K V) v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hdim : Module.finrank K V = 4) :
    (Subgroup.centralizer ({g} : Set F)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers g : Set F)) ∣ 4 := by
  rw [Subgroup.relIndex, ← cyclicNormalizerCommutantAction_ker_eq rho hrho g
    (rationalCommutant_isField (rho g : Module.End K V) hirr)]
  exact rationalCommutant_normalizer_kernel_index_dvd_four
    (rho.comp (Subgroup.normalizer (Subgroup.zpowers g : Set F)).subtype)
    (rho g : Module.End K V) hirr hdim
    (fun n S hS => normalizer_preserves_rationalCommutant (rho g)
      ⟨rho n.val, map_mem_normalizer_zpowers rho g n.val n.property⟩ S hS)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
