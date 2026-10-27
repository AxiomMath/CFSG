module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFieldNormalizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem endomorphismConjugation_eq_self_iff
    (g : LinearMap.GeneralLinearGroup K V) (S : Module.End K V) :
    endomorphismConjugation g S = S ↔
      (g : Module.End K V) * S = S * (g : Module.End K V) := by
  let e := endomorphismConjugation g
  have he : e S = (g : Module.End K V) * S * (g⁻¹ : LinearMap.GeneralLinearGroup K V) := rfl
  rw [he]
  constructor
  · intro h
    have h' := congrArg (fun R : Module.End K V => R * (g : Module.End K V)) h
    simpa only [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one] using h'
  · intro h
    rw [h, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

theorem rationalCommutant_eq_of_zpowers_eq
    (g h : LinearMap.GeneralLinearGroup K V)
    (hcyclic : Subgroup.zpowers g = Subgroup.zpowers h) :
    rationalCommutant (g : Module.End K V) = rationalCommutant (h : Module.End K V) := by
  have fixesPower (a : LinearMap.GeneralLinearGroup K V) (S : Module.End K V)
      (hS : endomorphismConjugation a S = S) (n : ℤ) :
      endomorphismConjugation (a ^ n) S = S := by
    let Stab : Subgroup (LinearMap.GeneralLinearGroup K V) :=
      (MulAction.stabilizer (Module.End K V ≃ₐ[K] Module.End K V) S).comap
        endomorphismConjugation
    exact Stab.zpow_mem hS n
  ext S
  rw [mem_rationalCommutant_iff, mem_rationalCommutant_iff,
    ← endomorphismConjugation_eq_self_iff, ← endomorphismConjugation_eq_self_iff]
  constructor
  · intro hS
    have hh : h ∈ Subgroup.zpowers g := hcyclic.symm ▸ Subgroup.mem_zpowers h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hn]
    exact fixesPower g S hS n
  · intro hS
    have hg : g ∈ Subgroup.zpowers h := hcyclic ▸ Subgroup.mem_zpowers g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← hn]
    exact fixesPower h S hS n

theorem normalizer_preserves_rationalCommutant
    (g : LinearMap.GeneralLinearGroup K V)
    (n : Subgroup.normalizer (Subgroup.zpowers g : Set (LinearMap.GeneralLinearGroup K V)))
    (S : Module.End K V) (hS : S ∈ rationalCommutant (g : Module.End K V)) :
    endomorphismConjugation n.val S ∈ rationalCommutant (g : Module.End K V) := by
  let c : LinearMap.GeneralLinearGroup K V := (MulAut.conj n.val) g
  have hcyclic : Subgroup.zpowers c = Subgroup.zpowers g := by
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp n.property
    rw [MonoidHom.map_zpowers] at h
    exact h
  rw [← rationalCommutant_eq_of_zpowers_eq c g hcyclic, mem_rationalCommutant_iff]
  have hcomm := (mem_rationalCommutant_iff (g : Module.End K V) S).mp hS
  have h := congrArg (endomorphismConjugation n.val) hcomm
  have hc : endomorphismConjugation n.val (g : Module.End K V) =
      (c : Module.End K V) := rfl
  simpa only [map_mul, hc] using h

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
