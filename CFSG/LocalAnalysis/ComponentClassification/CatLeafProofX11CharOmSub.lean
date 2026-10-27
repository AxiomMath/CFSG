module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCReduce
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Corr

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X11Char

open CFSG Subgroup Module
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8

attribute [local instance] finite_linearEquiv

variable {H : Type} [Group H] [Finite H] {G : Subgroup H} [G.Normal] {K : Type} [Field K]
  [Finite K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {Θ : G ≃* projectiveDerived Q} {t : H} {U U' : Submodule K V}

@[expose] def rightFactor (A : V ≃ₗ[K] V)
    (ψ : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)) :
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype) →*
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  (orthogonalOperatorCentralizer Q A.toLinearMap).subtype.comp
    (ψ.symm.toMonoidHom.comp (MonoidHom.inr _ _))

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem rightFactor_apply (A : V ≃ₗ[K] V)
    (ψ : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)) (h) :
    rightFactor A ψ h = (ψ.symm (1, h)).val := rfl

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem rightFactor_injective (A : V ≃ₗ[K] V)
    (ψ : orthogonalOperatorCentralizer Q A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)) :
    Function.Injective (rightFactor A ψ) := fun x y h => by
  have h1 := ψ.symm.injective (Subtype.ext h)
  exact congrArg Prod.snd h1

@[expose] def rightFN (D : InvData G Q Θ t)
    (ψ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype)) :
    (orthogonalDerived Q).comap (rightFactor D.A ψ) →* FN D :=
  (((rightFactor D.A ψ).comp ((orthogonalDerived Q).comap (rightFactor D.A ψ)).subtype).codRestrict
    (fixedSubgroup (similarityConjugation Q D.A D.μ D.hsim)) fun z => by
      rw [fixed_similarityConjugation_eq]
      exact (ψ.symm (1, z.val)).property).codRestrict _ fun z => mem_subgroupOf.mpr z.property

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem rightFN_val (D : InvData G Q Θ t)
    (ψ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (z : (orthogonalDerived Q).comap (rightFactor D.A ψ)) :
    (rightFN D ψ z).val.val = (ψ.symm (1, z.val)).val := rfl

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem epsT_rightFN (D : InvData G Q Θ t)
    (ψ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (z : (orthogonalDerived Q).comap (rightFactor D.A ψ)) :
    epsT D ψ (rightFN D ψ z) = (1, z.val) := by
  have e1 : (fixedCentralizerEquiv Q D.A D.μ D.hsim) (rightFN D ψ z).val = ψ.symm (1, z.val) :=
    Subtype.ext rfl
  change ψ ((fixedCentralizerEquiv Q D.A D.μ D.hsim) (rightFN D ψ z).val) = _
  rw [e1, MulEquiv.apply_symm_apply]

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem toHD_rightFN_injective (D : InvData G Q Θ t)
    (ψ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (hψ : ∀ h (x : U) (y : U'), (ψ.symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val) (h2 : (2 : K) ≠ 0) (hU : ∃ u : U, u ≠ 0) :
    Function.Injective ((toHD D).comp (rightFN D ψ)) := by
  obtain ⟨u, hu⟩ := hU
  rw [injective_iff_map_eq_one]
  intro z hz
  have h1 := (toH_eq_one_iff G Q Θ t D.A D.μ D.hsim D.hconj (rightFN D ψ z)).mp hz
  rw [rightFN_val, mem_scalarSigns_iff] at h1
  rcases h1 with h1 | h1
  · refine Subtype.ext (rightFactor_injective D.A ψ ?_)
    rw [rightFactor_apply, h1]
    exact (map_one (rightFactor D.A ψ)).symm
  · exfalso
    have e1 := hψ (1, z.val) u 0
    rw [h1] at e1
    simp only [QuadraticMap.coe_negOrthogonal, LinearEquiv.neg_apply, Submodule.coe_zero,
      add_zero, map_zero, OneMemClass.coe_one] at e1
    have e2 : -(u : V) = u := e1
    have e3 : (2 : K) • (u : V) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← e2]
      exact neg_add_cancel _
    exact hu (Subtype.ext ((smul_eq_zero.mp e3).resolve_left h2))

omit [Finite H] [Finite K] [FiniteDimensional K V] in
theorem commute_rightFN (D : InvData G Q Θ t)
    (ψ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (M : Subgroup (FN D)) (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)))
    (hML : M.map (epsT D ψ) = L.prod ⊥) (z : (orthogonalDerived Q).comap (rightFactor D.A ψ))
    {m : FN D} (hm : m ∈ M) : rightFN D ψ z * m = m * rightFN D ψ z := by
  have hm2 : (epsT D ψ m).2 = 1 := by
    have h1 : epsT D ψ m ∈ L.prod ⊥ := hML ▸ mem_map_of_mem _ hm
    exact mem_bot.mp (mem_prod.mp h1).2
  apply epsT_injective D ψ
  rw [map_mul, map_mul, epsT_rightFN]
  refine Prod.ext ?_ ?_
  · change 1 * (epsT D ψ m).1 = (epsT D ψ m).1 * 1
    rw [one_mul, mul_one]
  · change z.val * (epsT D ψ m).2 = (epsT D ψ m).2 * z.val
    rw [hm2, one_mul, mul_one]

omit [Finite H] in
theorem exists_twoSubgroup_of_left (D : InvData G Q Θ t)
    (ψ : orthogonalOperatorCentralizer Q D.A.toLinearMap ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp U'.subtype))
    (hψ : ∀ h (x : U) (y : U'), (ψ.symm h).val.val (x.val + y.val) =
      (h.1.val x).val + (h.2.val y).val) (h2 : (2 : K) ≠ 0) (hU : ∃ u : U, u ≠ 0)
    (M : Subgroup (FN D)) (L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)))
    (hML : M.map (epsT D ψ) = L.prod ⊥) {n : ℕ}
    (hdvd : 2 ^ n ∣ Nat.card ((orthogonalDerived Q).comap (rightFactor D.A ψ))) :
    ∃ R : Subgroup H, Nat.card R = 2 ^ n ∧
      R ≤ centralizer ({t} : Set H) ⊓ UnbalancedLayer.coreActionKernel (M.map (toHD D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨P.map ((toHD D).comp (rightFN D ψ)), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (toHD_rightFN_injective D ψ hψ h2 hU), hP]
  rintro _ ⟨z, -, rfl⟩
  refine ⟨toH_mem_centralizer G Q Θ t D.A D.μ D.hsim D.hconj (rightFN D ψ z), ?_⟩
  apply CatFactsSp4.mem_coreActionKernel_of_commute
  rintro _ ⟨m, hm, rfl⟩
  change toHD D (rightFN D ψ z) * toHD D m = toHD D m * toHD D (rightFN D ψ z)
  rw [← map_mul, ← map_mul, commute_rightFN D ψ M L hML z hm]

end CFSG.ComponentClassification.CatLeafProof.X11Char
