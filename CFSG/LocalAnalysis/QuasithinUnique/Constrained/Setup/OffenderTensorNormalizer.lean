module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensor
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open TensorProduct Module

variable {F : Type*} [Field F]

variable {U : Type*} [AddCommGroup U] [Module F U] {s : ℕ}

theorem full_matrix_tensor_factor_normalizer [Module.Finite F U]
    (hd : 2 ≤ finrank F U) (hs : 2 ≤ s) (π : Equiv.Perm (Fin s))
    (b : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U)
    (hb : ∀ i : Fin s, (factorAlg (F := F) (V := fun _ : Fin s => U) i).map
      (b.conjAlgEquiv F).toAlgHom = factorAlg (π i)) :
    ∃ g : Fin s → (U ≃ₗ[F] U),
      b = (PiTensorProduct.reindex F (fun _ : Fin s => U) π).trans (PiTensorProduct.congr g) := by
  classical
  have : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (M := U) (by omega)
  obtain ⟨P, hP⟩ : ∃ P : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U,
      P = PiTensorProduct.reindex F (fun _ : Fin s => U) π := ⟨_, rfl⟩
  have hPfe : ∀ i (g : Module.End F U) x, P (factorEnd i g x) = factorEnd (π i) g (P x) := by
    intro i g x
    rw [hP]
    exact reindex_factorEnd π i g x
  have hPinv : ∀ j (g : Module.End F U) x,
      P.symm (factorEnd j g x) = factorEnd (π.symm j) g (P.symm x) := by
    intro j g x
    have h1 := hPfe (π.symm j) g (P.symm x)
    rw [Equiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    rw [← h1]
    simp
  have hbj : ∀ j, (factorAlg (F := F) (V := fun _ : Fin s => U) (π.symm j)).map
      (b.conjAlgEquiv F).toAlgHom = factorAlg j := fun j => by
    rw [hb, Equiv.apply_symm_apply]
  have hinj : ∀ j, Function.Injective
      (factorAlgHom (F := F) (V := fun _ : Fin s => U) j) := fun j => factorAlgHom_injective j
  have hβ : ∀ j, ∃ β : Module.End F U ≃ₐ[F] Module.End F U, ∀ g,
      factorEnd j (β g) = b.conjAlgEquiv F (factorEnd (π.symm j) g) := by
    intro j
    refine ⟨(AlgEquiv.ofInjective (factorAlgHom (F := F) (V := fun _ : Fin s => U) (π.symm j))
        (hinj _)).trans (((b.conjAlgEquiv F).subalgebraMap
          (factorAlg (F := F) (V := fun _ : Fin s => U) (π.symm j))).trans
          ((Subalgebra.equivOfEq _ _ (hbj j)).trans
            (AlgEquiv.ofInjective (factorAlgHom (F := F) (V := fun _ : Fin s => U) j)
              (hinj _)).symm)), fun g => ?_⟩
    simp [← factorAlgHom_apply, AlgEquiv.trans_apply]
    exact congrArg Subtype.val
      ((AlgEquiv.ofInjective (factorAlgHom (F := F) (V := fun _ : Fin s => U) j)
        (hinj j)).apply_symm_apply _)
  choose β hβ using hβ
  choose g hg using fun j => AlgEquiv.eq_linearEquivConjAlgEquiv (β j)
  obtain ⟨c, hc⟩ : ∃ c : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U, c = P.symm.trans b :=
    ⟨_, rfl⟩
  have hcφ : ∀ j f x, c (factorEnd j f x) = factorEnd j (β j f) (c x) := by
    intro j f x
    have h2 := congrArg (fun T => T (b (P.symm x))) (hβ j f)
    simp only [LinearEquiv.conjAlgEquiv_apply] at h2
    simp at h2
    rw [hc]
    show b (P.symm (factorEnd j f x)) = factorEnd j (β j f) (b (P.symm x))
    rw [hPinv, h2]
  obtain ⟨G, hGdef⟩ : ∃ G : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U,
      G = PiTensorProduct.congr g := ⟨_, rfl⟩
  have hβg : ∀ j f, β j f = ((g j : U ≃ₗ[F] U) : Module.End F U) * f *
      (((g j).symm : U ≃ₗ[F] U) : Module.End F U) := by
    intro j f
    rw [hg j]
    rfl
  have hGinv : ∀ j f y, G.symm (factorEnd j (((g j : U ≃ₗ[F] U) : Module.End F U) * f *
      (((g j).symm : U ≃ₗ[F] U) : Module.End F U)) y) = factorEnd j f (G.symm y) := by
    intro j f y
    have := congr_factorEnd g j f (G.symm y)
    rw [← hGdef, LinearEquiv.apply_symm_apply] at this
    rw [← this]
    simp
  obtain ⟨c', hc'⟩ : ∃ c' : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U,
      c' = c.trans G.symm := ⟨_, rfl⟩
  have hc'comm : ∀ j f, (c' : Module.End F (⨂[F] _ : Fin s, U)) * factorEnd j f =
      factorEnd j f * (c' : Module.End F (⨂[F] _ : Fin s, U)) := by
    intro j f
    refine LinearMap.ext fun x => ?_
    show c' (factorEnd j f x) = factorEnd j f (c' x)
    rw [hc']
    show G.symm (c (factorEnd j f x)) = factorEnd j f (G.symm (c x))
    rw [hcφ, hβg, hGinv]
  obtain ⟨a, ha⟩ := exists_smul_one_of_commute_factorEnd _ hc'comm
  have hca : ∀ y, c' y = a • y := fun y => by
    have := congrArg (fun T => T y) ha
    simpa using this
  have ha0 : a ≠ 0 := by
    intro h0
    obtain ⟨e, he⟩ := exists_ne (0 : U)
    have ht : PiTensorProduct.tprod F (fun _ : Fin s => e) ≠ 0 :=
      tprod_ne_zero_of_ne_zero (fun _ => he)
    apply ht
    apply c'.injective
    rw [hca, h0, zero_smul, map_zero]
  have hs0 : 0 < s := by omega
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin s, i₀ = ⟨0, hs0⟩ := ⟨_, rfl⟩
  obtain ⟨g', hg'⟩ : ∃ g' : Fin s → (U ≃ₗ[F] U),
      g' = Function.update g i₀ ((LinearEquiv.smulOfNeZero F U a ha0).trans (g i₀)) := ⟨_, rfl⟩
  have hGg' : ∀ y, PiTensorProduct.congr g' y = a • G y := by
    intro y
    rw [congr_eq_map, hGdef, congr_eq_map]
    have hfun : (fun i => ((g' i : U ≃ₗ[F] U) : Module.End F U)) =
        Function.update (fun i => ((g i : U ≃ₗ[F] U) : Module.End F U)) i₀
          (a • ((g i₀ : U ≃ₗ[F] U) : Module.End F U)) := by
      funext i
      by_cases hi : i = i₀
      · subst hi
        rw [hg']
        simp only [Function.update_self]
        ext u
        simp
      · rw [hg', Function.update_of_ne hi, Function.update_of_ne hi]
    rw [hfun, PiTensorProduct.map_update_smul, Function.update_eq_self]
    rfl
  refine ⟨g', ?_⟩
  refine LinearEquiv.ext fun x => ?_
  have h1 : c (P x) = b x := by rw [hc]; simp
  have h2 : ∀ y, c y = a • G y := by
    intro y
    have h3 : G.symm (c y) = a • y := by
      have := hca y
      rw [hc'] at this
      exact this
    calc c y = G (G.symm (c y)) := (G.apply_symm_apply _).symm
      _ = G (a • y) := by rw [h3]
      _ = a • G y := map_smul _ _ _
  rw [LinearEquiv.trans_apply, ← hP, hGg', ← h2 (P x)]
  exact h1.symm

end CFSG.QuasithinUnique.Setup.Offender
