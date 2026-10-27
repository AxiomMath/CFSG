module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Relabel

public noncomputable section

open CategoryTheory WithConv

namespace CFSG.LieType.AlgebraicGroups

universe u

abbrev PermutationTorus (k : Type u) (ι : Type u) [Field k] [Finite ι] :=
  TauCeti.FiniteTypeCommHopfAlgCat.of k
    (MonoidAlgebra k (Multiplicative (ι →₀ ℤ)))

variable {k : Type u} [Field k] {ι : Type u} [Finite ι]

private theorem recoveredCharacterMap_eq
    (π : Equiv.Perm ι)
    (σ : PermutationTorus k ι →ₐc[k] PermutationTorus k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    MonoidAlgebra.mapDomainOfBialgHom σ =
      (TauCeti.SplitTorus.characterRelabel π : Multiplicative (ι →₀ ℤ) →* _) := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨f, rfl⟩ := Multiplicative.ofAdd.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ =>
      simp only [ofAdd_add, map_mul, h₁, h₂]
  | single i n =>
      change MonoidAlgebra.mapDomainOfBialgHom σ
          (Multiplicative.ofAdd (Finsupp.single i n)) =
        TauCeti.SplitTorus.characterRelabel π (Multiplicative.ofAdd (Finsupp.single i n))
      have hgen : MonoidAlgebra.mapDomainOfBialgHom σ
            (Multiplicative.ofAdd (Finsupp.single i 1)) =
          Multiplicative.ofAdd (Finsupp.single (π i) 1) := by
        apply MonoidAlgebra.single_left_injective (R := k) one_ne_zero
        change MonoidAlgebra.single
            ((MonoidAlgebra.mapDomainOfBialgHom σ)
              (Multiplicative.ofAdd (Finsupp.single i 1))) 1 =
          MonoidAlgebra.single
            (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1
        rw [MonoidAlgebra.single_mapDomainOfBialgHom, hσ i]
      rw [TauCeti.SplitTorus.characterRelabel_ofAdd, Finsupp.equivMapDomain_single,
        show Finsupp.single i n = n • Finsupp.single i 1 by simp, ofAdd_zsmul,
        show Finsupp.single (π i) n = n • Finsupp.single (π i) 1 by simp, ofAdd_zsmul,
        map_zpow, hgen]


theorem eq_mapDomainBialgHom_characterRelabel
    (π : Equiv.Perm ι)
    (σ : PermutationTorus k ι →ₐc[k] PermutationTorus k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    σ = MonoidAlgebra.mapDomainBialgHom k
      (TauCeti.SplitTorus.characterRelabel π) := by
  rw [← MonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom (R := k) σ,
    recoveredCharacterMap_eq π σ hσ]

theorem bijective_permutationTorusAut
    (π : Equiv.Perm ι)
    (σ : PermutationTorus k ι →ₐc[k] PermutationTorus k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    Function.Bijective σ := by
  have hσ_eq := eq_mapDomainBialgHom_characterRelabel π σ hσ
  let τ : PermutationTorus k ι →ₐc[k] PermutationTorus k ι :=
    MonoidAlgebra.mapDomainBialgHom k (TauCeti.SplitTorus.characterRelabel π⁻¹)
  have hleft : Function.LeftInverse τ σ := by
    intro x
    have h : τ.comp σ = BialgHom.id k (PermutationTorus k ι) := by
      dsimp only [τ]
      rw [hσ_eq, ← MonoidAlgebra.mapDomainBialgHom_comp,
        TauCeti.SplitTorus.characterRelabel_comp, inv_mul_cancel,
        TauCeti.SplitTorus.characterRelabel_one, MonoidAlgebra.mapDomainBialgHom_id]
    exact congrArg (fun f : PermutationTorus k ι →ₐc[k] PermutationTorus k ι => f x) h
  have hright : Function.RightInverse τ σ := by
    intro x
    have h : σ.comp τ = BialgHom.id k (PermutationTorus k ι) := by
      dsimp only [τ]
      rw [hσ_eq, ← MonoidAlgebra.mapDomainBialgHom_comp,
        TauCeti.SplitTorus.characterRelabel_comp, mul_inv_cancel,
        TauCeti.SplitTorus.characterRelabel_one, MonoidAlgebra.mapDomainBialgHom_id]
    exact congrArg (fun f : PermutationTorus k ι →ₐc[k] PermutationTorus k ι => f x) h
  exact ⟨hleft.injective, hright.surjective⟩

noncomputable def permutationTorusBialgEquiv
    (π : Equiv.Perm ι)
    (σ : PermutationTorus k ι →ₐc[k] PermutationTorus k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    PermutationTorus k ι ≃ₐc[k] PermutationTorus k ι :=
  BialgEquiv.ofBijective σ (bijective_permutationTorusAut π σ hσ)

theorem permutationTorusBialgEquiv_coe
    (π : Equiv.Perm ι)
    (σ : PermutationTorus k ι →ₐc[k] PermutationTorus k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    (permutationTorusBialgEquiv π σ hσ : PermutationTorus k ι →ₐc[k] PermutationTorus k ι) =
      σ := by
  exact BialgHom.ext fun x =>
    BialgEquiv.ofBijective_apply σ (bijective_permutationTorusAut π σ hσ) x

theorem bijective_mapDomain_permutationTorusAut
    (π : Equiv.Perm ι)
    (σ : PermutationTorus k ι →ₐc[k] PermutationTorus k ι)
    (hσ : ∀ i : ι,
      σ (MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single i 1)) 1) =
        MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (π i) 1)) 1) :
    Function.Bijective (TauCeti.AlgHom.mapDomain (A := k) σ) := by
  let e := permutationTorusBialgEquiv π σ hσ
  have he : (e : PermutationTorus k ι →ₐc[k] PermutationTorus k ι) = σ :=
    permutationTorusBialgEquiv_coe π σ hσ
  have h := (TauCeti.AlgHom.mapDomainMulEquiv (A := k) e).bijective
  have hfun : ((TauCeti.AlgHom.mapDomainMulEquiv (A := k) e :
      WithConv (PermutationTorus k ι →ₐ[k] k) ≃*
        WithConv (PermutationTorus k ι →ₐ[k] k)) :
      WithConv (PermutationTorus k ι →ₐ[k] k) →
        WithConv (PermutationTorus k ι →ₐ[k] k)) =
      TauCeti.AlgHom.mapDomain (A := k) σ := by
    funext x
    rw [TauCeti.AlgHom.mapDomainMulEquiv_apply, he]
  rwa [hfun] at h

end CFSG.LieType.AlgebraicGroups
