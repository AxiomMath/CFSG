module

public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.LieType.Universal.SpecialLinearExtras

public section

namespace CFSG.LieType.SpecialLinear

open CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
open scoped commutatorElement Pointwise

variable {K : Type*} [Group K]

@[expose] def negUnipotentExcept (D : UniversalRootDatum K) (i : Fin D.rank) : Subgroup K :=
  ⨆ γ ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).negExcept i, D.rootGroup γ

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem rootGroup_le_negUnipotentExcept {i : Fin D.rank} {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ (Φ).negExcept i) : D.rootGroup γ ≤ negUnipotentExcept D i :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ (Φ).negExcept i) => D.rootGroup γ) γ hγ le_rfl

theorem negUnipotentExcept_le_negUnipotent (i : Fin D.rank) :
    negUnipotentExcept D i ≤ negUnipotent D :=
  iSup₂_le fun _ hγ => rootGroup_le_negUnipotent hγ.1.1 hγ.1.2

theorem negUnipotent_eq_sup (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    negUnipotent D = negUnipotentExcept D i ⊔ D.rootGroup (-Pi.single i 1) := by
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    by_cases h1 : γ = -Pi.single i 1
    · subst h1
      exact le_sup_right
    by_cases h2 : γ = -(2 • (Pi.single i 1 : Fin D.rank → ℤ))
    · subst h2
      have hmem : -((2 : ℕ) • (Pi.single i 1 : Fin D.rank → ℤ)) =
          ((2 : ℕ) • (-(Pi.single i 1 : Fin D.rank → ℤ))) := by
        rw [smul_neg]
      rw [hmem] at hγ ⊢
      exact (hext.two_smul_le (-Pi.single i 1) ((Φ).neg_mem _ ((Φ).single_mem i)) hγ.1).trans
        le_sup_right
    refine le_sup_of_le_left (rootGroup_le_negUnipotentExcept ⟨hγ, ?_⟩)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  · exact sup_le (negUnipotentExcept_le_negUnipotent i)
      (rootGroup_le_negUnipotent ((Φ).neg_mem _ ((Φ).single_mem i)) (by
        rw [ht_neg, ht_single]; norm_num))

theorem rootGroup_single_le_normalizer_negExcept (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    D.rootGroup (Pi.single i 1) ≤
      Subgroup.normalizer (negUnipotentExcept D i : Set K) :=
  le_normalizer_iSup₂ fun x hx γ hγ y hy => by
    have hc := hext.commutator_mem _ ((Φ).single_mem i) γ hγ.1.1
      ((Φ).linIndepPair_of_mem_negExcept (Or.inl rfl) hγ) x hx y hy
    have hle : ⨆ ε ∈ openCone D.roots (Pi.single i 1) γ, D.rootGroup ε ≤
        negUnipotentExcept D i := iSup₂_le fun _ hε =>
      rootGroup_le_negUnipotentExcept ((Φ).openCone_subset_negExcept (Or.inl rfl) hγ hε)
    have h : ⁅x, y⁆ * y ∈ negUnipotentExcept D i :=
      mul_mem (hle hc) (rootGroup_le_negUnipotentExcept hγ hy)
    rwa [commutatorElement_def, inv_mul_cancel_right] at h

theorem rootGroup_neg_single_le_normalizer_negExcept (hext : SteinbergExtras D n H)
    (i : Fin D.rank) :
    D.rootGroup (-Pi.single i 1) ≤
      Subgroup.normalizer (negUnipotentExcept D i : Set K) :=
  le_normalizer_iSup₂ fun x hx γ hγ y hy => by
    have hc := hext.commutator_mem _ ((Φ).neg_mem _ ((Φ).single_mem i)) γ hγ.1.1
      ((Φ).linIndepPair_of_mem_negExcept (Or.inr rfl) hγ) x hx y hy
    have hle : ⨆ ε ∈ openCone D.roots (-Pi.single i 1) γ, D.rootGroup ε ≤
        negUnipotentExcept D i := iSup₂_le fun _ hε =>
      rootGroup_le_negUnipotentExcept ((Φ).openCone_subset_negExcept (Or.inr rfl) hγ hε)
    have h : ⁅x, y⁆ * y ∈ negUnipotentExcept D i :=
      mul_mem (hle hc) (rootGroup_le_negUnipotentExcept hγ hy)
    rwa [commutatorElement_def, inv_mul_cancel_right] at h

theorem conj_n_mem_negUnipotentExcept
    (hct : IsCTGroupDatum (RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (i : Fin D.rank) {u : K} (hu : u ∈ negUnipotentExcept D i) :
    n i * u * (n i)⁻¹ ∈ negUnipotentExcept D i :=
  conj_mem_of_forall_mem (P := (Φ).negExcept i) (X := D.rootGroup) (fun γ hγ y hy => by
    have h := (actsAs_n hct i).conj_mem hγ.1.1 hy
    rw [weylAction_simple] at h
    exact rootGroup_le_negUnipotentExcept ((Φ).refl_mem_negExcept hγ) h) hu

end CFSG.LieType.SpecialLinear
