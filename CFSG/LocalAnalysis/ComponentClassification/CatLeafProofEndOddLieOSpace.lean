module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLowDimensionFrontiers
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddO

open Subgroup Module QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalLowDimensionFrontiers

variable {K : Type} [Field K]

section Small

variable [Finite K] {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem exists_quasisimple_or_three (hodd : Odd (Nat.card K)) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (h3 : 3 ≤ finrank K W) :
    (∃ L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q), CFSG.IsQuasisimple L) ∨
      (Nat.card K = 3 ∧ finrank K W ≤ 4) := by
  by_cases hq : Nat.card K = 3
  · by_cases h4 : finrank K W ≤ 4
    · exact Or.inr ⟨hq, h4⟩
    · exact Or.inl ⟨_, OddSelector.commutator_orthogonalGroup_quasisimple hodd Q hQ (by omega)⟩
  · left
    rcases (show finrank K W = 3 ∨ finrank K W = 4 ∨ 5 ≤ finrank K W by omega) with h | h | h
    · obtain ⟨-, -, -, -, -, -, hq', -⟩ :=
        LocalAnalysis.ComponentInitial.orthogonal_three_derived hodd hq Q hQ h
      exact ⟨_, hq'⟩
    · by_cases hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
      · have hK2 : Nat.card K ≠ 2 := fun h2 => by
          rw [h2] at hodd
          exact absurd hodd (by decide)
        obtain ⟨-, e, -, -, -, hL, -⟩ :=
          LocalAnalysis.ComponentInitial.orthogonal_split_four_derived hK2 hq Q hQ h hS
        exact ⟨_, hL⟩
      · obtain ⟨-, -, -, -, -, -, -, -, hq', -⟩ :=
          LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hodd Q hQ h hS
        exact ⟨_, hq'⟩
    · exact ⟨_, OddSelector.commutator_orthogonalGroup_quasisimple hodd Q hQ h⟩

theorem eq_commutator_of_three (hodd : Odd (Nat.card K)) (hq : Nat.card K = 3)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (h3 : 3 ≤ finrank K W)
    (h4 : finrank K W ≤ 4) {L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hL : CFSG.IsComponent L) :
    finrank K W = 4 ∧ L = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rcases (show finrank K W = 3 ∨ finrank K W = 4 by omega) with h | h
  · exfalso
    have hsol := ((orthogonal_three_p_components_frontier hodd Q hQ h).2 hq).1
    exact LocalAnalysis.ComponentInitial.not_isComponent_of_isSolvable _ hL
  · refine ⟨h, ?_⟩
    by_cases hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    · exfalso
      have hsol := ((orthogonal_four_split_p_components_frontier hodd Q hQ h hS).2 hq).1
      exact LocalAnalysis.ComponentInitial.not_isComponent_of_isSolvable _ hL
    · obtain ⟨-, -, -, -, -, -, -, -, hq', -⟩ :=
        LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hodd Q hQ h hS
      exact LocalAnalysis.ComponentInitial.eq_commutator_of_isComponent hL hq'

end Small

section Blocks

variable {V : Type} [AddCommGroup V] [Module K V] {M F : Submodule K V}

theorem commute_of_blocks (hMF : IsCompl M F) {g h : V ≃ₗ[K] V}
    (hgM : ∀ m ∈ M, g m = m) (hgF : ∀ f ∈ F, g f ∈ F)
    (hhF : ∀ f ∈ F, h f = f) (hhM : ∀ m ∈ M, h m ∈ M) : g * h = h * g := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨m, f, rfl⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hMF v
  have e1 : g (h ((m : V) + f)) = h m + g f := by
    rw [map_add, hhF f f.2, map_add, hgM (h m) (hhM m m.2)]
  have e2 : h (g ((m : V) + f)) = h m + g f := by
    rw [map_add, hgM m m.2, map_add, hhF (g f) (hgF f f.2)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, e2]

theorem commute_of_eigen (hMF : IsCompl M F) {A g : V ≃ₗ[K] V} {s : K}
    (hAM : ∀ m ∈ M, A m = s • m) (hAF : ∀ f ∈ F, A f = -s • f)
    (hgM : ∀ m ∈ M, g m ∈ M) (hgF : ∀ f ∈ F, g f ∈ F) : g * A = A * g := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨m, f, rfl⟩ := LocalAnalysis.ComponentInitial.exists_add_of_isCompl hMF v
  have e1 : g (A ((m : V) + f)) = s • g m + -s • g f := by
    rw [map_add, hAM m m.2, hAF f f.2, map_add, map_smul, map_smul]
  have e2 : A (g ((m : V) + f)) = s • g m + -s • g f := by
    rw [map_add, map_add, hAM _ (hgM m m.2), hAF _ (hgF f f.2)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1, e2]

theorem exists_ext_subgroup {Q : QuadraticForm K V} (hMF : IsCompl M F)
    (horth : ∀ m ∈ M, ∀ f ∈ F, polar Q m f = 0)
    {L : Subgroup (TauCeti.QuadraticMap.orthogonalGroup (Q.comp F.subtype))}
    (hL : CFSG.IsQuasisimple L) :
    ∃ G : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple G ∧
      G ≤ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ g ∈ G, ∀ m ∈ M, g m = m) ∧
      ∀ g ∈ G, ∀ f ∈ F, g f ∈ F := by
  obtain ⟨hinj, hO, -, -⟩ :=
    LocalAnalysis.ComponentInitial.orthogonal_complement_elementary_embedding Q hMF.symm
      (fun f hf m hm => by rw [polar_comm]; exact horth m hm f hf)
  let φ : TauCeti.QuadraticMap.orthogonalGroup (Q.comp F.subtype) →* (V ≃ₗ[K] V) :=
    (LocalAnalysis.ComponentInitial.orthExtend hMF.symm).comp
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp F.subtype)).subtype
  have hφ : Function.Injective φ := hinj.comp Subtype.val_injective
  refine ⟨L.map φ,
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr (L.equivMapOfInjective φ hφ)).1 hL,
    ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact hO x.val x.2
  · rintro _ ⟨x, -, rfl⟩ m hm
    have h := LocalAnalysis.ComponentInitial.orthExtend_apply hMF.symm x.val 0 ⟨m, hm⟩
    rw [map_zero, ZeroMemClass.coe_zero, zero_add] at h
    exact h
  · rintro _ ⟨x, -, rfl⟩ f hf
    have h := LocalAnalysis.ComponentInitial.orthExtend_apply hMF.symm x.val ⟨f, hf⟩ 0
    rw [ZeroMemClass.coe_zero, add_zero, add_zero] at h
    have h' : LocalAnalysis.ComponentInitial.orthExtend hMF.symm x.val f =
        ((x.val ⟨f, hf⟩ : F) : V) := h
    show LocalAnalysis.ComponentInitial.orthExtend hMF.symm x.val f ∈ F
    rw [h']
    exact (x.val ⟨f, hf⟩).2

end Blocks

end CFSG.ComponentClassification.CatLeafProof.EndOddO
