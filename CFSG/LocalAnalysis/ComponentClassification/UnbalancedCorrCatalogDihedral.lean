module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAUnitaryExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAAlternatingSmallDegree
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalDihedralExceptional
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalDihedralTwisted
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCLargeReeExclusion

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Assembly.LowTwoRank Blueprint

@[expose] def DihedralSylowTitsExclusion : Prop :=
  ∀ (T : Type) [Group T] (p f : ℕ), ReeTitsModel T .Tits p f → ∀ s : ℕ, 2 ≤ s →
    ∀ P : Sylow 2 T, ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1)))

@[expose] def DihedralSylowSporadicExclusion : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [Nontrivial T], NativeSporadic.SporadicRep T →
    ∀ s : ℕ, 2 ≤ s →
      ∀ P : Sylow 2 T, ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1)))

theorem catalog_dihedral_sylow_odd_linear_or_alternating_seven_of_exclusions
    (hTits : DihedralSylowTitsExclusion) (hSpor : DihedralSylowSporadicExclusion)
    {T : Type} [Group T] [Finite T] (hnonab : ∃ x y : T, x * y ≠ y * x) (hT : Catalog T)
    {s : ℕ} (hs : 2 ≤ s) (P : Sylow 2 T)
    (hP : Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1)))) :
    (∃ p f : ℕ, p.Prime ∧ Odd p ∧ 1 ≤ f ∧ StatedClassicalModel T .PSL 2 p f) ∨
      Nonempty (T ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨x, y, hxy⟩ := hnonab
  rcases hT with ⟨p, -, ⟨e⟩⟩ | ⟨n, hn, hA⟩ | ⟨t, n, p, f, hC⟩ | hE | hS
  ·
    exact absurd (e.injective (by rw [map_mul, map_mul, mul_comm])) hxy
  ·
    rcases (UnbalancedGS.dihedral_sylow_alternating_model_small_degree hn hA hs P hP).2.2.2 with
      ⟨-, h7⟩ | ⟨ℓ, e, hℓ, hℓo, he, hm⟩
    · exact Or.inr h7
    · exact Or.inl ⟨ℓ, e, hℓ, hℓo, he, hm⟩
  ·
    cases t with
    | PSL =>
      obtain ⟨-, ℓ, e, hℓ, hℓo, he, hm⟩ :=
        OutcomeLocal.dihedral_sylow_linear_model_odd_rank_one hC hs P hP
      exact Or.inl ⟨ℓ, e, hℓ, hℓo, he, hm⟩
    | PSU => exact absurd hP (UnbalancedGS.dihedral_sylow_unitary_model_exclusion hC s hs P)
    | PSp => exact absurd hP (UnbalancedGS.dihedral_sylow_symplectic_model_exclusion hC s hs P)
    | POmegaOdd =>
      exact absurd hP
        (UnbalancingLocal.dihedral_sylow_orthogonal_model_exclusion (.inl rfl) hC s hs P)
    | POmegaPlus =>
      exact absurd hP
        (UnbalancingLocal.dihedral_sylow_orthogonal_model_exclusion (.inr (.inl rfl)) hC s hs P)
    | POmegaMinus =>
      exact absurd hP
        (UnbalancingLocal.dihedral_sylow_orthogonal_model_exclusion (.inr (.inr rfl)) hC s hs P)
    | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
      exact hC.2.elim
  ·
    exfalso
    rcases hE with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
    · simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact UnbalancingLocal.dihedral_sylow_ordinary_exceptional_model_exclusion (.inl rfl) hm
          s hs P hP
      · exact UnbalancingLocal.dihedral_sylow_ordinary_exceptional_model_exclusion
          (.inr (.inl rfl)) hm s hs P hP
      · exact UnbalancingLocal.dihedral_sylow_ordinary_exceptional_model_exclusion
          (.inr (.inr (.inl rfl))) hm s hs P hP
      · exact UnbalancingLocal.dihedral_sylow_ordinary_exceptional_model_exclusion
          (.inr (.inr (.inr (.inl rfl)))) hm s hs P hP
      · exact UnbalancingLocal.dihedral_sylow_ordinary_exceptional_model_exclusion
          (.inr (.inr (.inr (.inr rfl)))) hm s hs P hP
      · exact UnbalancingLocal.dihedral_sylow_graph_twisted_exceptional_model_exclusion
          (.inl rfl) hm s hs P hP
      · exact UnbalancingLocal.dihedral_sylow_graph_twisted_exceptional_model_exclusion
          (.inr rfl) hm s hs P hP
    · simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact UnbalancedGS.dihedral_sylow_small_ree_model_exclusion hm s hs P hP
      · exact UnbalancedGS.dihedral_sylow_large_ree_model_exclusion hm s hs P hP
      · exact hTits T p f hm s hs P hP
    · exact UnbalancedGS.dihedral_sylow_suzuki_model_exclusion hm s hs P hP
  ·
    have : Nontrivial T := ⟨⟨x * y, y * x, hxy⟩⟩
    exact absurd hP (hSpor T hS s hs P)

end CFSG.ComponentClassification.UnbalancedCorr
