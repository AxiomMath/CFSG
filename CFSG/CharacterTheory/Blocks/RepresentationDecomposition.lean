module

public import CFSG.CharacterTheory.Blocks.VirtualCharacterCoefficients

public section

open scoped BigOperators Classical

namespace CFSG

open TwoRankLowerBound.Helpers

universe u

theorem complex_representation_invariant_complement {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Submodule ℂ V)
    (hW : ∀ (g : G), ∀ v ∈ W, ρ g v ∈ W) :
    ∃ W' : Submodule ℂ V, IsCompl W W' ∧ ∀ (g : G), ∀ v ∈ W', ρ g v ∈ W' := by
  have : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let Wr : Subrepresentation ρ := ⟨W, fun g v hv => hW g v hv⟩
  obtain ⟨Wc, hWc⟩ := ComplementedLattice.exists_isCompl Wr
  refine ⟨Wc.toSubmodule, ⟨?_, ?_⟩, fun g v hv => Wc.apply_mem_toSubmodule g hv⟩
  · rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule hWc.inf_eq_bot
  · rw [codisjoint_iff]
    exact congrArg Subrepresentation.toSubmodule hWc.sup_eq_top

theorem natural_expansion_eq_blocksCharacterExpansion {G : Type} [Group G]
    (m : BlocksIrr G →₀ ℕ) :
    (m.sum fun χ k => (k : ℂ) • (χ : G → ℂ)) =
      blocksCharacterExpansion G (m.mapRange (fun k : ℕ => (k : ℤ)) (by simp)) := by
  rw [blocksCharacterExpansion, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (by simp)]
  refine Finsupp.sum_congr fun χ _ => ?_
  funext x
  simp

theorem natural_expansion_coefficient {G : Type} [Group G] [Fintype G] (m : BlocksIrr G →₀ ℕ)
    (χ : BlocksIrr G) :
    BlocksInnerProduct (m.sum fun χ k => (k : ℂ) • (χ : G → ℂ)) (χ : G → ℂ) = (m χ : ℂ) := by
  rw [natural_expansion_eq_blocksCharacterExpansion, blocksInnerProduct_expansion_coefficient,
    Finsupp.mapRange_apply]
  push_cast
  rfl

theorem complex_representation_character_decomposition {G : Type} [Group G] [Fintype G]
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    (∃ (n : ℕ) (W : Fin n → FiniteComplexRepresentation.{0, 0} G)
        (e : V ≃ₗ[ℂ] ∀ i, (W i).vector),
      (∀ i, (W i).IsIrreducible) ∧
        ∀ (g : G) (v : V) (i : Fin n), e (ρ g v) i = (W i).representation g (e v i)) ∧
    (∃! m : BlocksIrr G →₀ ℕ, ρ.character = m.sum fun χ k => (k : ℂ) • (χ : G → ℂ)) ∧
    ∀ m : BlocksIrr G →₀ ℕ, ρ.character = (m.sum fun χ k => (k : ℂ) • (χ : G → ℂ)) →
      ∀ χ : BlocksIrr G, (m χ : ℂ) = BlocksInnerProduct ρ.character χ := by
  have hcoeff : ∀ m : BlocksIrr G →₀ ℕ,
      ρ.character = (m.sum fun χ k => (k : ℂ) • (χ : G → ℂ)) →
      ∀ χ : BlocksIrr G, (m χ : ℂ) = BlocksInnerProduct ρ.character χ := by
    intro m hm χ
    rw [hm, natural_expansion_coefficient]
  refine ⟨?_, ?_, hcoeff⟩
  ·
    obtain ⟨size, summand, equivalence, hsimple⟩ :=
      representation_exists_simple_module_decomposition ρ
    let : ∀ i, FiniteDimensional ℂ (summand i) := fun i =>
      Module.Finite.of_injective ((summand i).subtype.restrictScalars ℂ)
        (summand i).subtype_injective
    let W : Fin size → FiniteComplexRepresentation.{0, 0} G := fun i =>
      moduleFiniteComplexRepresentation (G := G) (module := summand i)
    let e : V ≃ₗ[ℂ] ∀ i, (W i).vector :=
      ρ.asModuleEquiv.symm.trans ((equivalence.restrictScalars ℂ).trans
        (LinearEquiv.piCongrRight fun i =>
          (restrictScalarsLinearEquiv (G := G) (module := summand i)).symm))
    refine ⟨size, W, e, fun i => ?_, fun g v i => ?_⟩
    · have : IsSimpleModule (MonoidAlgebra ℂ G) (summand i) := hsimple i
      exact moduleFiniteComplexRepresentation_isIrreducible
    · change (restrictScalarsLinearEquiv (G := G) (module := summand i)).symm
          (equivalence (ρ.asModuleEquiv.symm (ρ g v)) i) =
        Representation.ofModule (k := ℂ) (G := G) (summand i) g
          ((restrictScalarsLinearEquiv (G := G) (module := summand i)).symm
            (equivalence (ρ.asModuleEquiv.symm v) i))
      rw [Representation.asModuleEquiv_symm_map_rho, map_smul]
      rfl
  ·
    obtain ⟨size, summand, hirr, hsum⟩ :=
      finiteComplexRepresentation_exists_irreducible_character_sum
        ({ vector := V, representation := ρ } : FiniteComplexRepresentation.{0, 0} G)
    have hmem : ∀ j, (summand j).character ∈ BlocksIrr G := by
      intro j
      rw [blocksIrr_eq_irreducible_characters]
      exact ⟨summand j, hirr j, rfl⟩
    let μ : Fin size → BlocksIrr G := fun j => ⟨(summand j).character, hmem j⟩
    let m : BlocksIrr G →₀ ℕ := ∑ j, Finsupp.single (μ j) 1
    have hm : ρ.character = m.sum fun χ k => (k : ℂ) • (χ : G → ℂ) := by
      simp only [m]
      rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
      funext g
      rw [Finset.sum_apply]
      refine (hsum g).trans (Finset.sum_congr rfl fun j _ => ?_)
      rw [Finsupp.sum_single_index (by simp)]
      simp [μ]
    refine ⟨m, hm, fun m' hm' => ?_⟩
    ext χ
    have h1 := hcoeff m hm χ
    have h2 := hcoeff m' hm' χ
    exact_mod_cast h2.trans h1.symm

end CFSG
