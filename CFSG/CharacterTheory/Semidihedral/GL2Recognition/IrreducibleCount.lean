module

public import CFSG.CharacterTheory.Blocks.IrreducibleCharacterBasis
public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.BlockSectionOrthogonality.Helpers

theorem blocksIsClassFunction_iff_exists {G : Type*} [Group G] (f : G → ℂ) :
    CFSG.BlocksIsClassFunction f ↔ ∃ φ : ConjClasses G → ℂ, ∀ g, f g = φ (ConjClasses.mk g) := by
  constructor
  · intro hf
    refine ⟨fun c => f (Classical.choose (ConjClasses.exists_rep c)), fun g => ?_⟩
    have hrep := Classical.choose_spec (ConjClasses.exists_rep (ConjClasses.mk g))
    obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hrep)
    show f g = f (Classical.choose (ConjClasses.exists_rep (ConjClasses.mk g)))
    conv_lhs => rw [← hc]
    exact hf _ _
  · rintro ⟨φ, hφ⟩ g h
    rw [hφ, hφ]
    congr 1
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨h⁻¹, by group⟩)

theorem card_irreducibles_eq_card_conjClasses (G : Type) [Group G] [Fintype G] :
    (irreducibles_finite G).toFinset.card = Nat.card (ConjClasses G) := by
  obtain ⟨-, hind, hspan, -⟩ := irreducible_character_basis G
  let L : (ConjClasses G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun φ g => φ (ConjClasses.mk g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hLinj : Function.Injective L := by
    intro φ ψ h
    funext c
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    exact congrFun h g
  have hrange : LinearMap.range L = Submodule.span ℂ (CFSG.BlocksIrr G) := by
    ext f
    rw [LinearMap.mem_range, ← hspan f, blocksIsClassFunction_iff_exists]
    constructor
    · rintro ⟨φ, rfl⟩
      exact ⟨φ, fun g => rfl⟩
    · rintro ⟨φ, hφ⟩
      exact ⟨φ, funext fun g => (hφ g).symm⟩
  let _ : Fintype (CFSG.BlocksIrr G) := (irreducibles_finite G).fintype
  have h1 : Module.finrank ℂ (LinearMap.range L) = Nat.card (ConjClasses G) := by
    rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_fintype_fun_eq_card,
      Nat.card_eq_fintype_card]
  have h2 : Module.finrank ℂ (Submodule.span ℂ (CFSG.BlocksIrr G)) =
      Fintype.card (CFSG.BlocksIrr G) := by
    have h := finrank_span_eq_card hind
    rwa [Subtype.range_coe] at h
  rw [Set.Finite.card_toFinset, ← h2, ← hrange, h1]

theorem commutator_eq_top_of_linear_eq_one {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G)
    (h : ∀ l : basis.index, (basis.representation l).character 1 = 1 →
      (basis.representation l).character = 1) :
    commutator G = ⊤ := by
  by_contra hne
  have hnt : ∃ a : Abelianization G, a ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne
    rw [eq_top_iff]
    intro g _
    rw [← Abelianization.ker_of, MonoidHom.mem_ker]
    exact hall _
  obtain ⟨a, ha⟩ := hnt
  have : Finite (Abelianization G) := Finite.of_surjective _ (QuotientGroup.mk_surjective)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (Abelianization G) ℂ ha
  obtain ⟨g, rfl⟩ : ∃ g : G, Abelianization.of g = a := QuotientGroup.mk_surjective a
  obtain ⟨l, hl⟩ := CFSG.Wreathed.CompatibleFamily.exists_linear_label basis
    (φ.comp Abelianization.of)
  have hl1 : (basis.representation l).character 1 = 1 := by
    rw [hl, map_one, Units.val_one]
  have hprin := congrFun (h l hl1) g
  rw [hl, Pi.one_apply, MonoidHom.comp_apply] at hprin
  exact hφ (Units.val_eq_one.mp hprin)

end CFSG.Semidihedral.GL2Recognition
