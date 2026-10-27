module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ConjClassFunction
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterBasis
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.SimpleCriteria
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_9
import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock

public section

namespace CFSG.LyonsUnitaryFour

section Conjugate

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

noncomputable def conjugateRepresentation (τ : ℂ ≃+* ℂ) (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) where
  toFun g := Matrix.toLin'
    ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ g)).map
      (τ : ℂ →+* ℂ))
  map_one' := by
    rw [map_one, LinearMap.toMatrix_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem conjugateRepresentation_character (τ : ℂ ≃+* ℂ) (ρ : Representation ℂ G V) (g : G) :
    (conjugateRepresentation τ ρ).character g = τ (ρ.character g) := by
  change LinearMap.trace ℂ _ (Matrix.toLin' _) = τ (LinearMap.trace ℂ V (ρ g))
  rw [Matrix.trace_toLin'_eq, LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (ρ g)]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rfl

theorem inner_characterClassFunction_eq [Finite G] (ρ : Representation ℂ G V) :
    letI := Fintype.ofFinite G
    Theory.Character.classFunctionInner (Theory.Character.characterClassFunction ρ)
      (Theory.Character.characterClassFunction ρ) =
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * star (ρ.character g) := rfl

theorem conjugateRepresentation_isIrreducible [Finite G] (τ : ℂ ≃+* ℂ)
    (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) {k : ℕ} (hk : (Nat.card G).Coprime k)
    (hτ : ∀ g, τ (ρ.character g) = ρ.character (g ^ k)) :
    (conjugateRepresentation τ ρ).IsIrreducible := by
  let := Fintype.ofFinite G
  rw [Theory.Character.irreducible_iff_character_norm_one, inner_characterClassFunction_eq]
    at hρ ⊢
  rw [← hρ]
  congr 1
  simp only [conjugateRepresentation_character, hτ]
  exact Equiv.sum_comp (powCoprime hk) (fun g => ρ.character g * star (ρ.character g))

end Conjugate

section Basis

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G) {k : ℕ}

theorem exists_label_character_pow (hk : (Nat.card G).Coprime k) (a : basis.index) :
    ∃ b : basis.index, ∀ g, (basis.representation b).character g =
      (basis.representation a).character (g ^ k) := by
  obtain ⟨τ, hτroot⟩ := CFSG.Section1.complex_galois_aut_pow_on_roots_aux
    (n := Nat.card G) (e := k) Nat.card_pos.ne' hk.symm
  have hτ : ∀ g, τ.toRingEquiv ((basis.representation a).character g) =
      (basis.representation a).character (g ^ k) := fun g =>
    CFSG.Section1.representation_character_apply_galois_eq_argumentPow hτroot
      (basis.representation a).representation (dvd_refl _) g
  let data : FiniteComplexRepresentation G :=
    { vector := Fin (Module.finrank ℂ (basis.representation a).vector) → ℂ
      representation := conjugateRepresentation τ.toRingEquiv
        (basis.representation a).representation }
  have hirr : data.IsIrreducible :=
    conjugateRepresentation_isIrreducible τ.toRingEquiv _ (basis.irreducible a) hk hτ
  obtain ⟨b, hb⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis data hirr
  refine ⟨b, fun g => ?_⟩
  rw [hb]
  change (conjugateRepresentation τ.toRingEquiv _).character g = _
  rw [conjugateRepresentation_character, hτ]

theorem exists_perm_character_pow (hk : (Nat.card G).Coprime k) :
    ∃ π : Equiv.Perm basis.index, ∀ a g, (basis.representation (π a)).character g =
      (basis.representation a).character (g ^ k) := by
  choose f hf using exists_label_character_pow basis hk
  have hinj : Function.Injective f := by
    intro a a' h
    apply basis.distinct
    funext g
    obtain ⟨y, rfl⟩ := (powCoprime hk).surjective g
    have ha := hf a y
    have ha' := hf a' y
    rw [h] at ha
    simp only [powCoprime_apply]
    exact ha.symm.trans ha'
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩

end Basis

end CFSG.LyonsUnitaryFour
