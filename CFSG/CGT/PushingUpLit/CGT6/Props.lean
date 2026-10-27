module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.Assembly
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin
open scoped commutatorElement

@[expose] def IsNaturalAltModuleWith (L : Type) [Group L] (n : ℕ)
    (φ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin (2 * n + 1))) : Prop :=
  ∃ ψ : ↥(shortU L) →* Multiplicative (Fin (2 * n + 1) → ZMod 2),
    (∀ u, ∑ i, Multiplicative.toAdd (ψ u) i = 0) ∧
    (∀ v : Fin (2 * n + 1) → ZMod 2, ∑ i, v i = 0 → ∃ u, ψ u = Multiplicative.ofAdd v) ∧
    ψ.ker = (shortC L).subgroupOf (shortU L) ∧
    ∀ (l u : L) (hu : u ∈ shortU L) (hu' : l * u * l⁻¹ ∈ shortU L),
      ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd (permActionTwo
        ((φ (l : L ⧸ pCore 2 L) : alternatingGroup (Fin (2 * n + 1))) : Equiv.Perm _)
        (Multiplicative.toAdd (ψ ⟨u, hu⟩)))

theorem isNaturalAltModule_iff {L : Type} [Group L] {n : ℕ} :
    IsNaturalAltModule L n ↔
      ∃ φ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin (2 * n + 1)), IsNaturalAltModuleWith L n φ :=
  Iff.rfl

variable {G : Type} [Group G]

@[expose] def ArrowNat (Y X : Subgroup G) : Prop :=
  Y = X ∨ ∃ (a b : ℕ) (φ : (↥X ⧸ pCore 2 ↥X) ≃* alternatingGroup (Fin (2 * a + 1)))
    (F : Finset (Fin (2 * a + 1))),
    Nonempty ((↥Y ⧸ pCore 2 ↥Y) ≃* alternatingGroup (Fin (2 * b + 1))) ∧
    IsNaturalAltModuleWith ↥X a φ ∧ F.card = (2 * a + 1) - (2 * b + 1) ∧
    (shortU ↥Y).map Y.subtype ≤ (shortU ↥X).map X.subtype ∧ Y ≤ X ∧
    ((Y.subgroupOf X).map (QuotientGroup.mk' (pCore 2 ↥X))).map φ.toMonoidHom =
      altStabilizer (2 * a + 1) F

theorem ArrowNat.arrow {Y X : Subgroup G} (h : ArrowNat Y X) : Arrow Y X := by
  rcases h with rfl | ⟨a, b, φ, F, hY, -, hF, hU, hYX, himg⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨2 * b + 1, 2 * a + 1, hY, φ, F, hF, hU, hYX, himg⟩

abbrev Fq (n : ℕ) : Type := GaloisField 2 n

@[expose] noncomputable def omegaPlusAct (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) (Fq n) × Matrix.SpecialLinearGroup (Fin 2) (Fq n) →
      Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)) →
      Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n)) :=
  fun g m => Multiplicative.ofAdd
    ((g.1 : Matrix (Fin 2) (Fin 2) (Fq n)) * Multiplicative.toAdd m *
      (g.2 : Matrix (Fin 2) (Fin 2) (Fq n)).transpose)

@[expose] noncomputable def frobHalf (n : ℕ) (x : Fq (2 * n)) : Fq (2 * n) := x ^ 2 ^ n

@[expose] def hermSub (n : ℕ) : AddSubgroup (Matrix (Fin 2) (Fin 2) (Fq (2 * n))) where
  carrier := {M | ∀ i j, M i j = frobHalf n (M j i)}
  zero_mem' := fun i j => by
    simp [frobHalf]
  add_mem' := by
    intro a b ha hb i j
    have : CharP (Fq (2 * n)) 2 := inferInstance
    simp only [Matrix.add_apply, frobHalf] at ha hb ⊢
    rw [add_pow_char_pow, ← ha i j, ← hb i j]
  neg_mem' := by
    intro a ha i j
    have : CharP (Fq (2 * n)) 2 := inferInstance
    simp only [Matrix.neg_apply, frobHalf] at ha ⊢
    rw [CharTwo.neg_eq, CharTwo.neg_eq]
    exact ha i j

@[expose] noncomputable def omegaMinusAct (n : ℕ) :
    Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)) → Multiplicative (hermSub n) →
      Multiplicative (hermSub n) := fun A m => by
  classical
  exact if h : (A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))) * (Multiplicative.toAdd m : _) *
      ((A : Matrix (Fin 2) (Fin 2) (Fq (2 * n))).map (frobHalf n)).transpose ∈ hermSub n
    then Multiplicative.ofAdd ⟨_, h⟩ else m

@[expose] def OmegaFourOutcome (V Y X : Subgroup G) : Prop :=
  oResidualTwo ↥X = ⊤ ∧ ⁅X, X⁆ = X ∧
    ∃ n : ℕ, 2 ≤ n ∧
      (IsNatBy (omegaPlusAct n) X ⁅X, V⁆ ∨ IsNatBy (omegaMinusAct n) X ⁅X, V⁆) ∧
      (⁅X, V⁆ : Subgroup G) ⊓ Subgroup.centralizer (X : Set G) = ⊥ ∧
      X ⊓ Subgroup.centralizer ((⁅X, V⁆ : Subgroup G) : Set G) ≤
        Subgroup.centralizer (V : Set G) ∧
      ¬ (Y.subgroupOf X).IsSubnormal

@[expose] def AschbacherTwoEight : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (E A : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n →
      A ≤ Subgroup.normalizer (E : Set (MulAut V)) → IsOff A →
      (IsNatSectionBy (omegaPlusAct n) E (commV E) (commV E ⊓ fixV E) ∨
        IsNatSectionBy (omegaMinusAct n) E (commV E) (commV E ⊓ fixV E)) →
      commV E ⊓ fixV E = ⊥ →
      ⁅E, A⁆ = ⊥

end CFSG.CGT.PushingUpLit.CGT6
