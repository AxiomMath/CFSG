module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.TwoTorusAlg
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Matrix Polynomial

variable {F : Type*} [Field F]

@[expose] noncomputable def evRoot (E : Matrix (Fin 2) (Fin 2) F) :
    AdjoinRoot E.charpoly →+* Matrix (Fin 2) (Fin 2) F :=
  Ideal.Quotient.lift (Ideal.span {E.charpoly}) (aeval E : F[X] →ₐ[F] _).toRingHom (by
    intro g hg
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.1 hg
    simp [Matrix.aeval_self_charpoly])

theorem evRoot_mk (E : Matrix (Fin 2) (Fin 2) F) (g : F[X]) :
    evRoot E (AdjoinRoot.mk E.charpoly g) = aeval E g := rfl

theorem evRoot_root (E : Matrix (Fin 2) (Fin 2) F) :
    evRoot E (AdjoinRoot.root E.charpoly) = E := by
  rw [AdjoinRoot.root, evRoot_mk]; simp

theorem evRoot_of (E : Matrix (Fin 2) (Fin 2) F) (a : F) :
    evRoot E (algebraMap F (AdjoinRoot E.charpoly) a) = a • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, evRoot_mk]
  simp [Algebra.algebraMap_eq_smul_one]

theorem evRoot_comm (E : Matrix (Fin 2) (Fin 2) F) (x : AdjoinRoot E.charpoly) :
    evRoot E x * E = E * evRoot E x := by
  have h := congrArg (evRoot E) (mul_comm x (AdjoinRoot.root E.charpoly))
  rwa [map_mul, map_mul, evRoot_root] at h

theorem exists_torus [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {E : Matrix (Fin 2) (Fin 2) F} (hE : ∀ a : F, E.charpoly.eval a ≠ 0) :
    ∃ T : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F),
      (∀ A ∈ T, (A : Matrix (Fin 2) (Fin 2) F) * E = E * A) ∧ IsCyclic T ∧
      Nat.card F + 1 ≤ Nat.card T ∧ (∀ A ∈ T, A ^ p = 1 → A = 1) ∧
      (∀ s : F, ∀ A ∈ T, (A : Matrix (Fin 2) (Fin 2) F).trace = s → ∀ A' ∈ T,
        (A' : Matrix (Fin 2) (Fin 2) F).trace = s →
        A' = A ∨ (A' : Matrix (Fin 2) (Fin 2) F) =
          s • (1 : Matrix (Fin 2) (Fin 2) F) - A) := by
  classical
  have hdeg : E.charpoly.natDegree = 2 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hirr : Irreducible E.charpoly :=
    irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hE
  have : Fact (Irreducible E.charpoly) := ⟨hirr⟩
  have hevinj : Function.Injective (evRoot E) := (evRoot E).injective
  have : Module.Finite F (AdjoinRoot E.charpoly) := (Matrix.charpoly_monic E).finite_adjoinRoot
  have : Finite (AdjoinRoot E.charpoly) := Module.finite_of_finite F
  have : CharP (AdjoinRoot E.charpoly) p :=
    charP_of_injective_algebraMap (algebraMap F (AdjoinRoot E.charpoly)).injective p
  have hcardL : Nat.card (AdjoinRoot E.charpoly) = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := AdjoinRoot E.charpoly)]
    congr 1
    have := (AdjoinRoot.powerBasis hirr.ne_zero).finrank
    rw [AdjoinRoot.powerBasis_dim] at this
    rw [this, hdeg]
  let detEv : AdjoinRoot E.charpoly →* F :=
    (Matrix.detMonoidHom (n := Fin 2) (R := F)).comp (evRoot E).toMonoidHom
  let ψ : (AdjoinRoot E.charpoly)ˣ →* Fˣ := Units.map detEv
  let Kr : Subgroup (AdjoinRoot E.charpoly)ˣ := ψ.ker
  have hdetx : ∀ x : Kr, (evRoot E ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly)).det = 1 := by
    intro x
    have hx := x.2
    rw [MonoidHom.mem_ker] at hx
    have := congrArg Units.val hx
    simpa [ψ, detEv] using this
  let Φ : Kr →* Matrix.SpecialLinearGroup (Fin 2) F :=
    MonoidHom.mk' (fun x => ⟨evRoot E ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly), hdetx x⟩)
      (fun x y => by
        refine Subtype.ext ?_
        show evRoot E (((x * y : Kr) : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) =
          evRoot E ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) *
            evRoot E ((y : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly)
        simp)
  have hΦval : ∀ x : Kr, ((Φ x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      evRoot E ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) := fun x => rfl
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have h : evRoot E ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) =
        evRoot E ((y : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) := by
      rw [← hΦval, ← hΦval, hxy]
    exact Subtype.ext (Units.ext (hevinj h))
  have hq : 2 ≤ Nat.card F := Nat.succ_le_of_lt Finite.one_lt_card
  have hcardLu : Nat.card (AdjoinRoot E.charpoly)ˣ = Nat.card F ^ 2 - 1 := by
    rw [Nat.card_units (AdjoinRoot E.charpoly), hcardL]
  have hcardFu : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have hmul := Subgroup.card_ker_mul_card_range ψ
  have hrange : Nat.card ψ.range ≤ Nat.card F - 1 := by
    rw [← hcardFu]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hKcard : Nat.card F + 1 ≤ Nat.card Kr := by
    have hsq : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1, (by omega : 1 ≤ Nat.card F)]
      ring
    have h2 : (Nat.card F + 1) * (Nat.card F - 1) ≤ Nat.card Kr * (Nat.card F - 1) := by
      calc (Nat.card F + 1) * (Nat.card F - 1) = Nat.card Kr * Nat.card ψ.range := by
            rw [← hsq, ← hcardLu, ← hmul]
        _ ≤ Nat.card Kr * (Nat.card F - 1) := Nat.mul_le_mul_left _ hrange
    exact Nat.le_of_mul_le_mul_right h2 (by omega)
  refine ⟨Φ.range, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨x, rfl⟩
    rw [hΦval]
    exact evRoot_comm E _
  · have : IsCyclic Kr := inferInstance
    exact isCyclic_of_surjective Φ.rangeRestrict Φ.rangeRestrict_surjective
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv]
    exact hKcard
  · rintro A ⟨x, rfl⟩ hA
    have h1 : Φ (x ^ p) = Φ 1 := by rw [map_pow, hA, map_one]
    have h2 := hΦinj h1
    have h3 : ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) ^ p = 1 := by
      have := congrArg (fun y : Kr => ((y : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly)) h2
      simpa using this
    have h4 : (((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) - 1) ^ p = 0 := by
      rw [sub_pow_char, h3, one_pow, sub_self]
    have h5 : ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) = 1 := by
      have := pow_eq_zero_iff (n := p) (Fact.out : p.Prime).ne_zero |>.1 h4
      exact sub_eq_zero.1 this
    have : x = 1 := Subtype.ext (Units.ext h5)
    rw [this, map_one]
  · rintro s A ⟨x, rfl⟩ hs A' ⟨x', rfl⟩ hs'
    have key : ∀ y : Kr, (Φ y : Matrix.SpecialLinearGroup (Fin 2) F).1.trace = s →
        ((y : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) ^ 2 -
          algebraMap F (AdjoinRoot E.charpoly) s * ((y : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) + 1 = 0 := by
      intro y hy
      apply hevinj
      have hCH := mat2_mul_self (evRoot E ((y : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly))
      rw [hdetx y, one_smul] at hCH
      rw [hΦval] at hy
      simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, evRoot_of]
      rw [pow_two, hCH, hy]
      simp
    have h1 := key x hs
    have h2 := key x' hs'
    have hprod : (((x' : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) - ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly)) *
        (((x' : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) + ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) -
          algebraMap F (AdjoinRoot E.charpoly) s) = 0 := by
      linear_combination h2 - h1
    rcases mul_eq_zero.1 hprod with h | h
    · left
      have : x' = x := Subtype.ext (Units.ext (sub_eq_zero.1 h))
      rw [this]
    · right
      have h' : ((x' : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) =
          algebraMap F (AdjoinRoot E.charpoly) s - ((x : (AdjoinRoot E.charpoly)ˣ) : AdjoinRoot E.charpoly) := by
        linear_combination h
      rw [hΦval, h']
      simp only [map_sub, evRoot_of, hΦval]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
