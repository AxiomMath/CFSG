module

public import CFSG.LieType.Steinberg.Adjoint.Brackets
public import CFSG.LieType.Chevalley.RootOps.Groups
public import CFSG.LieType.Steinberg.Adjoint.Exp
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Nat

variable {τ : Tag}

theorem simple_smul_eq_sRoot (i : Fin τ.rank) (α : Root τ) : simple τ i • α = sRoot i α :=
  Subtype.ext (simple_smul i α.1)

theorem sign_cast_eq {R : Type*} [CommRing R] {s : ℤ} (hs : s = 1 ∨ s = -1) :
    (s : R) * (s : R) = 1 := by
  rcases hs with rfl | rfl <;> norm_num

theorem sign_mul_sign_eq {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

namespace RootOperatorFamily'

variable (F : RootOperatorFamily τ) {D : AdjData τ} (hD : D.Valid)
include hD

theorem exists_D_one_eq (α : Root τ) :
    ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ ∀ (R : Type) [CommRing R], F.D R α 1 = (δ : R) • D.rootOp R α := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    refine ⟨1, Or.inl rfl, fun R _ => ?_⟩
    rw [Int.cast_one, one_smul, show (⟨Pi.single j 1, IsRoot.basis j⟩ : Root τ) =
      simpleRoot τ j from rfl, F.D_simple, xCoeff_one]
    exact (AdjData.rootOp_simple hD j).symm
  | @reflect i v hv ih =>
    obtain ⟨δ, hδ, h⟩ := ih
    refine ⟨F.sign i ⟨v, hv⟩ * δ * D.rootSign ⟨v, hv⟩ i,
      sign_mul_sign_eq (sign_mul_sign_eq (F.sign_eq i _) hδ) (AdjData.rootSign_eq _ i),
      fun R _ => ?_⟩
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      (simple_smul_eq_sRoot i ⟨v, hv⟩).symm
    rw [hs, F.D_simple_smul, pow_one, h R, mul_smul_comm, smul_mul_assoc, ← weylElt_inv,
      AdjData.rootOp_weyl hD, smul_smul, smul_smul, simple_smul_eq_sRoot]
    push_cast
    ring_nf

@[expose] def relSign (α : Root τ) : ℤ := (exists_D_one_eq F hD α).choose

theorem relSign_eq (α : Root τ) : relSign F hD α = 1 ∨ relSign F hD α = -1 :=
  (exists_D_one_eq F hD α).choose_spec.1

theorem D_one_eq (α : Root τ) (R : Type) [CommRing R] :
    F.D R α 1 = (relSign F hD α : R) • D.rootOp R α :=
  (exists_D_one_eq F hD α).choose_spec.2 R

theorem rootOp_eq (α : Root τ) (R : Type) [CommRing R] :
    D.rootOp R α = (relSign F hD α : R) • F.D R α 1 := by
  rw [D_one_eq F hD, smul_smul, sign_cast_eq (relSign_eq F hD α), one_smul]

omit hD in
theorem D_one_pow (α : Root τ) {R : Type} [CommRing R] (k : ℕ) :
    F.D R α 1 ^ k = (k ! : R) • F.D R α k := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    rw [show (⟨Pi.single j 1, IsRoot.basis j⟩ : Root τ) = simpleRoot τ j from rfl, F.D_simple,
      F.D_simple, xCoeff_one, infE_pow]
  | @reflect i v hv ih =>
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      (simple_smul_eq_sRoot i ⟨v, hv⟩).symm
    rw [hs, F.D_simple_smul, F.D_simple_smul, pow_one, smul_pow, ← weylElt_inv, Units.conj_pow,
      ih, mul_smul_comm, smul_mul_assoc, smul_comm (k ! : R)]
    push_cast
    rfl

theorem bracket (β γ : Root τ) (hγ : γ.1 ≠ -β.1) :
    (∀ h : IsRoot τ (β.1 + γ.1), ∃ N : ℤ, N.natAbs = stringNorm β.1 γ.1 ∧
      ∀ (R : Type) [CommRing R],
        F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 = (N : R) • F.D R ⟨β.1 + γ.1, h⟩ 1) ∧
      (¬IsRoot τ (β.1 + γ.1) → ∀ (R : Type) [CommRing R],
        F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 = 0) := by
  obtain ⟨h₁, h₂⟩ := AdjData.rootOp_bracket.{0} hD β γ hγ
  have key : ∀ (R : Type) [CommRing R], F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 =
      ((relSign F hD β * relSign F hD γ : ℤ) : R) •
        (D.rootOp R β * D.rootOp R γ - D.rootOp R γ * D.rootOp R β) := by
    intro R _
    rw [D_one_eq F hD β, D_one_eq F hD γ, smul_mul_smul_comm, smul_mul_smul_comm,
      mul_comm (relSign F hD γ : R), ← smul_sub, Int.cast_mul]
  refine ⟨fun h => ?_, fun hn R _ => by rw [key, h₂ hn R, smul_zero]⟩
  obtain ⟨N, hN, hbr⟩ := h₁ h
  refine ⟨relSign F hD β * relSign F hD γ * relSign F hD ⟨_, h⟩ * N, ?_, fun R _ => ?_⟩
  · rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_mul, hN]
    rcases relSign_eq F hD β with h1 | h1 <;> rcases relSign_eq F hD γ with h2 | h2 <;>
      rcases relSign_eq F hD (⟨_, h⟩ : Root τ) with h3 | h3 <;> simp [h1, h2, h3]
  · rw [key, hbr R, rootOp_eq F hD, smul_smul, smul_smul]
    push_cast
    ring_nf

open _root_.Classical in
@[expose] def bracketCoeff (β γ : Root τ) : ℤ :=
  if h : γ.1 ≠ -β.1 ∧ IsRoot τ (β.1 + γ.1) then ((bracket F hD β γ h.1).1 h.2).choose else 0

theorem bracketCoeff_natAbs {β γ : Root τ} (hγ : γ.1 ≠ -β.1) (h : IsRoot τ (β.1 + γ.1)) :
    (bracketCoeff F hD β γ).natAbs = stringNorm β.1 γ.1 := by
  rw [bracketCoeff, dite_eq_left ⟨hγ, h⟩]
  exact ((bracket F hD β γ hγ).1 h).choose_spec.1

theorem bracket_eq {β γ : Root τ} (hγ : γ.1 ≠ -β.1) (h : IsRoot τ (β.1 + γ.1)) (R : Type)
    [CommRing R] :
    F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 =
      (bracketCoeff F hD β γ : R) • F.D R ⟨β.1 + γ.1, h⟩ 1 := by
  rw [bracketCoeff, dite_eq_left ⟨hγ, h⟩]
  exact ((bracket F hD β γ hγ).1 h).choose_spec.2 R

theorem bracket_eq_zero {β γ : Root τ} (hγ : γ.1 ≠ -β.1) (h : ¬IsRoot τ (β.1 + γ.1)) (R : Type)
    [CommRing R] : F.D R β 1 * F.D R γ 1 - F.D R γ 1 * F.D R β 1 = 0 :=
  (bracket F hD β γ hγ).2 h R

omit hD in
theorem exists_D_eq_word (α : Root τ) :
    ∃ (j : Fin τ.rank) (ε : ℤ) (w : List (Fin τ.rank)), (ε = 1 ∨ ε = -1) ∧
      ∀ (R : Type) [CommRing R] (k : ℕ), F.D R α k = ((ε ^ k : ℤ) : R) •
        ((((w.map fun i => weylElt τ R i 1).prod : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R)) * xCoeff τ R j k *
          (((w.map fun i => weylElt τ R i 1).prod⁻¹ : (Module.End R (RootModule τ R))ˣ) :
            Module.End R (RootModule τ R))) := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    refine ⟨j, 1, [], Or.inl rfl, fun R _ k => ?_⟩
    rw [show (⟨Pi.single j 1, IsRoot.basis j⟩ : Root τ) = simpleRoot τ j from rfl, F.D_simple]
    simp
  | @reflect i v hv ih =>
    obtain ⟨j, ε, w, hε, h⟩ := ih
    refine ⟨j, F.sign i ⟨v, hv⟩ * ε, i :: w, sign_mul_sign_eq (F.sign_eq i _) hε,
      fun R _ k => ?_⟩
    have hs : (⟨reflect τ i v, IsRoot.reflect i hv⟩ : Root τ) = simple τ i • ⟨v, hv⟩ :=
      (simple_smul_eq_sRoot i ⟨v, hv⟩).symm
    rw [hs, F.D_simple_smul, h R k, mul_smul_comm, smul_mul_assoc, smul_smul, ← weylElt_inv,
      List.map_cons, List.prod_cons, mul_inv_rev, mul_pow, Int.cast_mul]
    simp only [Units.val_mul, mul_assoc]

omit hD in
theorem elt_eq_exp {R : Type} [CommRing R] [Algebra ℚ R] (α : Root τ) (c : R) :
    F.elt R α c = IsNilpotent.exp (c • F.D R α 1) := by
  have h4 : (c • F.D R α 1) ^ 4 = 0 := by
    rw [smul_pow, D_one_pow F α 4, F.D_eq_zero R α 4 le_rfl, smul_zero, smul_zero]
  rw [IsNilpotent.exp_eq_sum h4, RootOperatorFamily.elt]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_pow, D_one_pow F α k, smul_smul,
    ← algebraMap_smul R ((k ! : ℚ)⁻¹) ((c ^ k * (k ! : R)) • F.D R α k), smul_smul]
  congr 1
  rw [mul_comm (c ^ k), ← mul_assoc, show (k ! : R) = algebraMap ℚ R (k ! : ℚ) by simp,
    ← map_mul, inv_mul_cancel₀ (by positivity), map_one, one_mul]

end RootOperatorFamily'

end CFSG.LieType.Steinberg.Adjoint
