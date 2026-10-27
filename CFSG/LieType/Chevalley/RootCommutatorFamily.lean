module

public import CFSG.LieType.Chevalley.RootCommutatorPairs
public import CFSG.LieType.Chevalley.RootOps.Groups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem conj_list_prod {G : Type*} [Group G] (n : G) (l : List G) :
    n * l.prod * n⁻¹ = (l.map fun x => n * x * n⁻¹).prod := by
  induction l with
  | nil => simp
  | cons x l ih => rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]; group

namespace RootOperatorFamily

variable
    {τ : Tag} (F : RootOperatorFamily τ)

open _root_.Classical in
@[expose] def eltVec
    (R : Type) [CommRing R] (γ : Fin τ.rank → ℤ) (c : R) :
    (Module.End R (RootModule τ R))ˣ :=
  if h : IsRoot τ γ then F.eltUnit R ⟨γ, h⟩ c else 1

theorem eltVec_of_isRoot
    {R : Type} [CommRing R] {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : R) :
    F.eltVec R γ c = F.eltUnit R ⟨γ, h⟩ c := by
  unfold eltVec
  exact dite_eq_left h

theorem eltVec_of_not_isRoot
    {R : Type} [CommRing R] {γ : Fin τ.rank → ℤ} (h : ¬IsRoot τ γ)
    (c : R) : F.eltVec R γ c = 1 := by
  unfold eltVec
  exact dite_eq_right h

theorem eltVec_neg
    {R : Type} [CommRing R] (γ : Fin τ.rank → ℤ) (c : R) :
    F.eltVec R γ (-c) = (F.eltVec R γ c)⁻¹ := by
  by_cases h : IsRoot τ γ
  · rw [F.eltVec_of_isRoot h, F.eltVec_of_isRoot h, F.eltUnit_inv]
  · rw [F.eltVec_of_not_isRoot h, F.eltVec_of_not_isRoot h, inv_one]

open _root_.Classical in
@[expose] def signVec
    (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) : ℤ :=
  if h : IsRoot τ γ then F.sign i ⟨γ, h⟩ else 1

theorem signVec_eq
    (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    F.signVec i γ = 1 ∨ F.signVec i γ = -1 := by
  unfold signVec
  split_ifs with h
  · exact F.sign_eq i _
  · exact .inl rfl

theorem abs_signVec
    (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) : |F.signVec i γ| = 1 := by
  rcases F.signVec_eq i γ with h | h <;> rw [h] <;> rfl

theorem signVec_cast_mul_self
    (R : Type) [CommRing R] (i : Fin τ.rank) (γ : Fin τ.rank → ℤ) :
    (F.signVec i γ : R) * F.signVec i γ = 1 := by
  rcases F.signVec_eq i γ with h | h <;> rw [h] <;> norm_num

theorem weylElt_mul_eltVec_mul_inv
    (R : Type) [CommRing R] (i : Fin τ.rank)
    (γ : Fin τ.rank → ℤ) (c : R) :
    weylElt τ R i 1 * F.eltVec R γ c * (weylElt τ R i 1)⁻¹ =
      F.eltVec R (simple τ i • γ) ((F.signVec i γ : R) * c) := by
  by_cases h : IsRoot τ γ
  · rw [F.eltVec_of_isRoot h, F.eltVec_of_isRoot (IsRoot.smul h _),
      F.weylElt_mul_eltUnit_mul_inv]
    unfold signVec
    rw [dite_eq_left h]
    rfl
  · rw [F.eltVec_of_not_isRoot h, F.eltVec_of_not_isRoot fun h' => h ((isRoot_smul_iff _).1 h'),
      mul_one, mul_inv_cancel]

@[expose] def CommFormula
    (α β : Fin τ.rank → ℤ) (C : ℕ × ℕ → ℤ) : Prop :=
  ∀ (R : Type) [CommRing R] (c d : R),
    F.eltVec R α c * F.eltVec R β d * F.eltVec R α (-c) * F.eltVec R β (-d) =
      ((commPairs τ α β).map fun p =>
        F.eltVec R (p.1 • α + p.2 • β) ((C p : R) * c ^ p.1 * d ^ p.2)).prod

@[expose] def HasCommFormula
    (M : ℕ) (α β : Fin τ.rank → ℤ) : Prop :=
  ∃ C : ℕ × ℕ → ℤ, (∀ p ∈ commPairs τ α β, 1 ≤ |C p| ∧ |C p| ≤ M) ∧ F.CommFormula α β C

variable {F}

theorem CommFormula.simple_smul
    {α β : Fin τ.rank → ℤ} {C : ℕ × ℕ → ℤ}
    (h : F.CommFormula α β C) (i : Fin τ.rank) :
    F.CommFormula (simple τ i • α) (simple τ i • β) fun p =>
      F.signVec i (p.1 • α + p.2 • β) * F.signVec i α ^ p.1 * F.signVec i β ^ p.2 * C p := by
  intro R _ c d
  have hα := F.signVec_cast_mul_self R i α
  have hβ := F.signVec_cast_mul_self R i β
  have key := congrArg (fun x => weylElt τ R i 1 * x * (weylElt τ R i 1)⁻¹)
    (h R ((F.signVec i α : R) * c) ((F.signVec i β : R) * d))
  have e : ∀ x y z u : (Module.End R (RootModule τ R))ˣ,
      weylElt τ R i 1 * (x * y * z * u) * (weylElt τ R i 1)⁻¹ =
        (weylElt τ R i 1 * x * (weylElt τ R i 1)⁻¹) * (weylElt τ R i 1 * y * (weylElt τ R i 1)⁻¹) *
          (weylElt τ R i 1 * z * (weylElt τ R i 1)⁻¹) *
          (weylElt τ R i 1 * u * (weylElt τ R i 1)⁻¹) := fun x y z u => by group
  have e1 : (F.signVec i α : R) * ((F.signVec i α : R) * c) = c := by rw [← mul_assoc, hα, one_mul]
  have e2 : (F.signVec i α : R) * -((F.signVec i α : R) * c) = -c := by rw [mul_neg, e1]
  have e3 : (F.signVec i β : R) * ((F.signVec i β : R) * d) = d := by rw [← mul_assoc, hβ, one_mul]
  have e4 : (F.signVec i β : R) * -((F.signVec i β : R) * d) = -d := by rw [mul_neg, e3]
  simp only [e, F.weylElt_mul_eltVec_mul_inv, e1, e2, e3, e4, conj_list_prod, List.map_map] at key
  rw [key, commPairs_smul]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [Function.comp_apply, F.weylElt_mul_eltVec_mul_inv, smul_nsmul_add_nsmul_eq]
  congr 1
  push_cast
  ring

theorem HasCommFormula.simple_smul
    {M : ℕ} {α β : Fin τ.rank → ℤ} (h : F.HasCommFormula M α β)
    (i : Fin τ.rank) : F.HasCommFormula M (simple τ i • α) (simple τ i • β) := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨_, fun p hp => ?_, hF.simple_smul i⟩
  rw [commPairs_smul] at hp
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, F.abs_signVec, F.abs_signVec, F.abs_signVec,
    one_pow, one_pow, one_mul, one_mul, one_mul]
  exact hC p hp

theorem HasCommFormula.smul
    {M : ℕ} {α β : Fin τ.rank → ℤ} (h : F.HasCommFormula M α β)
    (w : WeylGroup τ) : F.HasCommFormula M (w • α) (w • β) := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => simpa using h
  | mul_simple_left w i ih =>
    rw [mul_smul, mul_smul]
    exact ih.simple_smul i

end RootOperatorFamily

end CFSG.LieType.Chevalley
