module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.GroupTheory

open Function

section FiniteAmalgam

variable {A B C : Type*} [Group A] [Group B] [Group C]

private def cosetSetoid (i : C →* A) : Setoid A where
  r a b := ∃ c : C, i c * a = b
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨1, by simp⟩
    · rintro a b ⟨c, rfl⟩
      exact ⟨c⁻¹, by simp⟩
    · rintro a b d ⟨c, rfl⟩ ⟨c', rfl⟩
      exact ⟨c' * c, by simp [map_mul, mul_assoc]⟩

private abbrev Coset (i : C →* A) : Type _ := Quotient (cosetSetoid i)

private abbrev mkCoset (i : C →* A) (a : A) : Coset i :=
  Quotient.mk'' (s₁ := cosetSetoid i) a

private noncomputable def cosetRep (i : C →* A) (r : Coset i) : A := Quotient.out r

private lemma cosetRep_spec (i : C →* A) (a : A) :
    ∃ c : C, i c * cosetRep i (mkCoset i a) = a :=
  Quotient.mk_out (s := cosetSetoid i) a

private noncomputable def cosetCoeff (i : C →* A) (a : A) : C :=
  Classical.choose (cosetRep_spec i a)

private lemma cosetCoeff_spec (i : C →* A) (a : A) :
    i (cosetCoeff i a) * cosetRep i (mkCoset i a) = a :=
  Classical.choose_spec (cosetRep_spec i a)

private noncomputable def eA (i : C →* A) (hi : Injective i) : C × Coset i ≃ A where
  toFun p := i p.1 * cosetRep i p.2
  invFun a := (cosetCoeff i a, mkCoset i a)
  left_inv := by
    rintro ⟨c, r⟩
    refine Prod.ext ?_ ?_
    · have h2 : mkCoset i (i c * cosetRep i r) = r := by
        conv_rhs => rw [← Quotient.out_eq' r]
        exact Quotient.sound' (s₁ := cosetSetoid i) (a := i c * cosetRep i r)
          (b := cosetRep i r) ⟨c⁻¹, by simp⟩
      have h := cosetCoeff_spec i (i c * cosetRep i r)
      rw [h2] at h
      exact hi (mul_right_cancel h)
    · conv_rhs => rw [← Quotient.out_eq' r]
      exact Quotient.sound' (s₁ := cosetSetoid i) (a := i c * cosetRep i r)
        (b := cosetRep i r) ⟨c⁻¹, by simp⟩
  right_inv a := cosetCoeff_spec i a

private lemma eA_symm_apply (i : C →* A) (hi : Injective i) (a : A) :
    (eA i hi).symm a = (cosetCoeff i a, mkCoset i a) := rfl

private lemma eA_symm_mul_left (i : C →* A) (hi : Injective i) (c₀ : C) (a : A) :
    (eA i hi).symm (i c₀ * a) = (c₀ * ((eA i hi).symm a).1, ((eA i hi).symm a).2) := by
  apply (eA i hi).injective
  rw [Equiv.apply_symm_apply]
  show i c₀ * a = i (c₀ * ((eA i hi).symm a).1) * cosetRep i ((eA i hi).symm a).2
  rw [map_mul, mul_assoc]
  exact (congrArg (fun z => i c₀ * z) (cosetCoeff_spec i a)).symm

private abbrev AmalgamSet (i : C →* A) (j : C →* B) : Type _ :=
  (C × Coset i) × Coset j

private noncomputable def fAct (i : C →* A) (hi : Injective i) (a : A) (q : C × Coset i) :
    C × Coset i :=
  (eA i hi).symm (a * eA i hi q)

private noncomputable def gAct (j : C →* B) (hj : Injective j) (b : B) (q : C × Coset j) :
    C × Coset j :=
  (eA j hj).symm (b * eA j hj q)

private lemma fAct_mul (i : C →* A) (hi : Injective i) (a a' : A) (q : C × Coset i) :
    fAct i hi a (fAct i hi a' q) = fAct i hi (a * a') q := by
  simp only [fAct, Equiv.apply_symm_apply, mul_assoc]

private lemma fAct_one (i : C →* A) (hi : Injective i) (q : C × Coset i) :
    fAct i hi 1 q = q := by
  simp [fAct]

private lemma fAct_inv (i : C →* A) (hi : Injective i) (a : A) (q : C × Coset i) :
    fAct i hi a⁻¹ (fAct i hi a q) = q := by
  simp [fAct, mul_assoc]

private lemma fAct_inv' (i : C →* A) (hi : Injective i) (a : A) (q : C × Coset i) :
    fAct i hi a (fAct i hi a⁻¹ q) = q := by
  simp [fAct, mul_assoc]

private lemma gAct_mul (j : C →* B) (hj : Injective j) (b b' : B) (q : C × Coset j) :
    gAct j hj b (gAct j hj b' q) = gAct j hj (b * b') q := by
  simp only [gAct, Equiv.apply_symm_apply, mul_assoc]

private lemma gAct_one (j : C →* B) (hj : Injective j) (q : C × Coset j) :
    gAct j hj 1 q = q := by
  simp [gAct]

private lemma gAct_inv (j : C →* B) (hj : Injective j) (b : B) (q : C × Coset j) :
    gAct j hj b ((gAct j hj b⁻¹ q).1, (gAct j hj b⁻¹ q).2) = q := by
  rw [show ((gAct j hj b⁻¹ q).1, (gAct j hj b⁻¹ q).2) = gAct j hj b⁻¹ q from rfl]
  simp [gAct, mul_assoc]

private lemma gAct_inv' (j : C →* B) (hj : Injective j) (b : B) (q : C × Coset j) :
    gAct j hj b⁻¹ ((gAct j hj b q).1, (gAct j hj b q).2) = q := by
  rw [show ((gAct j hj b q).1, (gAct j hj b q).2) = gAct j hj b q from rfl]
  simp [gAct, mul_assoc]

private lemma fAct_i (i : C →* A) (hi : Injective i) (c₀ : C) (c : C) (x : Coset i) :
    fAct i hi (i c₀) (c, x) = (c₀ * c, x) := by
  simp [fAct, eA_symm_mul_left]

private lemma gAct_j (j : C →* B) (hj : Injective j) (c₀ : C) (c : C) (y : Coset j) :
    gAct j hj (j c₀) (c, y) = (c₀ * c, y) := by
  simp [gAct, eA_symm_mul_left]

private noncomputable def fPerm (i : C →* A) (hi : Injective i) (j : C →* B) (a : A) :
    Equiv.Perm (AmalgamSet i j) where
  toFun p := (fAct i hi a p.1, p.2)
  invFun p := (fAct i hi a⁻¹ p.1, p.2)
  left_inv p := by
    obtain ⟨q, y⟩ := p
    simp only [fAct_inv]
  right_inv p := by
    obtain ⟨q, y⟩ := p
    simp only [fAct_inv']

private noncomputable def gPerm (i : C →* A) (j : C →* B) (hj : Injective j) (b : B) :
    Equiv.Perm (AmalgamSet i j) where
  toFun p := (((gAct j hj b (p.1.1, p.2)).1, p.1.2), (gAct j hj b (p.1.1, p.2)).2)
  invFun p := (((gAct j hj b⁻¹ (p.1.1, p.2)).1, p.1.2), (gAct j hj b⁻¹ (p.1.1, p.2)).2)
  left_inv p := by
    obtain ⟨⟨c, x⟩, y⟩ := p
    have h : gAct j hj b⁻¹ ((gAct j hj b (c, y)).1, (gAct j hj b (c, y)).2) = (c, y) :=
      gAct_inv' j hj b (c, y)
    simp only [h]
  right_inv p := by
    obtain ⟨⟨c, x⟩, y⟩ := p
    have h : gAct j hj b ((gAct j hj b⁻¹ (c, y)).1, (gAct j hj b⁻¹ (c, y)).2) = (c, y) :=
      gAct_inv j hj b (c, y)
    simp only [h]

private lemma fPerm_apply (i : C →* A) (hi : Injective i) (j : C →* B) (a : A)
    (p : AmalgamSet i j) :
    fPerm i hi j a p = (fAct i hi a p.1, p.2) := rfl

private lemma gPerm_apply (i : C →* A) (j : C →* B) (hj : Injective j) (b : B)
    (c : C) (x : Coset i) (y : Coset j) :
    gPerm i j hj b ((c, x), y) = (((gAct j hj b (c, y)).1, x), (gAct j hj b (c, y)).2) := rfl

private noncomputable def fHom (i : C →* A) (hi : Injective i) (j : C →* B) :
    A →* Equiv.Perm (AmalgamSet i j) where
  toFun := fPerm i hi j
  map_one' := by
    apply Equiv.Perm.ext
    intro p
    obtain ⟨q, y⟩ := p
    show (fAct i hi 1 q, y) = (q, y)
    simp only [fAct_one]
  map_mul' a a' := by
    apply Equiv.Perm.ext
    intro p
    obtain ⟨⟨c, x⟩, y⟩ := p
    show (fAct i hi (a * a') (c, x), y) = (fAct i hi a (fAct i hi a' (c, x)), y)
    simp only [fAct_mul]

private noncomputable def gHom (i : C →* A) (j : C →* B) (hj : Injective j) :
    B →* Equiv.Perm (AmalgamSet i j) where
  toFun := gPerm i j hj
  map_one' := by
    apply Equiv.Perm.ext
    intro p
    obtain ⟨⟨c, x⟩, y⟩ := p
    show (((gAct j hj 1 (c, y)).1, x), (gAct j hj 1 (c, y)).2) = ((c, x), y)
    simp only [gAct_one]
  map_mul' b b' := by
    apply Equiv.Perm.ext
    intro p
    obtain ⟨⟨c, x⟩, y⟩ := p
    show (((gAct j hj (b * b') (c, y)).1, x), (gAct j hj (b * b') (c, y)).2)
      = (((gAct j hj b (gAct j hj b' (c, y))).1, x),
          (gAct j hj b (gAct j hj b' (c, y))).2)
    simp only [gAct_mul]

private theorem fPerm_injective (i : C →* A) (hi : Injective i) (j : C →* B) :
    Injective (fPerm i hi j) := by
  intro a a' h
  set q₀ : C × Coset i := ((1 : C), mkCoset i (1 : A)) with hq₀
  set r₀ : Coset j := mkCoset j (1 : B) with hr₀
  have hp : fPerm i hi j a (q₀, r₀) = fPerm i hi j a' (q₀, r₀) :=
    congrArg (fun σ : Equiv.Perm (AmalgamSet i j) => σ (q₀, r₀)) h
  have h1 : fAct i hi a q₀ = fAct i hi a' q₀ := by
    simpa [fPerm_apply] using congrArg (fun p : AmalgamSet i j => p.1) hp
  have h1' : (eA i hi).symm (a * eA i hi q₀) = (eA i hi).symm (a' * eA i hi q₀) := by
    simpa only [fAct] using h1
  have h2 : a * eA i hi q₀ = a' * eA i hi q₀ := by
    simpa using congrArg (eA i hi) h1'
  exact mul_right_cancel h2

private theorem gPerm_injective (i : C →* A) (j : C →* B) (hj : Injective j) :
    Injective (gPerm i j hj) := by
  intro b b' h
  set q₀ : C × Coset j := ((1 : C), mkCoset j (1 : B)) with hq₀
  set x₀ : Coset i := mkCoset i (1 : A) with hx₀
  have hp : gPerm i j hj b ((q₀.1, x₀), q₀.2) = gPerm i j hj b' ((q₀.1, x₀), q₀.2) :=
    congrArg (fun σ : Equiv.Perm (AmalgamSet i j) => σ ((q₀.1, x₀), q₀.2)) h
  have h1a : (gAct j hj b q₀).1 = (gAct j hj b' q₀).1 := by
    simpa [gPerm_apply] using congrArg (fun p : AmalgamSet i j => p.1.1) hp
  have h1b : (gAct j hj b q₀).2 = (gAct j hj b' q₀).2 := by
    simpa [gPerm_apply] using congrArg (fun p : AmalgamSet i j => p.2) hp
  have h1 : gAct j hj b q₀ = gAct j hj b' q₀ := Prod.ext h1a h1b
  have h1' : (eA j hj).symm (b * eA j hj q₀) = (eA j hj).symm (b' * eA j hj q₀) := by
    simpa only [gAct] using h1
  have h2 : b * eA j hj q₀ = b' * eA j hj q₀ := by
    simpa using congrArg (eA j hj) h1'
  exact mul_right_cancel h2

private theorem fHom_injective (i : C →* A) (hi : Injective i) (j : C →* B) :
    Injective (fHom i hi j) := by
  intro a a' h
  exact fPerm_injective i hi j (show fPerm i hi j a = fPerm i hi j a' from h)

private theorem gHom_injective (i : C →* A) (j : C →* B) (hj : Injective j) :
    Injective (gHom i j hj) := by
  intro b b' h
  exact gPerm_injective i j hj (show gPerm i j hj b = gPerm i j hj b' from h)

private theorem fHom_comp_eq (i : C →* A) (hi : Injective i) (j : C →* B) (hj : Injective j) :
    (fHom i hi j).comp i = (gHom i j hj).comp j := by
  apply MonoidHom.ext
  intro c₀
  apply Equiv.Perm.ext
  intro p
  obtain ⟨⟨c, x⟩, y⟩ := p
  show fPerm i hi j (i c₀) ((c, x), y) = gPerm i j hj (j c₀) ((c, x), y)
  simp only [fPerm_apply, gPerm_apply, fAct_i, gAct_j]

end FiniteAmalgam

theorem exists_finite_amalgam_embedding {A B C : Type} [Group A] [Group B] [Group C] [Finite A]
    [Finite B] (i : C →* A) (j : C →* B) (hi : Function.Injective i)
    (hj : Function.Injective j) :
    ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : A →* F) (g : B →* F),
      Function.Injective f ∧ Function.Injective g ∧ f.comp i = g.comp j := by
  classical
  haveI : Finite C := Finite.of_injective i hi
  refine ⟨Equiv.Perm (AmalgamSet i j), inferInstance, inferInstance, fHom i hi j, gHom i j hj,
    fHom_injective i hi j, gHom_injective i j hj, fHom_comp_eq i hi j hj⟩

end CFSG.GroupTheory
