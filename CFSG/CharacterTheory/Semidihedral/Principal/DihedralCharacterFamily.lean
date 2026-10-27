module

public import CFSG.CharacterTheory.Blocks.VirtualCharacterCoefficients

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section Powers

variable {G : Type*} [Monoid G] {M : ℕ} [NeZero M]

theorem pow_val_add_of_pow_eq_one {c : G} (hc : c ^ M = 1) (x y : ZMod M) :
    c ^ (x + y).val = c ^ x.val * c ^ y.val := by
  rw [ZMod.val_add, ← pow_add]
  exact pow_eq_pow_of_modEq (Nat.mod_modEq _ _) hc

theorem pow_val_sub_mul_of_pow_eq_one {c : G} (hc : c ^ M = 1) (x y : ZMod M) :
    c ^ (y - x).val * c ^ x.val = c ^ y.val := by
  rw [← pow_val_add_of_pow_eq_one hc, sub_add_cancel]

theorem pow_val_sub_of_mul_eq_one {G : Type*} [CommMonoid G] {c c' : G} (hc : c ^ M = 1)
    (hcc : c' * c = 1) (x y : ZMod M) : c ^ (y - x).val = c' ^ x.val * c ^ y.val := by
  have h1 : c ^ x.val * c' ^ x.val = 1 := by rw [← mul_pow, mul_comm, hcc, one_pow]
  calc c ^ (y - x).val = c ^ (y - x).val * (c ^ x.val * c' ^ x.val) := by rw [h1, mul_one]
    _ = c' ^ x.val * (c ^ (y - x).val * c ^ x.val) := by ac_rfl
    _ = c' ^ x.val * c ^ y.val := by rw [pow_val_sub_mul_of_pow_eq_one hc]

end Powers

section Word

variable {S : Type*} [Group S]

@[expose] def dihedralWord (r s : S) (M : ℕ) : DihedralGroup M → S
  | .r j => r ^ j.val
  | .sr j => s * r ^ j.val

theorem conj_pow_of_dihedral {r s : S} (hs : s * s = 1) (hrel : s * r * s = r⁻¹) (n : ℕ) :
    s * r ^ n * s = (r ^ n)⁻¹ := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have h := conj_pow (a := s) (b := r) (i := n)
  rw [hsinv, hrel, inv_pow] at h
  exact h.symm

@[expose] def dihedralWordHom (r s : S) (M : ℕ) [NeZero M] (hr : r ^ M = 1) (hs : s * s = 1)
    (hrel : s * r * s = r⁻¹) : DihedralGroup M →* S where
  toFun := dihedralWord r s M
  map_one' := by
    rw [DihedralGroup.one_def]
    simp [dihedralWord]
  map_mul' := by
    have hcomm : ∀ n : ℕ, r ^ n * s = s * (r ^ n)⁻¹ := by
      intro n
      rw [← conj_pow_of_dihedral hs hrel n, ← mul_assoc, ← mul_assoc, hs, one_mul]
    have hsub : ∀ x y : ZMod M, r ^ (y - x).val = (r ^ x.val)⁻¹ * r ^ y.val := by
      intro x y
      rw [eq_inv_mul_iff_mul_eq, (Commute.pow_pow_self r _ _).eq,
        pow_val_sub_mul_of_pow_eq_one hr]
    intro a b
    cases a with
    | r x =>
      cases b with
      | r y => simp only [DihedralGroup.r_mul_r, dihedralWord, pow_val_add_of_pow_eq_one hr]
      | sr y =>
        simp only [DihedralGroup.r_mul_sr, dihedralWord, hsub, ← mul_assoc, hcomm]
    | sr x =>
      cases b with
      | r y =>
        simp only [DihedralGroup.sr_mul_r, dihedralWord, pow_val_add_of_pow_eq_one hr, mul_assoc]
      | sr y =>
        simp only [DihedralGroup.sr_mul_sr, dihedralWord, hsub]
        rw [show s * r ^ x.val * (s * r ^ y.val) = (s * r ^ x.val * s) * r ^ y.val by group,
          conj_pow_of_dihedral hs hrel]

theorem dihedralWordHom_bijective {r s : S} {M : ℕ} [NeZero M] [Finite S] (hM : 2 ≤ M)
    (hcard : Nat.card S = 2 * M) (hgen : Subgroup.closure {r, s} = ⊤)
    (hr : r ^ M = 1) (hs : s * s = 1) (hrel : s * r * s = r⁻¹) :
    Function.Bijective (dihedralWordHom r s M hr hs hrel) := by
  have : Fact (1 < M) := ⟨by omega⟩
  have hsurj : Function.Surjective (dihedralWordHom r s M hr hs hrel) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨DihedralGroup.r 1, by simp [dihedralWordHom, dihedralWord, ZMod.val_one]⟩
    · exact ⟨DihedralGroup.sr 0, by simp [dihedralWordHom, dihedralWord]⟩
  exact hsurj.bijective_of_nat_card_le (by rw [DihedralGroup.nat_card, hcard])

@[expose] noncomputable def dihedralCoordinates (r s : S) (M : ℕ) : S → DihedralGroup M :=
  Function.invFun (dihedralWord r s M)

end Word

section Model

@[expose] noncomputable def dihedralZeta (M : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / M)

@[expose] def dihedralRotationSign : Fin 4 → ℂ := ![1, 1, -1, -1]

@[expose] def dihedralReflectionSign : Fin 4 → ℂ := ![1, -1, 1, -1]

@[expose] def dihedralIndexSet (M : ℕ) : Finset ℤ := Finset.Icc 1 ((M : ℤ) / 2 - 1)

@[expose] noncomputable def dihedralRotationMatrix (M : ℕ) (k : ℤ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![dihedralZeta M ^ k, dihedralZeta M ^ (-k)]

@[expose] def dihedralSwapMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

@[expose] def dihedralGroupLinearValue (M : ℕ) (i : Fin 4) : DihedralGroup M → ℂ
  | .r j => dihedralRotationSign i ^ j.val
  | .sr j => dihedralReflectionSign i * dihedralRotationSign i ^ j.val

@[expose] noncomputable def dihedralGroupRotationValue (M : ℕ) (k : ℤ) : DihedralGroup M → ℂ
  | .r j => (dihedralZeta M ^ k) ^ j.val + (dihedralZeta M ^ (-k)) ^ j.val
  | .sr _ => 0

@[expose] noncomputable def dihedralGroupMatrix (M : ℕ) (k : ℤ) :
    DihedralGroup M → Matrix (Fin 2) (Fin 2) ℂ
  | .r j => Matrix.diagonal ![(dihedralZeta M ^ k) ^ j.val, (dihedralZeta M ^ (-k)) ^ j.val]
  | .sr j => !![0, (dihedralZeta M ^ (-k)) ^ j.val; (dihedralZeta M ^ k) ^ j.val, 0]

theorem dihedralZeta_isPrimitiveRoot {M : ℕ} (hM : M ≠ 0) :
    IsPrimitiveRoot (dihedralZeta M) M :=
  Complex.isPrimitiveRoot_exp M hM

theorem dihedralZeta_ne_zero (M : ℕ) : dihedralZeta M ≠ 0 := Complex.exp_ne_zero _

theorem dihedralZeta_zpow_pow {M : ℕ} [NeZero M] (k : ℤ) : (dihedralZeta M ^ k) ^ M = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
    (dihedralZeta_isPrimitiveRoot (NeZero.ne M)).pow_eq_one, one_zpow]

theorem dihedralRotationSign_mul_self (i : Fin 4) :
    dihedralRotationSign i * dihedralRotationSign i = 1 := by
  fin_cases i <;> norm_num [dihedralRotationSign]

theorem dihedralReflectionSign_mul_self (i : Fin 4) :
    dihedralReflectionSign i * dihedralReflectionSign i = 1 := by
  fin_cases i <;> norm_num [dihedralReflectionSign]

theorem dihedralRotationSign_pow {M : ℕ} (hM : Even M) (i : Fin 4) :
    dihedralRotationSign i ^ M = 1 := by
  obtain ⟨m, rfl⟩ := hM
  rw [← two_mul, pow_mul, sq, dihedralRotationSign_mul_self, one_pow]

@[expose] def dihedralGroupLinearHom (M : ℕ) [NeZero M] (hM : Even M) (i : Fin 4) :
    DihedralGroup M →* ℂ where
  toFun := dihedralGroupLinearValue M i
  map_one' := by
    rw [DihedralGroup.one_def]
    simp [dihedralGroupLinearValue]
  map_mul' := by
    have ha := dihedralRotationSign_pow hM i
    have haa := dihedralRotationSign_mul_self i
    have hbb := dihedralReflectionSign_mul_self i
    have hsub : ∀ x y : ZMod M, dihedralRotationSign i ^ (y - x).val =
        dihedralRotationSign i ^ x.val * dihedralRotationSign i ^ y.val :=
      pow_val_sub_of_mul_eq_one ha haa
    intro a b
    cases a with
    | r x =>
      cases b with
      | r y =>
        simp only [DihedralGroup.r_mul_r, dihedralGroupLinearValue,
          pow_val_add_of_pow_eq_one ha]
      | sr y =>
        simp only [DihedralGroup.r_mul_sr, dihedralGroupLinearValue, hsub]
        ring
    | sr x =>
      cases b with
      | r y =>
        simp only [DihedralGroup.sr_mul_r, dihedralGroupLinearValue,
          pow_val_add_of_pow_eq_one ha]
        ring
      | sr y =>
        simp only [DihedralGroup.sr_mul_sr, dihedralGroupLinearValue, hsub]
        linear_combination
          (-(dihedralRotationSign i ^ x.val * dihedralRotationSign i ^ y.val)) * hbb

@[expose] noncomputable def dihedralGroupMatrixHom (M : ℕ) [NeZero M] (k : ℤ) :
    DihedralGroup M →* Matrix (Fin 2) (Fin 2) ℂ where
  toFun := dihedralGroupMatrix M k
  map_one' := by
    rw [DihedralGroup.one_def]
    simp only [dihedralGroupMatrix, ZMod.val_zero, pow_zero]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    fin_cases a <;> rfl
  map_mul' := by
    have hc := dihedralZeta_zpow_pow (M := M) k
    have hc' := dihedralZeta_zpow_pow (M := M) (-k)
    have hcc : dihedralZeta M ^ (-k) * dihedralZeta M ^ k = 1 := by
      rw [← zpow_add₀ (dihedralZeta_ne_zero M), neg_add_cancel, zpow_zero]
    have hsub : ∀ (c c' : ℂ), c ^ M = 1 → c' * c = 1 → ∀ x y : ZMod M,
        c ^ (y - x).val = c' ^ x.val * c ^ y.val :=
      fun c c' hc hcc => pow_val_sub_of_mul_eq_one hc hcc
    have hcc' : dihedralZeta M ^ k * dihedralZeta M ^ (-k) = 1 := by rw [mul_comm, hcc]
    intro a b
    cases a with
    | r x =>
      cases b with
      | r y =>
        simp only [DihedralGroup.r_mul_r, dihedralGroupMatrix, Matrix.diagonal_mul_diagonal,
          pow_val_add_of_pow_eq_one hc, pow_val_add_of_pow_eq_one hc']
        congr 1
        ext a
        fin_cases a <;> simp
      | sr y =>
        simp only [DihedralGroup.r_mul_sr, dihedralGroupMatrix, hsub _ _ hc hcc,
          hsub _ _ hc' hcc']
        ext a b
        fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    | sr x =>
      cases b with
      | r y =>
        simp only [DihedralGroup.sr_mul_r, dihedralGroupMatrix, pow_val_add_of_pow_eq_one hc,
          pow_val_add_of_pow_eq_one hc']
        ext a b
        fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      | sr y =>
        simp only [DihedralGroup.sr_mul_sr, dihedralGroupMatrix, hsub _ _ hc hcc,
          hsub _ _ hc' hcc']
        ext a b
        fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] noncomputable def dihedralGroupRepresentation (M : ℕ) [NeZero M] (k : ℤ) :
    Representation ℂ (DihedralGroup M) (Fin 2 → ℂ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] _).toRingEquiv.toMonoidHom.comp
    (dihedralGroupMatrixHom M k)

theorem dihedralGroupRepresentation_apply (M : ℕ) [NeZero M] (k : ℤ) (d : DihedralGroup M) :
    dihedralGroupRepresentation M k d = Matrix.toLin' (dihedralGroupMatrix M k d) := rfl

theorem dihedralGroupRepresentation_character (M : ℕ) [NeZero M] (k : ℤ) :
    (dihedralGroupRepresentation M k).character = dihedralGroupRotationValue M k := by
  funext d
  rw [Representation.character, dihedralGroupRepresentation_apply, Matrix.trace_toLin'_eq]
  cases d with
  | r j => simp [dihedralGroupMatrix, dihedralGroupRotationValue]
  | sr j => simp [dihedralGroupMatrix, dihedralGroupRotationValue]

theorem pow_val_intCast_of_pow_eq_one {M : ℕ} [NeZero M] {c : ℂ} (hc0 : c ≠ 0)
    (hc : c ^ M = 1) (j : ℤ) : c ^ ((j : ZMod M).val) = c ^ j := by
  rw [← zpow_natCast, ZMod.val_intCast]
  conv_rhs => rw [← Int.emod_add_mul_ediv j M]
  rw [zpow_add₀ hc0, zpow_mul, zpow_natCast, hc, one_zpow, mul_one]

theorem dihedralRotationSign_ne_zero (i : Fin 4) : dihedralRotationSign i ≠ 0 := by
  fin_cases i <;> norm_num [dihedralRotationSign]

end Model

section Characters

variable {S : Type*} [Group S]

@[expose] noncomputable def dihedralLinearCharacter (r s : S) (M : ℕ) (i : Fin 4) : S → ℂ :=
  fun x => dihedralGroupLinearValue M i (dihedralCoordinates r s M x)

@[expose] noncomputable def dihedralRotationCharacter (r s : S) (M : ℕ) (k : ℤ) : S → ℂ :=
  fun x => dihedralGroupRotationValue M k (dihedralCoordinates r s M x)

@[expose] noncomputable def dihedralTheta (r s : S) (M : ℕ) : S → ℂ :=
  dihedralLinearCharacter r s M 0 + dihedralLinearCharacter r s M 1 -
    dihedralLinearCharacter r s M 2 - dihedralLinearCharacter r s M 3

@[expose] noncomputable def dihedralEta (r s : S) (M : ℕ) (k : ℤ) : S → ℂ :=
  dihedralLinearCharacter r s M 0 + dihedralLinearCharacter r s M 1 -
    dihedralRotationCharacter r s M k

theorem dihedralLinearCharacter_zero (r s : S) (M : ℕ) :
    dihedralLinearCharacter r s M 0 = 1 := by
  funext x
  simp only [dihedralLinearCharacter, Pi.one_apply]
  cases dihedralCoordinates r s M x <;>
    simp [dihedralGroupLinearValue, dihedralRotationSign, dihedralReflectionSign]

variable {r s : S} {M : ℕ}

theorem exists_dihedral_mulEquiv [Finite S] (hM : 2 ≤ M) (hcard : Nat.card S = 2 * M)
    (hgen : Subgroup.closure {r, s} = ⊤) (hr : r ^ M = 1) (hs : s * s = 1)
    (hrel : s * r * s = r⁻¹) :
    ∃ e : DihedralGroup M ≃* S, (∀ d, e d = dihedralWord r s M d) ∧
      dihedralCoordinates r s M = e.symm := by
  have : NeZero M := ⟨by omega⟩
  have hbij := dihedralWordHom_bijective hM hcard hgen hr hs hrel
  refine ⟨MulEquiv.ofBijective _ hbij, fun d => rfl, ?_⟩
  funext x
  rw [MulEquiv.eq_symm_apply]
  have hinj : Function.Injective (dihedralWord r s M) := hbij.injective
  exact Function.invFun_eq (hbij.surjective x)

section Equiv

variable (e : DihedralGroup M ≃* S) (he : ∀ d, e d = dihedralWord r s M d)
include he

theorem dihedral_symm_r [Fact (1 < M)] : e.symm r = DihedralGroup.r 1 := by
  rw [MulEquiv.symm_apply_eq, he]
  simp [dihedralWord, ZMod.val_one]

theorem dihedral_symm_s : e.symm s = DihedralGroup.sr 0 := by
  rw [MulEquiv.symm_apply_eq, he]
  simp [dihedralWord]

theorem dihedral_symm_r_zpow [Fact (1 < M)] (j : ℤ) : e.symm (r ^ j) = DihedralGroup.r j := by
  rw [map_zpow, dihedral_symm_r e he, DihedralGroup.r_one_zpow]

theorem dihedral_symm_s_mul_r_zpow [Fact (1 < M)] (j : ℤ) :
    e.symm (s * r ^ j) = DihedralGroup.sr j := by
  rw [map_mul, dihedral_symm_r_zpow e he, dihedral_symm_s e he, DihedralGroup.sr_mul_r,
    zero_add]

variable (hcoord : dihedralCoordinates r s M = e.symm)
include hcoord

theorem dihedralLinearCharacter_r_zpow [Fact (1 < M)] (hM : Even M) (i : Fin 4) (j : ℤ) :
    dihedralLinearCharacter r s M i (r ^ j) = dihedralRotationSign i ^ j := by
  have : NeZero M := ⟨by have := (Fact.out : 1 < M); omega⟩
  simp only [dihedralLinearCharacter, hcoord, dihedral_symm_r_zpow e he, dihedralGroupLinearValue]
  exact pow_val_intCast_of_pow_eq_one (dihedralRotationSign_ne_zero i)
    (dihedralRotationSign_pow hM i) j

theorem dihedralLinearCharacter_s_mul_r_zpow [Fact (1 < M)] (hM : Even M) (i : Fin 4)
    (j : ℤ) : dihedralLinearCharacter r s M i (s * r ^ j) =
      dihedralReflectionSign i * dihedralRotationSign i ^ j := by
  have : NeZero M := ⟨by have := (Fact.out : 1 < M); omega⟩
  simp only [dihedralLinearCharacter, hcoord, dihedral_symm_s_mul_r_zpow e he,
    dihedralGroupLinearValue]
  rw [pow_val_intCast_of_pow_eq_one (dihedralRotationSign_ne_zero i)
    (dihedralRotationSign_pow hM i) j]

theorem dihedralRotationCharacter_r_zpow [Fact (1 < M)] (k j : ℤ) :
    dihedralRotationCharacter r s M k (r ^ j) =
      dihedralZeta M ^ (k * j) + dihedralZeta M ^ (-(k * j)) := by
  have : NeZero M := ⟨by have := (Fact.out : 1 < M); omega⟩
  have hz := dihedralZeta_ne_zero M
  simp only [dihedralRotationCharacter, hcoord, dihedral_symm_r_zpow e he,
    dihedralGroupRotationValue]
  rw [pow_val_intCast_of_pow_eq_one (zpow_ne_zero _ hz) (dihedralZeta_zpow_pow k) j,
    pow_val_intCast_of_pow_eq_one (zpow_ne_zero _ hz) (dihedralZeta_zpow_pow (-k)) j,
    ← zpow_mul, ← zpow_mul, neg_mul]

theorem dihedralRotationCharacter_s_mul_r_zpow [Fact (1 < M)] (k j : ℤ) :
    dihedralRotationCharacter r s M k (s * r ^ j) = 0 := by
  simp only [dihedralRotationCharacter, hcoord, dihedral_symm_s_mul_r_zpow e he,
    dihedralGroupRotationValue]

theorem exists_dihedral_linear_representation [Fact (1 < M)] (hM : Even M) (i : Fin 4) :
    ∃ R : Representation ℂ S ℂ, R r = dihedralRotationSign i • LinearMap.id ∧
      R s = dihedralReflectionSign i • LinearMap.id ∧
      R.character = dihedralLinearCharacter r s M i := by
  have : NeZero M := ⟨by have := (Fact.out : 1 < M); omega⟩
  refine ⟨scalarHomRepresentation ((dihedralGroupLinearHom M hM i).comp e.symm.toMonoidHom),
    ?_, ?_, ?_⟩
  · change dihedralGroupLinearValue M i (e.symm r) • (1 : Module.End ℂ ℂ) = _
    rw [dihedral_symm_r e he]
    simp [dihedralGroupLinearValue, ZMod.val_one, Module.End.one_eq_id]
  · change dihedralGroupLinearValue M i (e.symm s) • (1 : Module.End ℂ ℂ) = _
    rw [dihedral_symm_s e he]
    simp [dihedralGroupLinearValue, Module.End.one_eq_id]
  · rw [scalarHomRepresentation_character]
    funext x
    simp only [dihedralLinearCharacter, hcoord]
    rfl

theorem exists_dihedral_rotation_representation [Fact (1 < M)] (k : ℤ) :
    ∃ ρ : Representation ℂ S (Fin 2 → ℂ), ρ r = Matrix.toLin' (dihedralRotationMatrix M k) ∧
      ρ s = Matrix.toLin' dihedralSwapMatrix ∧
      ρ.character = dihedralRotationCharacter r s M k := by
  have : NeZero M := ⟨by have := (Fact.out : 1 < M); omega⟩
  refine ⟨(dihedralGroupRepresentation M k).comp e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · change dihedralGroupRepresentation M k (e.symm r) = _
    rw [dihedral_symm_r e he, dihedralGroupRepresentation_apply]
    simp [dihedralGroupMatrix, dihedralRotationMatrix, ZMod.val_one]
  · change dihedralGroupRepresentation M k (e.symm s) = _
    rw [dihedral_symm_s e he, dihedralGroupRepresentation_apply]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;> simp [dihedralGroupMatrix, dihedralSwapMatrix]
  · funext x
    change (dihedralGroupRepresentation M k).character (e.symm x) = _
    rw [dihedralGroupRepresentation_character]
    simp only [dihedralRotationCharacter, hcoord]

end Equiv

end Characters

section Irreducible

theorem representation_complex_line_isIrreducible {G : Type*} [Group G]
    (R : Representation ℂ G ℂ) : R.IsIrreducible := by
  change IsSimpleOrder (Subrepresentation R)
  have hnontrivial : (⊥ : Subrepresentation R) ≠ ⊤ := by
    intro hequal
    have hmem : (1 : ℂ) ∈ (⊥ : Subrepresentation R) := by
      rw [hequal]
      trivial
    exact one_ne_zero hmem
  let : Nontrivial (Subrepresentation R) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro W
  obtain hbot | htop := eq_bot_or_eq_top W.toSubmodule
  · exact Or.inl (Subrepresentation.ext hbot)
  · exact Or.inr (Subrepresentation.ext htop)

theorem representation_swap_diagonal_isIrreducible {G : Type*} [Group G]
    (ρ : Representation ℂ G (Fin 2 → ℂ)) {r s : G} {c c' : ℂ} (hne : c ≠ c')
    (hr : ρ r = Matrix.toLin' (Matrix.diagonal ![c, c']))
    (hs : ρ s = Matrix.toLin' dihedralSwapMatrix) : ρ.IsIrreducible := by
  change IsSimpleOrder (Subrepresentation ρ)
  have hnontrivial : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hequal
    have hmem : (![1, 0] : Fin 2 → ℂ) ∈ (⊥ : Subrepresentation ρ) := by
      rw [hequal]
      trivial
    have h0 : (![1, 0] : Fin 2 → ℂ) = 0 := hmem
    have := congrFun h0 0
    simp at this
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  have hrv : ∀ v : Fin 2 → ℂ, ρ r v = ![c * v 0, c' * v 1] := by
    intro v
    rw [hr, Matrix.toLin'_apply]
    funext a
    fin_cases a <;> simp [Matrix.mulVec_diagonal]
  have hsv : ∀ v : Fin 2 → ℂ, ρ s v = ![v 1, v 0] := by
    intro v
    rw [hs, Matrix.toLin'_apply]
    funext a
    fin_cases a <;> simp [dihedralSwapMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  intro W
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.ext hW)
  right
  apply Subrepresentation.ext
  show W.toSubmodule = ⊤
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hmemr : ρ r w ∈ W.toSubmodule := W.apply_mem_toSubmodule r hwW
  have hmems : ∀ v ∈ W.toSubmodule, ρ s v ∈ W.toSubmodule :=
    fun v hv => W.apply_mem_toSubmodule s hv
  have hne' : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have hne'' : c' - c ≠ 0 := sub_ne_zero.mpr hne.symm
  have hv0 : (![(c' - c) * w 0, 0] : Fin 2 → ℂ) ∈ W.toSubmodule := by
    have := W.toSubmodule.sub_mem (W.toSubmodule.smul_mem c' hwW) hmemr
    convert this using 1
    rw [hrv]
    funext a
    fin_cases a <;> simp [sub_mul]
  have hv1 : (![0, (c - c') * w 1] : Fin 2 → ℂ) ∈ W.toSubmodule := by
    have := W.toSubmodule.sub_mem (W.toSubmodule.smul_mem c hwW) hmemr
    convert this using 1
    rw [hrv]
    funext a
    fin_cases a <;> simp [sub_mul]
  have hswap0 : (![1, 0] : Fin 2 → ℂ) ∈ W.toSubmodule → (![0, 1] : Fin 2 → ℂ) ∈ W.toSubmodule := by
    intro h
    have := hmems _ h
    rw [hsv] at this
    simpa using this
  have hswap1 : (![0, 1] : Fin 2 → ℂ) ∈ W.toSubmodule → (![1, 0] : Fin 2 → ℂ) ∈ W.toSubmodule := by
    intro h
    have := hmems _ h
    rw [hsv] at this
    simpa using this
  have hbasis : (![1, 0] : Fin 2 → ℂ) ∈ W.toSubmodule ∧ (![0, 1] : Fin 2 → ℂ) ∈ W.toSubmodule := by
    by_cases hw00 : w 0 = 0
    · have hw1 : w 1 ≠ 0 := by
        intro hw1
        apply hw0
        funext a
        fin_cases a <;> simp [hw00, hw1]
      have h1 : (![0, 1] : Fin 2 → ℂ) ∈ W.toSubmodule := by
        have := W.toSubmodule.smul_mem ((c - c') * w 1)⁻¹ hv1
        convert this using 1
        funext a
        fin_cases a
        · simp
        · simp
          field_simp
      exact ⟨hswap1 h1, h1⟩
    · have h0 : (![1, 0] : Fin 2 → ℂ) ∈ W.toSubmodule := by
        have := W.toSubmodule.smul_mem ((c' - c) * w 0)⁻¹ hv0
        convert this using 1
        funext a
        fin_cases a
        · simp
          field_simp
        · simp
      exact ⟨h0, hswap0 h0⟩
  rw [eq_top_iff]
  intro v _
  have hv : v = v 0 • (![1, 0] : Fin 2 → ℂ) + v 1 • (![0, 1] : Fin 2 → ℂ) := by
    funext a
    fin_cases a <;> simp
  rw [hv]
  exact W.toSubmodule.add_mem (W.toSubmodule.smul_mem _ hbasis.1)
    (W.toSubmodule.smul_mem _ hbasis.2)

theorem dihedralZeta_add_inv_injective {M : ℕ} (hM : 2 ≤ M) {k l : ℤ}
    (hk : k ∈ dihedralIndexSet M) (hl : l ∈ dihedralIndexSet M)
    (h : dihedralZeta M ^ k + dihedralZeta M ^ (-k) =
      dihedralZeta M ^ l + dihedralZeta M ^ (-l)) : k = l := by
  have hprim := dihedralZeta_isPrimitiveRoot (M := M) (by omega)
  have hz := dihedralZeta_ne_zero M
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  obtain ⟨hl1, hl2⟩ := Finset.mem_Icc.mp hl
  have e1 : dihedralZeta M ^ k * dihedralZeta M ^ (-(k + l)) = dihedralZeta M ^ (-l) := by
    rw [← zpow_add₀ hz]
    congr 1
    ring
  have e2 : dihedralZeta M ^ l * dihedralZeta M ^ (-(k + l)) = dihedralZeta M ^ (-k) := by
    rw [← zpow_add₀ hz]
    congr 1
    ring
  have hfac : (dihedralZeta M ^ k - dihedralZeta M ^ l) *
      (1 - dihedralZeta M ^ (-(k + l))) = 0 := by
    linear_combination h - e1 + e2
  rcases mul_eq_zero.mp hfac with h1 | h1
  · have h2 : dihedralZeta M ^ (k - l) = 1 := by
      rw [zpow_sub₀ hz, sub_eq_zero.mp h1, div_self (zpow_ne_zero _ hz)]
    have hdvd := (hprim.zpow_eq_one_iff_dvd _).mp h2
    have := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by omega, by omega⟩)
    omega
  · have h2 : dihedralZeta M ^ (-(k + l)) = 1 := (sub_eq_zero.mp h1).symm
    have hdvd := (hprim.zpow_eq_one_iff_dvd _).mp h2
    have := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by omega, by omega⟩)
    omega

theorem dihedralZeta_zpow_ne_neg {M : ℕ} (hM : 2 ≤ M) {k : ℤ} (hk : k ∈ dihedralIndexSet M) :
    dihedralZeta M ^ k ≠ dihedralZeta M ^ (-k) := by
  intro h
  have hprim := dihedralZeta_isPrimitiveRoot (M := M) (by omega)
  have hz := dihedralZeta_ne_zero M
  obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
  have h2 : dihedralZeta M ^ (k - -k) = 1 := by
    rw [zpow_sub₀ hz, h, div_self (zpow_ne_zero _ hz)]
  have hdvd := (hprim.zpow_eq_one_iff_dvd _).mp h2
  have := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

theorem representation_eq_of_generators {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    {r s : G} (hgen : Subgroup.closure {r, s} = ⊤) {R R' : Representation ℂ G V}
    (hr : R r = R' r) (hs : R s = R' s) : R = R' := by
  apply MonoidHom.eq_of_eqOn_dense hgen
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hr
  · exact hs

end Irreducible

section InnerProduct

variable {G : Type} [Group G] [Fintype G]

private theorem innerProduct_add_left (f g h : G → ℂ) :
    BlocksInnerProduct (f + g) h = BlocksInnerProduct f h + BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.add_apply, add_mul]

private theorem innerProduct_sub_left (f g h : G → ℂ) :
    BlocksInnerProduct (f - g) h = BlocksInnerProduct f h - BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.sub_apply, sub_mul]

private theorem innerProduct_add_right (f g h : G → ℂ) :
    BlocksInnerProduct f (g + h) = BlocksInnerProduct f g + BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.add_apply, map_add, mul_add]

private theorem innerProduct_sub_right (f g h : G → ℂ) :
    BlocksInnerProduct f (g - h) = BlocksInnerProduct f g - BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.sub_apply, map_sub, mul_sub]

theorem blocksInnerProduct_of_mem_blocksIrr {f g : G → ℂ} (hf : f ∈ BlocksIrr G)
    (hg : g ∈ BlocksIrr G) : BlocksInnerProduct f g = if f = g then 1 else 0 := by
  have h := blocksInnerProduct_irreducible (⟨f, hf⟩ : BlocksIrr G) ⟨g, hg⟩
  simpa only [Subtype.mk.injEq] using h

end InnerProduct

section Main

variable {S : Type} [Group S] [Fintype S] {r s : S} {M : ℕ}

theorem dihedral_explicit_character_family (hM : 2 ≤ M) (hEven : Even M)
    (hcard : Nat.card S = 2 * M) (hgen : Subgroup.closure {r, s} = ⊤) (hr : orderOf r = M)
    (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹) :
    (∀ i : Fin 4,
      (∃! R : Representation ℂ S ℂ, R r = dihedralRotationSign i • LinearMap.id ∧
        R s = dihedralReflectionSign i • LinearMap.id) ∧
      ∀ R : Representation ℂ S ℂ, R r = dihedralRotationSign i • LinearMap.id →
        R s = dihedralReflectionSign i • LinearMap.id →
        R.IsIrreducible ∧ R.character = dihedralLinearCharacter r s M i) ∧
    (∀ k ∈ dihedralIndexSet M,
      (∃! ρ : Representation ℂ S (Fin 2 → ℂ),
        ρ r = Matrix.toLin' (dihedralRotationMatrix M k) ∧
        ρ s = Matrix.toLin' dihedralSwapMatrix) ∧
      ∀ ρ : Representation ℂ S (Fin 2 → ℂ),
        ρ r = Matrix.toLin' (dihedralRotationMatrix M k) →
        ρ s = Matrix.toLin' dihedralSwapMatrix →
        ρ.IsIrreducible ∧ ρ.character = dihedralRotationCharacter r s M k) ∧
    (∀ i : Fin 4, dihedralLinearCharacter r s M i ∈ BlocksIrr S) ∧
    (∀ k ∈ dihedralIndexSet M, dihedralRotationCharacter r s M k ∈ BlocksIrr S) ∧
    Function.Injective (dihedralLinearCharacter r s M) ∧
    Set.InjOn (dihedralRotationCharacter r s M) (dihedralIndexSet M) ∧
    (∀ i : Fin 4, ∀ k ∈ dihedralIndexSet M,
      dihedralLinearCharacter r s M i ≠ dihedralRotationCharacter r s M k) ∧
    dihedralLinearCharacter r s M 0 = 1 ∧
    (∀ (i : Fin 4) (j : ℤ),
      dihedralLinearCharacter r s M i (r ^ j) = dihedralRotationSign i ^ j ∧
      dihedralLinearCharacter r s M i (s * r ^ j) =
        dihedralReflectionSign i * dihedralRotationSign i ^ j) ∧
    (∀ k j : ℤ,
      dihedralRotationCharacter r s M k (r ^ j) =
        dihedralZeta M ^ (k * j) + dihedralZeta M ^ (-(k * j)) ∧
      dihedralRotationCharacter r s M k (s * r ^ j) = 0) ∧
    dihedralTheta r s M ∈ BlocksVChar S ∧
    (∀ k ∈ dihedralIndexSet M, dihedralEta r s M k ∈ BlocksVChar S) ∧
    dihedralTheta r s M 1 = 0 ∧ (∀ j : ℤ, dihedralTheta r s M (s * r ^ j) = 0) ∧
    (∀ k : ℤ, dihedralEta r s M k 1 = 0 ∧ ∀ j : ℤ, dihedralEta r s M k (s * r ^ j) = 0) ∧
    BlocksInnerProduct (dihedralTheta r s M) (dihedralTheta r s M) = 4 ∧
    BlocksInnerProduct (dihedralTheta r s M) 1 = 1 ∧
    (∀ k ∈ dihedralIndexSet M, BlocksInnerProduct (dihedralEta r s M k) 1 = 1) ∧
    (∀ k ∈ dihedralIndexSet M,
      BlocksInnerProduct (dihedralTheta r s M) (dihedralEta r s M k) = 2) ∧
    ∀ k ∈ dihedralIndexSet M, ∀ l ∈ dihedralIndexSet M,
      BlocksInnerProduct (dihedralEta r s M k) (dihedralEta r s M l) =
        2 + if k = l then 1 else 0 := by
  have : NeZero M := ⟨by omega⟩
  have : Fact (1 < M) := ⟨by omega⟩
  have hrM : r ^ M = 1 := hr ▸ pow_orderOf_eq_one r
  have hss : s * s = 1 := by rw [← sq, ← hs, pow_orderOf_eq_one]
  obtain ⟨e, he, hcoord⟩ := exists_dihedral_mulEquiv hM hcard hgen hrM hss hrel
  have hφr := dihedralLinearCharacter_r_zpow e he hcoord hEven
  have hφs := dihedralLinearCharacter_s_mul_r_zpow e he hcoord hEven
  have hγr := dihedralRotationCharacter_r_zpow (M := M) e he hcoord
  have hγs := dihedralRotationCharacter_s_mul_r_zpow (M := M) e he hcoord
  have hφ1 : ∀ i, dihedralLinearCharacter r s M i 1 = 1 := by
    intro i
    simpa using hφr i 0
  have hφr1 : ∀ i, dihedralLinearCharacter r s M i r = dihedralRotationSign i := by
    intro i
    simpa using hφr i 1
  have hφs1 : ∀ i, dihedralLinearCharacter r s M i s = dihedralReflectionSign i := by
    intro i
    simpa using hφs i 0
  have hγ1 : ∀ k, dihedralRotationCharacter r s M k 1 = 2 := by
    intro k
    have := hγr k 0
    simp only [zpow_zero, mul_zero, neg_zero] at this
    rw [this]
    norm_num
  have hγr1 : ∀ k, dihedralRotationCharacter r s M k r =
      dihedralZeta M ^ k + dihedralZeta M ^ (-k) := by
    intro k
    simpa using hγr k 1
  have hlin : ∀ i : Fin 4, ∀ R : Representation ℂ S ℂ,
      R r = dihedralRotationSign i • LinearMap.id →
      R s = dihedralReflectionSign i • LinearMap.id →
      R.IsIrreducible ∧ R.character = dihedralLinearCharacter r s M i := by
    intro i R hRr hRs
    obtain ⟨R₀, hR₀r, hR₀s, hR₀⟩ := exists_dihedral_linear_representation e he hcoord hEven i
    refine ⟨representation_complex_line_isIrreducible R, ?_⟩
    rw [representation_eq_of_generators hgen (hRr.trans hR₀r.symm) (hRs.trans hR₀s.symm), hR₀]
  have hrot : ∀ k ∈ dihedralIndexSet M, ∀ ρ : Representation ℂ S (Fin 2 → ℂ),
      ρ r = Matrix.toLin' (dihedralRotationMatrix M k) →
      ρ s = Matrix.toLin' dihedralSwapMatrix →
      ρ.IsIrreducible ∧ ρ.character = dihedralRotationCharacter r s M k := by
    intro k hk ρ hρr hρs
    obtain ⟨ρ₀, hρ₀r, hρ₀s, hρ₀⟩ := exists_dihedral_rotation_representation e he hcoord k
    refine ⟨representation_swap_diagonal_isIrreducible ρ (dihedralZeta_zpow_ne_neg hM hk) hρr
      hρs, ?_⟩
    rw [representation_eq_of_generators hgen (hρr.trans hρ₀r.symm) (hρs.trans hρ₀s.symm), hρ₀]
  have hφirr : ∀ i, dihedralLinearCharacter r s M i ∈ BlocksIrr S := by
    intro i
    obtain ⟨R₀, hR₀r, hR₀s, hR₀⟩ := exists_dihedral_linear_representation e he hcoord hEven i
    exact ⟨ℂ, inferInstance, inferInstance, inferInstance, R₀,
      representation_complex_line_isIrreducible R₀, hR₀⟩
  have hγirr : ∀ k ∈ dihedralIndexSet M, dihedralRotationCharacter r s M k ∈ BlocksIrr S := by
    intro k hk
    obtain ⟨ρ₀, hρ₀r, hρ₀s, hρ₀⟩ := exists_dihedral_rotation_representation e he hcoord k
    exact ⟨Fin 2 → ℂ, inferInstance, inferInstance, inferInstance, ρ₀,
      (hrot k hk ρ₀ hρ₀r hρ₀s).1, hρ₀⟩
  have hφinj : Function.Injective (dihedralLinearCharacter r s M) := by
    intro i j hij
    have h1 := congrFun hij r
    have h2 := congrFun hij s
    rw [hφr1, hφr1] at h1
    rw [hφs1, hφs1] at h2
    fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | (norm_num [dihedralRotationSign] at h1; done)
      | norm_num [dihedralReflectionSign] at h2
  have hγinj : Set.InjOn (dihedralRotationCharacter r s M) (dihedralIndexSet M) := by
    intro k hk l hl hkl
    have h := congrFun hkl r
    rw [hγr1, hγr1] at h
    exact dihedralZeta_add_inv_injective hM hk hl h
  have hφγ : ∀ i : Fin 4, ∀ k ∈ dihedralIndexSet M,
      dihedralLinearCharacter r s M i ≠ dihedralRotationCharacter r s M k := by
    intro i k _ h
    have h1 := congrFun h 1
    rw [hφ1, hγ1] at h1
    norm_num at h1
  have hφφ : ∀ i j : Fin 4, BlocksInnerProduct (dihedralLinearCharacter r s M i)
      (dihedralLinearCharacter r s M j) = if i = j then 1 else 0 := by
    intro i j
    rw [blocksInnerProduct_of_mem_blocksIrr (hφirr i) (hφirr j)]
    exact if_congr hφinj.eq_iff rfl rfl
  have hφγ' : ∀ i : Fin 4, ∀ k ∈ dihedralIndexSet M, BlocksInnerProduct
      (dihedralLinearCharacter r s M i) (dihedralRotationCharacter r s M k) = 0 := by
    intro i k hk
    rw [blocksInnerProduct_of_mem_blocksIrr (hφirr i) (hγirr k hk)]
    exact ite_eq_right_iff.mpr fun h => absurd h (hφγ i k hk)
  have hγφ : ∀ i : Fin 4, ∀ k ∈ dihedralIndexSet M, BlocksInnerProduct
      (dihedralRotationCharacter r s M k) (dihedralLinearCharacter r s M i) = 0 := by
    intro i k hk
    rw [blocksInnerProduct_of_mem_blocksIrr (hγirr k hk) (hφirr i)]
    exact ite_eq_right_iff.mpr fun h => absurd h.symm (hφγ i k hk)
  have hγγ : ∀ k ∈ dihedralIndexSet M, ∀ l ∈ dihedralIndexSet M, BlocksInnerProduct
      (dihedralRotationCharacter r s M k) (dihedralRotationCharacter r s M l) =
        if k = l then 1 else 0 := by
    intro k hk l hl
    rw [blocksInnerProduct_of_mem_blocksIrr (hγirr k hk) (hγirr l hl)]
    exact if_congr ⟨fun h => hγinj hk hl h, fun h => h ▸ rfl⟩ rfl rfl
  have hone : (1 : S → ℂ) = dihedralLinearCharacter r s M 0 :=
    (dihedralLinearCharacter_zero r s M).symm
  refine ⟨fun i => ⟨?_, hlin i⟩, fun k hk => ⟨?_, hrot k hk⟩, hφirr, hγirr, hφinj, hγinj, hφγ,
    dihedralLinearCharacter_zero r s M, fun i j => ⟨hφr i j, hφs i j⟩,
    fun k j => ⟨hγr k j, hγs k j⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨R₀, hR₀r, hR₀s, _⟩ := exists_dihedral_linear_representation e he hcoord hEven i
    exact ⟨R₀, ⟨hR₀r, hR₀s⟩, fun R hR =>
      representation_eq_of_generators hgen (hR.1.trans hR₀r.symm) (hR.2.trans hR₀s.symm)⟩
  · obtain ⟨ρ₀, hρ₀r, hρ₀s, _⟩ := exists_dihedral_rotation_representation e he hcoord k
    exact ⟨ρ₀, ⟨hρ₀r, hρ₀s⟩, fun ρ hρ =>
      representation_eq_of_generators hgen (hρ.1.trans hρ₀r.symm) (hρ.2.trans hρ₀s.symm)⟩
  · exact AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (AddSubgroup.add_mem _
      (AddSubgroup.subset_closure (hφirr 0)) (AddSubgroup.subset_closure (hφirr 1)))
      (AddSubgroup.subset_closure (hφirr 2))) (AddSubgroup.subset_closure (hφirr 3))
  · intro k hk
    exact AddSubgroup.sub_mem _ (AddSubgroup.add_mem _
      (AddSubgroup.subset_closure (hφirr 0)) (AddSubgroup.subset_closure (hφirr 1)))
      (AddSubgroup.subset_closure (hγirr k hk))
  · simp only [dihedralTheta, Pi.add_apply, Pi.sub_apply, hφ1]
    norm_num
  · intro j
    simp only [dihedralTheta, Pi.add_apply, Pi.sub_apply, hφs]
    simp only [dihedralRotationSign, dihedralReflectionSign]
    norm_num
  · intro k
    refine ⟨?_, fun j => ?_⟩
    · simp only [dihedralEta, Pi.add_apply, Pi.sub_apply, hφ1, hγ1]
      norm_num
    · simp only [dihedralEta, Pi.add_apply, Pi.sub_apply, hφs, hγs]
      simp only [dihedralRotationSign, dihedralReflectionSign]
      norm_num
  · simp only [dihedralTheta, innerProduct_add_left, innerProduct_sub_left,
      innerProduct_add_right, innerProduct_sub_right, hφφ]
    norm_num
  · rw [hone]
    simp only [dihedralTheta, innerProduct_add_left, innerProduct_sub_left, hφφ]
    norm_num
  · intro k hk
    rw [hone]
    simp only [dihedralEta, innerProduct_add_left, innerProduct_sub_left, hφφ, hγφ 0 k hk]
    norm_num
  · intro k hk
    simp only [dihedralTheta, dihedralEta, innerProduct_add_left, innerProduct_sub_left,
      innerProduct_add_right, innerProduct_sub_right, hφφ, hφγ' _ k hk]
    norm_num
  · intro k hk l hl
    simp only [dihedralEta, innerProduct_add_left, innerProduct_sub_left,
      innerProduct_add_right, innerProduct_sub_right, hφφ, hφγ' _ l hl, hγφ _ k hk,
      hγγ k hk l hl]
    norm_num

end Main

end CFSG.Semidihedral.Principal
