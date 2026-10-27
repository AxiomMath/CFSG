module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AbelianSylowGL

public section

namespace CFSG.AGLEmbeddingD2.PartStab

open Matrix

variable {ι κ : Type*} {F : Type*} [Field F] (s : ι → κ)

@[expose] def IsPartDiag (A : Matrix ι ι F) : Prop := ∀ i j, s i ≠ s j → A i j = 0

theorem isPartDiag_one [DecidableEq ι] : IsPartDiag s (1 : Matrix ι ι F) := fun _ _ h =>
  Matrix.one_apply_ne fun hij => h (hij ▸ rfl)

variable {s} in
theorem IsPartDiag.mul [Fintype ι] {A B : Matrix ι ι F} (hA : IsPartDiag s A) (hB : IsPartDiag s B) :
    IsPartDiag s (A * B) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : s i = s k
  · rw [hB k j (hk ▸ h), mul_zero]
  · rw [hA i k hk, zero_mul]

variable {s} in
theorem IsPartDiag.pow [Fintype ι] [DecidableEq ι] {A : Matrix ι ι F} (hA : IsPartDiag s A) (n : ℕ) :
    IsPartDiag s (A ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact isPartDiag_one s
  | succ n ih => rw [pow_succ]; exact ih.mul hA

variable [Fintype ι] [DecidableEq ι] [Finite F]

variable (F) in
@[expose] def partStab : Subgroup (GL ι F) where
  carrier := {g | IsPartDiag s (g : Matrix ι ι F)}
  one_mem' := isPartDiag_one s
  mul_mem' := fun {a b} ha hb => by
    change IsPartDiag s ((a * b : GL ι F) : Matrix ι ι F)
    rw [Units.val_mul]
    exact IsPartDiag.mul ha hb
  inv_mem' := fun {g} hg => by
    have h0 : 0 < orderOf g := orderOf_pos g
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel h0,
        pow_orderOf_eq_one]
    change IsPartDiag s ((g⁻¹ : GL ι F) : Matrix ι ι F)
    rw [hinv, Units.val_pow_eq_pow_val]
    exact IsPartDiag.pow hg _

theorem mem_partStab {g : GL ι F} : g ∈ partStab F s ↔ IsPartDiag s (g : Matrix ι ι F) :=
  Iff.rfl

variable [DecidableEq κ]

@[expose] def blockMon (k : κ) : partStab F s →* Matrix {i // s i = k} {i // s i = k} F where
  toFun g := ((g : GL ι F) : Matrix ι ι F).submatrix Subtype.val Subtype.val
  map_one' := by
    ext i j
    simp only [OneMemClass.coe_one, Units.val_one, submatrix_apply]
    rw [Matrix.one_apply, Matrix.one_apply]
    simp only [Subtype.ext_iff]
  map_mul' g h := by
    ext i j
    simp only [Subgroup.coe_mul, Units.val_mul, submatrix_apply, Matrix.mul_apply]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun x => s x = k), add_eq_left]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [g.2 i x (by rw [i.2]; exact fun h => x.2 h.symm), zero_mul]

@[expose] def blockHom (k : κ) : partStab F s →* GL {i // s i = k} F :=
  (blockMon s k).toHomUnits

theorem coe_blockHom_apply (k : κ) (g : partStab F s) (i j : {i // s i = k}) :
    ((blockHom s k g : GL {i // s i = k} F) : Matrix _ _ F) i j =
      ((g : GL ι F) : Matrix ι ι F) i j :=
  rfl

theorem injective_pi_blockHom : Function.Injective (MonoidHom.pi (blockHom s (F := F))) := by
  intro g h hgh
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  by_cases hij : s i = s j
  · have := congrArg (fun φ : (∀ k, GL {x // s x = k} F) =>
      ((φ (s i) : GL {x // s x = s i} F) : Matrix {x // s x = s i} {x // s x = s i} F)
        ⟨i, rfl⟩ ⟨j, hij.symm⟩) hgh
    simpa [coe_blockHom_apply] using this
  · rw [g.2 i j hij, h.2 i j hij]

theorem isMulCommutative_of_le_partStab {p : ℕ}
    (h : ∀ (k : κ) (P : Subgroup (GL {i // s i = k} F)), IsPGroup p P → IsMulCommutative P)
    {Q : Subgroup (GL ι F)} (hQ : Q ≤ partStab F s) (hQp : IsPGroup p Q) :
    IsMulCommutative Q := by
  have h' := AbelianSylowGL.isMulCommutative_of_isPGroup_of_injective _
    (injective_pi_blockHom s) (fun R hR => AbelianSylowGL.isMulCommutative_of_isPGroup_pi h hR)
    (P := Q.subgroupOf (partStab F s))
    (hQp.comap_of_injective _ (partStab F s).subtype_injective)
  have e : Q.subgroupOf (partStab F s) ≃* Q := Subgroup.subgroupOfEquivOfLe hQ
  refine ⟨⟨fun a b => ?_⟩⟩
  have := h'.is_comm.comm (e.symm a) (e.symm b)
  simpa using congrArg e this

theorem isMulCommutative_of_isPGroup_five_GL_fintype {σ : Type*} [Fintype σ] [DecidableEq σ]
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hfm : (Odd f ∧ Fintype.card σ < 20) ∨ (f % 4 = 2 ∧ Fintype.card σ < 10) ∨
      (4 ∣ f ∧ Fintype.card σ < 5))
    (P : Subgroup (GL σ F)) (hP : IsPGroup 5 P) : IsMulCommutative P := by
  have := Fintype.ofFinite F
  let e : GL σ F ≃* GL (Fin (Fintype.card σ)) F :=
    Units.mapEquiv (Matrix.reindexAlgEquiv F F (Fintype.equivFin σ)).toMulEquiv
  exact AbelianSylowGL.isMulCommutative_of_isPGroup_five_of_injective_GL_two_pow
    (by rw [← Nat.card_eq_fintype_card]; exact hF) hfm e.toMonoidHom e.injective P hP

end CFSG.AGLEmbeddingD2.PartStab
