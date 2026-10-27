module

public import CFSG.HardMathSupport.Foote.E27.LieTwo.MatTable
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Orth

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)

@[expose] def OrthSet : Set (GL ι (ZMod 2)) :=
  {A | ∀ v, Q ((A : Matrix ι ι (ZMod 2)) *ᵥ v) = Q v}

@[expose] def OrthN : Subgroup (GL ι (ZMod 2)) := Subgroup.closure (OrthSet Q)

theorem mem_OrthN_iff {A : GL ι (ZMod 2)} : A ∈ OrthN Q ↔ A ∈ OrthSet Q := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro v; simp
  | mul x y _ _ hx hy =>
    intro v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    intro v
    have h := hx (((x⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm

variable {d : ℕ} (e : ι ≃ Fin d)

@[expose] noncomputable def matO : OrthN Q →* M2 d :=
  (((Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) e).toRingEquiv).toMonoidHom).comp
    ((Units.coeHom _).comp (OrthN Q).subtype)

theorem matO_apply (x : OrthN Q) :
    matO Q e x = ((x : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)).submatrix e.symm e.symm := rfl

theorem matO_injective : Function.Injective (matO Q e) := by
  intro x y h
  rw [matO_apply, matO_apply] at h
  have h2 := congrArg (fun M : M2 d => M.submatrix e e) h
  simp only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Subtype.ext (Units.ext h2)

theorem exists_of_orth {X Xi : M2 d} (h1 : X * Xi = 1) (h2 : Xi * X = 1)
    (hQ : ∀ v, Q ((X.submatrix e e) *ᵥ v) = Q v) : ∃ x : OrthN Q, matO Q e x = X := by
  have hm : ∀ M N : M2 d, M.submatrix e e * N.submatrix e e = (M * N).submatrix e e :=
    fun M N => Matrix.submatrix_mul_equiv M N e e e
  have h1' : X.submatrix e e * Xi.submatrix e e = 1 := by
    rw [hm, h1]; exact Matrix.submatrix_one_equiv e
  have h2' : Xi.submatrix e e * X.submatrix e e = 1 := by
    rw [hm, h2]; exact Matrix.submatrix_one_equiv e
  refine ⟨⟨⟨X.submatrix e e, Xi.submatrix e e, h1', h2'⟩, ?_⟩, ?_⟩
  · rw [mem_OrthN_iff]; exact hQ
  · rw [matO_apply]
    simp only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

theorem mem_statedOmega_of_inv {x y : GL ι (ZMod 2)} (hx : x ∈ OrthN Q) (hy : y ∈ OrthN Q)
    (hx9 : x ^ 9 = 1) (hyx : y * x * y⁻¹ = x⁻¹) : x ∈ StatedOmega Q := by
  have hc : ⁅y, x⁆ ∈ ⁅OrthN Q, OrthN Q⁆ := Subgroup.commutator_mem_commutator hy hx
  have e1 : ⁅y, x⁆ = x⁻¹ * x⁻¹ := by
    rw [commutatorElement_def, hyx]
  have e2 : x = (x⁻¹ * x⁻¹) ^ 4 := by
    have h : x ^ 8 * x = 1 := by rw [← pow_succ]; exact hx9
    have hx8 : x ^ 8 = x⁻¹ := eq_inv_of_mul_eq_one_left h
    have : (x⁻¹ * x⁻¹) ^ 4 = (x⁻¹) ^ 8 := by
      rw [← pow_two, ← pow_mul]
    rw [this, inv_pow, hx8, inv_inv]
  have hmem : ((⁅y, x⁆ : GL ι (ZMod 2))) ^ 4 ∈ StatedOmega Q := Subgroup.pow_mem _ hc 4
  rw [e1, ← e2] at hmem
  exact hmem

end Orth

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem zmod_two_units_eq_one (u : (ZMod 2)ˣ) : u = 1 := by
  apply Units.ext
  have h : (u : ZMod 2) ≠ 0 := u.ne_zero
  revert h
  generalize (u : ZMod 2) = a
  revert a
  decide

theorem statedScalars_zmod_two : StatedScalars ι (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨u, rfl⟩
  rw [zmod_two_units_eq_one u]
  simp

noncomputable def statedProjEquiv (H : Subgroup (GL ι (ZMod 2))) : StatedProj H ≃* H := by
  have h : (StatedScalars ι (ZMod 2)).subgroupOf H = ⊥ := by
    rw [statedScalars_zmod_two, Subgroup.bot_subgroupOf]
  exact (QuotientGroup.quotientMulEquivOfEq (G := ↥H) h).trans (QuotientGroup.quotientBot (G := ↥H))

theorem nonempty_mulEquiv_omegaPlus {G : Type} [Group G] {r : ℕ}
    (hcl : StatedClassicalModel G .POmegaPlus r 2 1) :
    Nonempty (G ≃* StatedOmega (StatedQuadPlus r (ZMod 2))) := by
  have hY : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus r (ZMod 2))))
      .POmegaPlus r 2 1 := ⟨hcl.1, ZMod 2, inferInstance, inferInstance, by simp,
    ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hcl hY
  exact ⟨e.trans (statedProjEquiv (StatedOmega (StatedQuadPlus r (ZMod 2))))⟩

theorem nonempty_mulEquiv_omegaMinus {G : Type} [Group G] {r : ℕ}
    (hcl : StatedClassicalModel G .POmegaMinus r 2 1) :
    Nonempty (G ≃* StatedOmega (StatedQuadMinus r (ZMod 2) 1 1)) := by
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hY : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus r (ZMod 2) 1 1)))
      .POmegaMinus r 2 1 := ⟨hcl.1, ZMod 2, inferInstance, inferInstance, by simp, 1, 1, hirr,
    ⟨MulEquiv.refl _⟩⟩
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hcl hY
  exact ⟨e.trans (statedProjEquiv (StatedOmega (StatedQuadMinus r (ZMod 2) 1 1)))⟩

end Transport

end CFSG.HardMathSupport.Foote.E27
