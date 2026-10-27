module

public import CFSG.FeitThompson.Representations.FiniteOrderTraceCharacters
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Polynomial

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

noncomputable def exteriorPowerEnd (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] (n : ℕ) : Module.End R M →* Module.End R (⋀[R]^n M) where
  toFun f := exteriorPower.map n f
  map_one' := exteriorPower.map_id (R := R) (M := M) (n := n)
  map_mul' f g := exteriorPower.map_comp (n := n) g f

@[simp]
theorem exteriorPowerEnd_apply (n : ℕ) (f : Module.End R M) :
    exteriorPowerEnd R M n f = exteriorPower.map n f := (rfl)

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V] {g : G}

noncomputable def Representation.exteriorPower (ρ : Representation R G M) (n : ℕ) :
    Representation R G (⋀[R]^n M) := (exteriorPowerEnd R M n).comp ρ

@[simp]
theorem Representation.exteriorPower_apply (ρ : Representation R G M) (n : ℕ) (g : G) :
    Representation.exteriorPower ρ n g = exteriorPower.map n (ρ g) := (rfl)

private theorem toMatrix_exteriorPower_diag (b : Basis ι R M) (f : Module.End R M) (n : ℕ)
    (s : ↥(Set.powersetCard ι n)) :
    LinearMap.toMatrix (b.exteriorPower n) (b.exteriorPower n) (exteriorPower.map n f) s s
      = ((LinearMap.toMatrix b b f).submatrix
          (Set.powersetCard.ofFinEmbEquiv.symm s)
          (Set.powersetCard.ofFinEmbEquiv.symm s)).det := by
  rw [LinearMap.toMatrix_apply, ← Basis.coord_apply, exteriorPower.basis_coord]
  have hb : (b.exteriorPower n) s
      = exteriorPower.ιMulti R n (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
    rw [exteriorPower.coe_basis]; rfl
  rw [hb, exteriorPower.map_apply_ιMulti, exteriorPower.ιMultiDual_apply_ιMulti,
    ← Matrix.det_transpose]
  congr 1
  ext i k
  simp [Matrix.submatrix, LinearMap.toMatrix_apply, Basis.coord_apply]

theorem trace_exteriorPower_map (b : Basis ι R M) (f : Module.End R M) (n : ℕ) :
    LinearMap.trace R (⋀[R]^n M) (exteriorPower.map n f)
      = ∑ s ∈ Finset.univ.powersetCard n,
          ((LinearMap.toMatrix b b f).submatrix (Subtype.val : ↥s → ι) Subtype.val).det := by
  classical
  rw [LinearMap.trace_eq_matrix_trace R (b.exteriorPower n), Matrix.trace,
    Finset.sum_subtype (p := fun s : Finset ι => s ∈ Set.powersetCard ι n)
      (Finset.univ.powersetCard n) (fun x => by simp [Set.powersetCard])
      (fun s => ((LinearMap.toMatrix b b f).submatrix (Subtype.val : ↥s → ι) Subtype.val).det)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.diag_apply, toMatrix_exteriorPower_diag,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  set A := LinearMap.toMatrix b b f
  rw [← Matrix.det_submatrix_equiv_self ((s : Finset ι).orderIsoOfFin s.2).toEquiv
      (A.submatrix (Subtype.val : ↥(s : Finset ι) → ι) Subtype.val), Matrix.submatrix_submatrix]
  rfl

theorem trace_exteriorPower_map_eq_coeff (b : Basis ι R M) (f : Module.End R M) (n : ℕ) :
    LinearMap.trace R (⋀[R]^n M) (exteriorPower.map n f)
      = (1 + (X : R[X]) • (LinearMap.toMatrix b b f).map C).det.coeff n := by
  classical
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors, trace_exteriorPower_map b]

theorem trace_exteriorPower_map_eq_sum_prod (b : Basis ι R M) (f : Module.End R M)
    (α : ι → R) (hf : ∀ i, f (b i) = α i • b i) (n : ℕ) :
    LinearMap.trace R (⋀[R]^n M) (exteriorPower.map n f)
      = ∑ s ∈ Finset.univ.powersetCard n, ∏ i ∈ s, α i := by
  classical
  have hm : LinearMap.toMatrix b b f = Matrix.diagonal α := by
    ext i j
    rw [LinearMap.toMatrix_apply, hf j, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one, Finsupp.single_apply, Matrix.diagonal_apply]
    rcases eq_or_ne i j with h | h
    · simp [h]
    · rw [if_neg (Ne.symm h), if_neg h]
  rw [trace_exteriorPower_map b, hm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show (Matrix.diagonal α).submatrix (Subtype.val : ↥s → ι) Subtype.val
      = Matrix.diagonal (fun i : ↥s => α i.1) from Matrix.submatrix_diagonal_embedding α
      (Function.Embedding.subtype (· ∈ s)), Matrix.det_diagonal, Finset.prod_coe_sort s α]

private noncomputable def stdBasis (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] :
    Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex R M))) R M :=
  (Module.Free.chooseBasis R M).reindex (Fintype.equivFin _)

theorem trace_exteriorPower_map_zero [Module.Free R M] [Module.Finite R M] (f : Module.End R M) :
    LinearMap.trace R (⋀[R]^0 M) (exteriorPower.map 0 f) = 1 := by
  rw [trace_exteriorPower_map (stdBasis R M), Finset.powersetCard_zero]
  simp

theorem trace_exteriorPower_map_one [Module.Free R M] [Module.Finite R M] (f : Module.End R M) :
    LinearMap.trace R (⋀[R]^1 M) (exteriorPower.map 1 f) = LinearMap.trace R M f := by
  rw [trace_exteriorPower_map (stdBasis R M), Finset.powersetCard_one, Finset.sum_map,
    LinearMap.trace_eq_matrix_trace R (stdBasis R M), Matrix.trace]
  exact Finset.sum_congr rfl fun i _ => by simp [Matrix.det_unique]

theorem trace_exteriorPower_map_eq_zero_of_lt [FiniteDimensional ℂ V] {j : ℕ}
    (hj : finrank ℂ V < j) (f : Module.End ℂ V) :
    LinearMap.trace ℂ (⋀[ℂ]^j V) (exteriorPower.map j f) = 0 := by
  have h0 : finrank ℂ (⋀[ℂ]^j V) = 0 := by
    rw [exteriorPower.finrank_eq]; exact Nat.choose_eq_zero_of_lt hj
  have hs : Subsingleton (⋀[ℂ]^j V) := by rw [← finrank_zero_iff (R := ℂ)]; exact h0
  have hf : exteriorPower.map j f = 0 := LinearMap.ext fun x => hs.elim _ _
  simp [hf]

theorem det_one_add_smul_eq_eval (b : Basis ι R M) (f : Module.End R M) (t : R) :
    LinearMap.det (LinearMap.id + t • f)
      = eval t (1 + (X : R[X]) • (LinearMap.toMatrix b b f).map C).det := by
  classical
  rw [← LinearMap.det_toMatrix b, ← Polynomial.coe_evalRingHom,
    RingHom.map_det (Polynomial.evalRingHom t)]
  congr 1
  ext i j
  simp only [map_add, LinearMap.toMatrix_id_eq_basis_toMatrix, Basis.toMatrix_self, map_smul,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, coe_evalRingHom,
    Matrix.map_apply, X_mul_C, eval_mul, eval_C, eval_X, Matrix.one_apply]
  rcases eq_or_ne i j with h | h
  · simp [h, mul_comm]
  · simp [h, mul_comm]

theorem natDegree_det_one_add_X_smul_le (A : Matrix ι ι R) :
    ((1 + (X : R[X]) • A.map C).det).natDegree ≤ Fintype.card ι := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Finset.powersetCard_eq_empty.2 (by simpa using hN)]
  simp

theorem det_one_add_smul_eq_sum_trace_exteriorPower (b : Basis ι R M) (f : Module.End R M)
    (t : R) :
    LinearMap.det (LinearMap.id + t • f)
      = ∑ j ∈ Finset.range (Fintype.card ι + 1),
          LinearMap.trace R (⋀[R]^j M) (exteriorPower.map j f) * t ^ j := by
  rw [det_one_add_smul_eq_eval b,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_det_one_add_X_smul_le _)) t]
  exact Finset.sum_congr rfl fun j _ => by rw [trace_exteriorPower_map_eq_coeff b]

noncomputable def Representation.exteriorChar (ρ : Representation ℂ G V) (j : ℕ) : G → ℂ :=
  (Representation.exteriorPower ρ j).character

theorem Representation.exteriorChar_apply (ρ : Representation ℂ G V) (j : ℕ) (g : G) :
    Representation.exteriorChar ρ j g
      = LinearMap.trace ℂ (⋀[ℂ]^j V) (exteriorPower.map j (ρ g)) := (rfl)

theorem Representation.exteriorChar_eq_character (ρ : Representation ℂ G V) (j : ℕ) :
    Representation.exteriorChar ρ j = (Representation.exteriorPower ρ j).character := (rfl)

theorem Representation.exists_fdRep_character_eq_exteriorChar {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (j : ℕ) :
    ∃ W : FDRep ℂ G, W.character = Representation.exteriorChar ρ j :=
  ⟨FDRep.of (Representation.exteriorPower ρ j), by
    funext g
    rw [FDRep.character, FDRep.of_ρ', Representation.exteriorChar, Representation.character]⟩

theorem Representation.det_one_add_smul_eq_sum_exteriorChar [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) (t : ℂ) :
    LinearMap.det (LinearMap.id + t • (ρ g : Module.End ℂ V))
      = ∑ j ∈ Finset.range (finrank ℂ V + 1), Representation.exteriorChar ρ j g * t ^ j := by
  have h := det_one_add_smul_eq_sum_trace_exteriorPower (Module.finBasis ℂ V)
    (ρ g : Module.End ℂ V) t
  rw [Fintype.card_fin] at h
  rw [h]
  exact Finset.sum_congr rfl fun j _ => by rw [Representation.exteriorChar_apply]

theorem Representation.exteriorChar_zero [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Representation.exteriorChar ρ 0 = 1 := by
  funext g
  rw [Representation.exteriorChar_apply, trace_exteriorPower_map_zero, Pi.one_apply]

theorem Representation.exteriorChar_one [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Representation.exteriorChar ρ 1 = ρ.character := by
  funext g
  rw [Representation.exteriorChar_apply, trace_exteriorPower_map_one, Representation.character]

theorem Representation.exteriorChar_eq_zero_of_finrank_lt [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {j : ℕ} (hj : finrank ℂ V < j) :
    Representation.exteriorChar ρ j = 0 := by
  funext g
  rw [Representation.exteriorChar_apply, trace_exteriorPower_map_eq_zero_of_lt hj, Pi.zero_apply]

theorem Representation.exteriorChar_eq_esymm_of_eigenbasis (ρ : Representation ℂ G V) (j : ℕ)
    (b : Basis ι ℂ V) (α : ι → ℂ) (hα : ∀ i, ρ g (b i) = α i • b i) :
    Representation.exteriorChar ρ j g = (Finset.univ.val.map α).esymm j := by
  rw [Representation.exteriorChar_apply, trace_exteriorPower_map_eq_sum_prod b _ α hα,
    Finset.esymm_map_val]

theorem Representation.exteriorChar_eq_esymm [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hg : IsOfFinOrder g) :
    ∃ α : Fin (finrank ℂ V) → ℂ,
      (∀ j, Representation.exteriorChar ρ j g = (Finset.univ.val.map α).esymm j) ∧
        ∀ i, Module.End.HasEigenvalue (ρ g) (α i) := by
  obtain ⟨b, α, hα, -⟩ := Representation.exists_basis_eigenvector ρ hg
  refine ⟨α, fun j => Representation.exteriorChar_eq_esymm_of_eigenbasis ρ j b α hα, fun i => ?_⟩
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨Module.End.mem_eigenspace_iff.2 (hα i), b.ne_zero i⟩

end CFSG.FeitThompson
