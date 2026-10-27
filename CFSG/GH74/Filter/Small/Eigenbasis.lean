module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.GH74.Filter

open Module Module.End Polynomial

section LinearAlgebra

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem aeval_X_sq_sub_one_eq_zero {f : End K V} (hf : f ^ 2 = 1) :
    aeval f (X ^ 2 - 1 : K[X]) = 0 := by
  rw [map_sub, map_pow, aeval_X, map_one, hf, sub_self]

theorem isSemisimple_of_sq_eq_one (h2 : (2 : K) ≠ 0) {f : End K V} (hf : f ^ 2 = 1) :
    f.IsSemisimple := by
  refine isSemisimple_of_squarefree_aeval_eq_zero ?_ (aeval_X_sq_sub_one_eq_zero hf)
  have h2' : ((2 : ℕ) : K) ≠ 0 := by simpa using h2
  simpa using (separable_X_pow_sub_C (1 : K) h2' one_ne_zero).squarefree

theorem iSup_eigenspace_eq_top_of_sq_eq_one (h2 : (2 : K) ≠ 0) {f : End K V} (hf : f ^ 2 = 1) :
    ⨆ μ, f.eigenspace μ = ⊤ := by
  refine top_unique fun v _ => ?_
  have hff : ∀ w : V, f (f w) = w := fun w => by
    rw [← Module.End.mul_apply, ← sq, hf, Module.End.one_apply]
  have h1 : (2 : K)⁻¹ • (v + f v) ∈ f.eigenspace 1 := by
    rw [mem_eigenspace_iff, one_smul, map_smul, map_add, hff, add_comm]
  have h2' : (2 : K)⁻¹ • (v - f v) ∈ f.eigenspace (-1) := by
    rw [mem_eigenspace_iff, neg_smul, one_smul, map_smul, map_sub, hff, ← smul_neg, neg_sub]
  have hv : v = (2 : K)⁻¹ • (v + f v) + (2 : K)⁻¹ • (v - f v) := by
    rw [← smul_add, add_add_sub_cancel, ← two_smul K v, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hv]
  exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem 1 h1) (Submodule.mem_iSup_of_mem (-1) h2')

theorem iSup_maxGenEigenspace_eq_top_of_sq_eq_one (h2 : (2 : K) ≠ 0) {f : End K V}
    (hf : f ^ 2 = 1) : ⨆ μ, f.maxGenEigenspace μ = ⊤ :=
  ((isSemisimple_of_sq_eq_one h2 hf).iSup_maxGenEigenspace_eq_top_iff).2
    (iSup_eigenspace_eq_top_of_sq_eq_one h2 hf)

theorem exists_basis_common_eigenvectors_of_sq_eq_one (h2 : (2 : K) ≠ 0)
    [FiniteDimensional K V] {ι : Type*} [Finite ι] (f : ι → End K V)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hsq : ∀ i, f i ^ 2 = 1) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (μ : ι → Fin (finrank K V) → K),
      ∀ i j, f i (b j) = μ i j • b j := by
  classical
  set W : (ι → K) → Submodule K V := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i) with hWdef
  have hW : ∀ (χ : ι → K) (i : ι), (f i).maxGenEigenspace (χ i) = (f i).eigenspace (χ i) :=
    fun χ i =>
    (isSemisimple_of_sq_eq_one h2 (hsq i)).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace _
  have htop : ⨆ χ, W χ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hcomm i j) fun i => iSup_maxGenEigenspace_eq_top_of_sq_eq_one h2 (hsq i)
  have hind : iSupIndep W :=
    independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      fun i j φ => mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let bW := fun χ => Basis.ofVectorSpace K (W χ)
  let b₀ := hint.collectedBasis bW
  have : Finite (Σ χ, Basis.ofVectorSpaceIndex K (W χ)) := Module.Finite.finite_basis b₀
  let e₀ : (Σ χ, Basis.ofVectorSpaceIndex K (W χ)) ≃ Fin (finrank K V) :=
    (Finite.equivFin _).trans (finCongr (finrank_eq_nat_card_basis b₀).symm)
  refine ⟨b₀.reindex e₀, fun i j => (e₀.symm j).1 i, fun i j => ?_⟩
  have hmem : b₀ (e₀.symm j) ∈ W (e₀.symm j).1 := hint.collectedBasis_mem bW (e₀.symm j)
  rw [Basis.reindex_apply]
  have hi := (Submodule.mem_iInf _).mp hmem i
  rw [hW] at hi
  exact mem_eigenspace_iff.mp hi

end LinearAlgebra

section Matrices

open Matrix

variable {K : Type*} [Field K]

theorem card_le_two_pow_of_elemAbelian_det (h2 : (2 : K) ≠ 0) {n : ℕ}
    (E : Subgroup (GL (Fin (n + 1)) K)) [Finite E] (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x ^ 2 = 1)
    (hdet : ∀ x ∈ E, (x : Matrix (Fin (n + 1)) (Fin (n + 1)) K).det = 1) :
    Nat.card E ≤ 2 ^ n := by
  classical
  let F : E →* End K (Fin (n + 1) → K) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin (n + 1)) (Fin (n + 1)) K ≃ₐ[K] _).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom (Matrix (Fin (n + 1)) (Fin (n + 1)) K)).comp E.subtype)
  have hF : ∀ g : E, F g = Matrix.toLin' ((g : GL (Fin (n + 1)) K) : Matrix _ _ K) := fun g => rfl
  have hFinj : Function.Injective F := fun g h hgh =>
    Subtype.ext (Units.ext (Matrix.toLinAlgEquiv'.injective hgh))
  have hFcomm : ∀ g h, Commute (F g) (F h) := fun g h => by
    show F g * F h = F h * F g
    rw [← map_mul, ← map_mul]
    exact congrArg F (Subtype.ext (hcomm g g.2 h h.2))
  have hFsq : ∀ g : E, F g ^ 2 = 1 := fun g => by
    have : g ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsq g g.2)
    rw [← map_pow, this, map_one]
  obtain ⟨b₀, μ₀, hb₀⟩ := exists_basis_common_eigenvectors_of_sq_eq_one h2 F hFcomm hFsq
  have hfin : finrank K (Fin (n + 1) → K) = n + 1 := Module.finrank_fin_fun K
  let b := b₀.reindex (finCongr hfin)
  let μ : E → Fin (n + 1) → K := fun g j => μ₀ g ((finCongr hfin).symm j)
  have hb : ∀ g j, F g (b j) = μ g j • b j := fun g j => by
    simp only [b, Basis.reindex_apply, μ]
    exact hb₀ g _
  have hμsq : ∀ g j, μ g j * μ g j = 1 := fun g j => by
    have h1 : (F g ^ 2) (b j) = b j := by rw [hFsq, Module.End.one_apply]
    rw [sq, Module.End.mul_apply, hb, map_smul, hb, smul_smul] at h1
    have h3 : (μ g j * μ g j - 1) • b j = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero j))
  have hdetμ : ∀ g, ∏ j, μ g j = 1 := fun g => by
    have h1 : LinearMap.toMatrix b b (F g) = Matrix.diagonal (μ g) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [LinearMap.toMatrix_apply, hb]
      · simp [LinearMap.toMatrix_apply, hb, hij]
    have h2' : (LinearMap.toMatrix b b (F g)).det = 1 := by
      rw [LinearMap.det_toMatrix, hF, LinearMap.det_toLin']
      exact hdet g g.2
    rwa [h1, Matrix.det_diagonal] at h2'
  let S : Finset K := {1, -1}
  have hS : Fintype.card S ≤ 2 := by
    rw [Fintype.card_coe]
    exact Finset.card_le_two
  let φ : E → (Fin n → S) := fun g j =>
    ⟨μ g (Fin.castSucc j), by
      rcases mul_self_eq_one_iff.1 (hμsq g (Fin.castSucc j)) with h | h <;> simp [S, h]⟩
  have hφ : Function.Injective φ := by
    intro g h hgh
    have hj : ∀ j : Fin n, μ g (Fin.castSucc j) = μ h (Fin.castSucc j) := fun j =>
      congrArg Subtype.val (congrFun hgh j)
    have hlast : μ g (Fin.last n) = μ h (Fin.last n) := by
      have hg := hdetμ g
      have hh := hdetμ h
      rw [Fin.prod_univ_castSucc] at hg hh
      have hP : ∏ j : Fin n, μ g (Fin.castSucc j) = ∏ j : Fin n, μ h (Fin.castSucc j) :=
        Finset.prod_congr rfl fun j _ => hj j
      rw [← hP] at hh
      exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hg) (hg.trans hh.symm)
    have hall : ∀ j, μ g j = μ h j := fun j => by
      induction j using Fin.lastCases with
      | last => exact hlast
      | cast j => exact hj j
    refine hFinj (b.ext fun j => ?_)
    rw [hb, hb, hall j]
  calc Nat.card E ≤ Nat.card (Fin n → S) := Nat.card_le_card_of_injective φ hφ
    _ = Fintype.card S ^ n := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := S), Nat.card_eq_fintype_card (α := Fin n),
        Fintype.card_fin]
    _ ≤ 2 ^ n := Nat.pow_le_pow_left hS n

end Matrices

end CFSG.GH74.Filter
