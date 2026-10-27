module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.GF2Type.Smith1979.Case2.U43Lin

open Module

open scoped Classical

variable {K : Type} [Field K]

@[expose] def sgn (K : Type) [Field K] (b : Bool) : K := if b then 1 else -1

@[expose] def jointEigen {V ι : Type} [AddCommGroup V] [Module K V] (F : ι → Module.End K V)
    (χ : ι → K) : Submodule K V :=
  ⨅ i, (F i).eigenspace (χ i)

@[expose] def signEigen {V ι : Type} [AddCommGroup V] [Module K V] (F : ι → Module.End K V)
    (b : ι → Bool) : Submodule K V :=
  jointEigen F (fun i => sgn K (b i))

theorem isSemisimple_of_mul_self_eq_one {V : Type} [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) {f : Module.End K V} (hf : f * f = 1) : f.IsSemisimple := by
  have hn : ((2 : ℕ) : K) ≠ 0 := by exact_mod_cast h2
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := Polynomial.X ^ 2 - Polynomial.C (1 : K)) ?_ ?_
  · exact (Polynomial.separable_X_pow_sub_C (1 : K) hn one_ne_zero).squarefree
  · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one, sq, hf, sub_self]

theorem iSup_maxGenEigenspace_eq_top_of_mul_self {V : Type} [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) {f : Module.End K V} (hf : f * f = 1) :
    ⨆ μ : K, f.maxGenEigenspace μ = ⊤ := by
  have hf2 : ∀ w, f (f w) = w := fun w => by rw [← Module.End.mul_apply, hf, Module.End.one_apply]
  have h2' : (2 : K)⁻¹ + 2⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  refine eq_top_iff.2 fun v _ => ?_
  have hp : f (v + f v) = (1 : K) • (v + f v) := by
    rw [map_add, hf2, one_smul, add_comm]
  have hm : f (v - f v) = (-1 : K) • (v - f v) := by
    rw [map_sub, hf2, neg_one_smul, neg_sub]
  have m1 : v + f v ∈ f.maxGenEigenspace 1 :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hp)
  have m2 : v - f v ∈ f.maxGenEigenspace (-1) :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 hm)
  have hsum : (2 : K)⁻¹ • (v + f v) + (2 : K)⁻¹ • (v - f v) = v := by
    rw [show (2 : K)⁻¹ • (v + f v) + (2 : K)⁻¹ • (v - f v) =
      ((2 : K)⁻¹ + (2 : K)⁻¹) • v by module, h2', one_smul]
  have hmem := Submodule.add_mem _
    (Submodule.mem_iSup_of_mem (1 : K) (Submodule.smul_mem _ (2 : K)⁻¹ m1))
    (Submodule.mem_iSup_of_mem (-1 : K) (Submodule.smul_mem _ (2 : K)⁻¹ m2))
  rwa [hsum] at hmem

theorem iSup_jointEigen_eq_top {V ι : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (F : ι → Module.End K V)
    (hF : ∀ i, F i * F i = 1) (hcomm : ∀ i j, Commute (F i) (F j)) :
    ⨆ χ : ι → K, jointEigen F χ = ⊤ := by
  have hss : ∀ i, (F i).IsSemisimple := fun i => isSemisimple_of_mul_self_eq_one h2 (hF i)
  have h1 : ∀ i μ, (F i).maxGenEigenspace μ = (F i).eigenspace μ := fun i μ =>
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    F (fun i j _ => hcomm i j) (fun i => iSup_maxGenEigenspace_eq_top_of_mul_self h2 (hF i))
  simpa only [jointEigen, h1] using this

theorem iSupIndep_jointEigen {V ι : Type} [AddCommGroup V] [Module K V]
    (F : ι → Module.End K V) (hss : ∀ i, (F i).IsSemisimple)
    (hcomm : ∀ i j, Commute (F i) (F j)) : iSupIndep fun χ : ι → K => jointEigen F χ := by
  have h1 : ∀ i μ, (F i).maxGenEigenspace μ = (F i).eigenspace μ := fun i μ =>
    (hss i).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  simpa only [jointEigen, h1] using this

theorem apply_of_mem_jointEigen {V ι : Type} [AddCommGroup V] [Module K V]
    {F : ι → Module.End K V} {χ : ι → K} {x : V} (hx : x ∈ jointEigen F χ) (i : ι) :
    F i x = χ i • x :=
  Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx i)

theorem eigen_sign {V ι : Type} [AddCommGroup V] [Module K V] {F : ι → Module.End K V}
    (hF : ∀ i, F i * F i = 1) (χ : ι → K) (hχ : jointEigen F χ ≠ ⊥) (i : ι) :
    χ i = 1 ∨ χ i = -1 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  have hva : F i v = χ i • v := apply_of_mem_jointEigen hv i
  have h1 : F i (F i v) = v := by rw [← Module.End.mul_apply, hF i, Module.End.one_apply]
  rw [hva, map_smul, hva, smul_smul] at h1
  have h3 : (χ i * χ i - 1) • v = 0 := by rw [sub_smul, one_smul, h1, sub_self]
  rcases smul_eq_zero.1 h3 with h | h
  · exact mul_self_eq_one_iff.1 (sub_eq_zero.1 h)
  · exact absurd h hv0

theorem sgn_injective (h2 : (2 : K) ≠ 0) : Function.Injective (sgn K : Bool → K) := by
  have hneg : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  intro x y h
  cases x <;> cases y
  · rfl
  · have h' : (-1 : K) = 1 := by simpa [sgn] using h
    exact absurd h' hneg
  · have h' : (-1 : K) = 1 := by simpa [sgn] using h.symm
    exact absurd h' hneg
  · rfl

theorem prod_sgn_eq_pow {n : ℕ} (b : Fin n → Bool) :
    ∏ k, sgn K (b k) = (-1 : K) ^ (∑ k, if b k then 0 else 1) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hb : b k <;> simp [sgn, hb]

@[expose] def evenPatterns : Finset (Fin 4 → Bool) :=
  Finset.univ.filter fun g => Even (∑ k, if g k then 0 else 1)

theorem card_evenPatterns : evenPatterns.card = 8 := by
  decide

theorem card_le_eight {V ι : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hdim : Module.finrank K V = 4) [Finite ι] (h2 : (2 : K) ≠ 0) (F : ι → Module.End K V)
    (hF : ∀ i, F i * F i = 1) (hcomm : ∀ i j, Commute (F i) (F j))
    (hdet : ∀ i, LinearMap.det (F i) = 1) (hinj : Function.Injective F) :
    Nat.card ι ≤ 8 := by
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [Nat.card_eq_fintype_card]
  have hneg : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  have hss : ∀ i, (F i).IsSemisimple := fun i => isSemisimple_of_mul_self_eq_one h2 (hF i)
  have hind : iSupIndep (signEigen F) := by
    have hsgn : Function.Injective (fun b : ι → Bool => fun i => sgn K (b i)) := by
      intro b c hbc
      funext i
      exact sgn_injective h2 (congrFun hbc i)
    exact (iSupIndep_jointEigen F hss hcomm).comp hsgn
  have hspan : ⨆ b : ι → Bool, signEigen F b = ⊤ := by
    rw [eq_top_iff, ← iSup_jointEigen_eq_top h2 F hF hcomm]
    refine iSup_le fun χ => ?_
    by_cases hχ : jointEigen F χ = ⊥
    · rw [hχ]
      exact bot_le
    · have e : (fun i => sgn K (decide (χ i = 1))) = χ := by
        funext i
        rcases eigen_sign hF χ hχ i with h | h <;> simp [sgn, h, hneg]
      refine le_iSup_of_le (fun i => decide (χ i = 1)) ?_
      show jointEigen F χ ≤ jointEigen F (fun i => sgn K (decide (χ i = 1)))
      exact le_of_eq (by rw [e])
  have hkey : ∀ i j : ι, (∀ b : ι → Bool, signEigen F b ≠ ⊥ → b i = b j) → F i = F j := by
    intro i j hij
    have hle : (⨆ b : ι → Bool, signEigen F b) ≤ LinearMap.eqLocus (F i) (F j) := by
      refine iSup_le fun b => ?_
      by_cases hb : signEigen F b = ⊥
      · rw [hb]
        exact bot_le
      · intro v hv
        have hvi : F i v = sgn K (b i) • v := apply_of_mem_jointEigen hv i
        have hvj : F j v = sgn K (b j) • v := apply_of_mem_jointEigen hv j
        rw [LinearMap.mem_eqLocus, hvi, hvj, hij b hb]
    rw [hspan] at hle
    exact LinearMap.ext fun v => LinearMap.mem_eqLocus.1 (hle Submodule.mem_top)
  have hcard4 : Fintype.card {b : ι → Bool // signEigen F b ≠ ⊥} ≤ 4 := by
    have := hind.subtype_ne_bot_le_finrank
    rwa [hdim] at this
  rcases Nat.lt_or_ge (Fintype.card {b : ι → Bool // signEigen F b ≠ ⊥}) 4 with hlt | hge
  ·
    have hinjΨ : Function.Injective
        (fun (i : ι) (c : {b : ι → Bool // signEigen F b ≠ ⊥}) => c.1 i) := by
      intro i j h
      have hij : ∀ b : ι → Bool, signEigen F b ≠ ⊥ → b i = b j := fun b hb =>
        congrFun h ⟨b, hb⟩
      exact hinj (hkey i j hij)
    calc Fintype.card ι
        ≤ Fintype.card ({b : ι → Bool // signEigen F b ≠ ⊥} → Bool) :=
          Fintype.card_le_of_injective _ hinjΨ
      _ = 2 ^ Fintype.card {b : ι → Bool // signEigen F b ≠ ⊥} := by
          rw [Fintype.card_fun, Fintype.card_bool]
      _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  ·
    have h4 : Fintype.card {b : ι → Bool // signEigen F b ≠ ⊥} = 4 := le_antisymm hcard4 hge
    let e : Fin 4 ≃ {b : ι → Bool // signEigen F b ≠ ⊥} :=
      (Fintype.equivFinOfCardEq h4).symm
    have hv : ∀ k : Fin 4, ∃ x : V, x ∈ signEigen F (e k).1 ∧ x ≠ 0 := fun k =>
      Submodule.exists_mem_ne_zero_of_ne_bot (e k).2
    choose v hvmem hv0 using hv
    have hli : LinearIndependent K v := by
      have hp : iSupIndep (fun k : Fin 4 => signEigen F (e k).1) :=
        hind.comp (f := fun k : Fin 4 => (e k).1) fun k l hkl => e.injective (Subtype.ext hkl)
      exact iSupIndep.linearIndependent _ hp hvmem hv0
    let bas : Basis (Fin 4) K V :=
      basisOfLinearIndependentOfCardEqFinrank hli (by rw [hdim]; simp)
    have hbas : ∀ k, bas k = v k := fun k => by
      simp [bas]
    have hdetF : ∀ i, LinearMap.det (F i) = ∏ k : Fin 4, sgn K ((e k).1 i) := by
      intro i
      have hM : LinearMap.toMatrix bas bas (F i) =
          Matrix.diagonal (fun k => sgn K ((e k).1 i)) := by
        ext k l
        have hFv : F i (bas l) = sgn K ((e l).1 i) • bas l := by
          rw [hbas l]
          exact apply_of_mem_jointEigen (hvmem l) i
        rw [LinearMap.toMatrix_apply, hFv, map_smul, Basis.repr_self, Finsupp.smul_apply,
          Finsupp.single_apply, Matrix.diagonal_apply]
        by_cases h : k = l
        · subst h
          simp
        · simp [h, Ne.symm h]
      rw [← LinearMap.det_toMatrix bas (F i), hM, Matrix.det_diagonal]
    have hpar : ∀ i, Even (∑ k : Fin 4, if (e k).1 i then 0 else 1) := by
      intro i
      have h1 : ∏ k : Fin 4, sgn K ((e k).1 i) =
          (-1 : K) ^ (∑ k : Fin 4, if (e k).1 i then 0 else 1) :=
        prod_sgn_eq_pow (fun k => (e k).1 i)
      have h3 : (-1 : K) ^ (∑ k : Fin 4, if (e k).1 i then 0 else 1) = 1 := by
        rw [← h1, ← hdetF i, hdet i]
      exact (neg_one_pow_eq_one_iff_even hneg).1 h3
    let Ψ : ι → (Fin 4 → Bool) := fun i k => (e k).1 i
    have hΨmem : ∀ i, Ψ i ∈ evenPatterns := fun i => by
      unfold evenPatterns
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hpar i⟩
    have hΨinj : Function.Injective Ψ := by
      intro i j h
      have hij : ∀ b : ι → Bool, signEigen F b ≠ ⊥ → b i = b j := by
        intro b hb
        have := congrFun h (e.symm ⟨b, hb⟩)
        simpa [Ψ] using this
      exact hinj (hkey i j hij)
    calc Fintype.card ι
        ≤ Fintype.card evenPatterns :=
          Fintype.card_le_of_injective (fun i => (⟨Ψ i, hΨmem i⟩ : evenPatterns))
            (fun i j h => hΨinj (congrArg Subtype.val h))
      _ = evenPatterns.card := Fintype.card_coe _
      _ = 8 := card_evenPatterns

theorem card_le_eight_of_subgroup [Finite K] (h2 : (2 : K) ≠ 0)
    (A : Subgroup (GL (Fin 4) K)) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a * a = 1) (hdet : ∀ a ∈ A, (a : Matrix (Fin 4) (Fin 4) K).det = 1) :
    Nat.card A ≤ 8 := by
  have hsqM : ∀ a : A, ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
    intro a
    rw [← Units.val_mul, hsq _ a.2, Units.val_one]
  refine card_le_eight (V := Fin 4 → K) (Module.finrank_fin_fun K) h2
    (fun a : A => Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) ?_ ?_ ?_ ?_
  · intro a
    show Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hsqM a, Matrix.toLin'_one]
    rfl
  · intro a b
    show Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.toLin' ((b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.toLin' ((b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
    congr 1
    rw [← Units.val_mul, ← Units.val_mul, hcomm _ a.2 _ b.2]
  · intro a
    show LinearMap.det (Matrix.toLin' ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = 1
    rw [LinearMap.det_toLin']
    exact hdet _ a.2
  · intro a b hab
    have hM : ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := Matrix.toLin'.injective hab
    exact Subtype.ext (Units.ext hM)

end CFSG.GF2Type.Smith1979.Case2.U43Lin
