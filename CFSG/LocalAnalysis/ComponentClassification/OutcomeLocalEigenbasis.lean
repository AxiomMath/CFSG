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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.ComponentClassification.OutcomeLocal

open Module Module.End Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

section LinearAlgebra

theorem splits_X_pow_sub_X_zmod : (X ^ p - X : (ZMod p)[X]).Splits := by
  rw [splits_iff_card_roots]
  have h := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at h
  rw [h, FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt, Finset.card_val,
    Finset.card_univ, ZMod.card]

theorem X_pow_sub_one_dvd_X_pow_sub_X : (X ^ (p - 1) - 1 : (ZMod p)[X]) ∣ X ^ p - X :=
  ⟨X, by rw [sub_mul, one_mul, ← pow_succ, Nat.sub_add_cancel hp.out.one_le]⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem aeval_X_pow_sub_one_of_pow_eq_one {f : End (ZMod p) V} (hf : f ^ (p - 1) = 1) :
    aeval f (X ^ (p - 1) - 1 : (ZMod p)[X]) = 0 := by
  rw [map_sub, map_pow, aeval_X, map_one, hf, sub_self]

theorem exists_hasEigenvalue_of_pow_eq_one [FiniteDimensional (ZMod p) V] [Nontrivial V]
    {f : End (ZMod p) V} (hf : f ^ (p - 1) = 1) : ∃ μ, f.HasEigenvalue μ := by
  have hint : IsIntegral (ZMod p) f := Algebra.IsIntegral.isIntegral f
  have hdvd : minpoly (ZMod p) f ∣ X ^ p - X :=
    (minpoly.dvd _ _ (aeval_X_pow_sub_one_of_pow_eq_one hf)).trans X_pow_sub_one_dvd_X_pow_sub_X
  have hsplit : (minpoly (ZMod p) f).Splits :=
    splits_X_pow_sub_X_zmod.of_dvd (FiniteField.X_pow_card_sub_X_ne_zero _ hp.out.one_lt) hdvd
  have hdeg : (minpoly (ZMod p) f).degree ≠ 0 := by
    rw [degree_eq_natDegree (minpoly.ne_zero hint)]
    exact_mod_cast (minpoly.natDegree_pos hint).ne'
  obtain ⟨μ, hμ⟩ := hsplit.exists_eval_eq_zero hdeg
  exact ⟨μ, hasEigenvalue_of_isRoot hμ⟩

theorem isSemisimple_of_pow_eq_one {f : End (ZMod p) V} (hf : f ^ (p - 1) = 1) :
    f.IsSemisimple := by
  refine isSemisimple_of_squarefree_aeval_eq_zero ?_ (aeval_X_pow_sub_one_of_pow_eq_one hf)
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hn : ((p - 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Nat.cast_sub hp.out.one_le, ZMod.natCast_self, zero_sub, Nat.cast_one]
    exact neg_ne_zero.mpr h1
  simpa using (separable_X_pow_sub_C (1 : ZMod p) hn h1).squarefree

theorem iSup_maxGenEigenspace_eq_top_of_pow_eq_one [FiniteDimensional (ZMod p) V]
    (f : End (ZMod p) V) (hf : f ^ (p - 1) = 1) : ⨆ μ, f.maxGenEigenspace μ = ⊤ := by
  suffices ∀ n, finrank (ZMod p) V = n → ⨆ μ, f.maxGenEigenspace μ = ⊤ from this _ rfl
  intro n h_dim
  induction n using Nat.strong_induction_on generalizing V with | h n ih =>
  rcases n with - | n
  · rw [← top_le_iff]
    simp only [Submodule.finrank_eq_zero.1 (Eq.trans (finrank_top _ _) h_dim), bot_le]
  · have : Nontrivial V := finrank_pos_iff.1 (by rw [h_dim]; apply Nat.zero_lt_succ)
    obtain ⟨μ₀, hμ₀⟩ := exists_hasEigenvalue_of_pow_eq_one hf
    let ES := f.genEigenspace μ₀ (finrank (ZMod p) V)
    let ER := f.genEigenrange μ₀ (finrank (ZMod p) V)
    have h_f_ER : ∀ x : V, x ∈ ER → f x ∈ ER := fun x hx =>
      map_genEigenrange_le (Submodule.mem_map_of_mem hx)
    let f' : End (ZMod p) ER := f.restrict h_f_ER
    have hpow' : ∀ (k : ℕ) (x : ER), ((f' ^ k) x : V) = (f ^ k) x := by
      intro k x
      induction k with
      | zero => rfl
      | succ k ihk =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.coe_restrict_apply, ihk, pow_succ',
          Module.End.mul_apply]
    have hf' : f' ^ (p - 1) = 1 := by
      ext x
      rw [hpow', hf, Module.End.one_apply, Module.End.one_apply]
    have h_dim_ES_pos : 0 < finrank (ZMod p) ES := by
      dsimp +instances only [ES]
      rw [h_dim]
      apply pos_finrank_genEigenspace_of_hasEigenvalue hμ₀ (Nat.zero_lt_succ n)
    have h_dim_add : finrank (ZMod p) ER + finrank (ZMod p) ES = finrank (ZMod p) V := by
      dsimp +instances only [ER, ES]
      rw [Module.End.genEigenspace_nat, Module.End.genEigenrange_nat]
      apply LinearMap.finrank_range_add_finrank_ker
    have h_dim_ER : finrank (ZMod p) ER < n.succ := by lia
    have ih_ER : ⨆ μ, f'.maxGenEigenspace μ = ⊤ := ih (finrank (ZMod p) ER) h_dim_ER f' hf' rfl
    have ih_ER' : ⨆ μ, (f'.maxGenEigenspace μ).map ER.subtype = ER := by
      simp only [(Submodule.map_iSup _ _).symm, ih_ER, Submodule.map_subtype_top ER]
    have hff' : ∀ μ, (f'.maxGenEigenspace μ).map ER.subtype ≤ f.maxGenEigenspace μ := by
      intros
      rw [maxGenEigenspace, genEigenspace_restrict]
      apply Submodule.map_comap_le
    have hER : ER ≤ ⨆ μ, f.maxGenEigenspace μ := by
      rw [← ih_ER']
      exact iSup_mono hff'
    have hES : ES ≤ ⨆ μ, f.maxGenEigenspace μ :=
      ((f.genEigenspace μ₀).mono le_top).trans (le_iSup f.maxGenEigenspace μ₀)
    have h_disjoint : Disjoint ER ES := generalized_eigenvec_disjoint_range_ker f μ₀
    change ⨆ μ, f.maxGenEigenspace μ = ⊤
    rw [← top_le_iff, ← Submodule.eq_top_of_disjoint ER ES h_dim_add.ge h_disjoint]
    exact sup_le hER hES

theorem exists_basis_common_eigenvectors [FiniteDimensional (ZMod p) V] {ι : Type*} [Finite ι]
    (f : ι → End (ZMod p) V) (hcomm : ∀ i j, Commute (f i) (f j))
    (hpow : ∀ i, f i ^ (p - 1) = 1) :
    ∃ (b : Basis (Fin (finrank (ZMod p) V)) (ZMod p) V)
      (μ : ι → Fin (finrank (ZMod p) V) → ZMod p), ∀ i j, f i (b j) = μ i j • b j := by
  classical
  set W : (ι → ZMod p) → Submodule (ZMod p) V := fun χ => ⨅ i, (f i).maxGenEigenspace (χ i)
    with hWdef
  have hW : ∀ (χ : ι → ZMod p) (i : ι), (f i).maxGenEigenspace (χ i) = (f i).eigenspace (χ i) :=
    fun χ i =>
    (isSemisimple_of_pow_eq_one (hpow i)).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace _
  have htop : ⨆ χ, W χ = ⊤ :=
    iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
      (fun i j _ => hcomm i j) fun i => iSup_maxGenEigenspace_eq_top_of_pow_eq_one (f i) (hpow i)
  have hind : iSupIndep W :=
    independent_iInf_maxGenEigenspace_of_forall_mapsTo f
      fun i j φ => mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let bW := fun χ => Basis.ofVectorSpace (ZMod p) (W χ)
  let b₀ := hint.collectedBasis bW
  have : Finite (Σ χ, Basis.ofVectorSpaceIndex (ZMod p) (W χ)) := Module.Finite.finite_basis b₀
  let e₀ : (Σ χ, Basis.ofVectorSpaceIndex (ZMod p) (W χ)) ≃ Fin (finrank (ZMod p) V) :=
    (Finite.equivFin _).trans (finCongr (finrank_eq_nat_card_basis b₀).symm)
  refine ⟨b₀.reindex e₀, fun i j => (e₀.symm j).1 i, fun i j => ?_⟩
  have hmem : b₀ (e₀.symm j) ∈ W (e₀.symm j).1 := hint.collectedBasis_mem bW (e₀.symm j)
  rw [Basis.reindex_apply]
  have hi := (Submodule.mem_iInf _).mp hmem i
  rw [hW] at hi
  exact mem_eigenspace_iff.mp hi

end LinearAlgebra

section Group

open scoped IsMulCommutative

variable {Q : Type*} [Group Q]

theorem exists_eigenbasis_subgroup (V : Subgroup Q) [Finite V]
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVp : ∀ x ∈ V, x ^ p = 1)
    {ι : Type*} [Finite ι] (φ : ι → Q →* Q) (hφV : ∀ i, ∀ x ∈ V, φ i x ∈ V)
    (hcomm : ∀ i j, ∀ x ∈ V, φ i (φ j x) = φ j (φ i x))
    (hpow : ∀ i, ∀ x ∈ V, (φ i)^[p - 1] x = x) :
    ∃ (r : ℕ) (e : Fin r → Q) (c : ι → Fin r → ZMod p), Nat.card V = p ^ r ∧
      (∀ j, e j ∈ V ∧ e j ≠ 1) ∧ (∀ x, x ∈ Subgroup.closure (Set.range e) ↔ x ∈ V) ∧
      ∀ i j, c i j ≠ 0 ∧ φ i (e j) = e j ^ (c i j).val := by
  classical
  have : IsMulCommutative V := ⟨⟨fun x y => Subtype.ext (hVc x x.2 y y.2)⟩⟩
  have hsmul : ∀ x : Additive V, p • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using hVp _ (Additive.toMul x).2)
  have instM : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule hsmul
  let ψ : ι → V →* V := fun i => ((φ i).domRestrict V).codRestrict V fun x => hφV i x x.2
  let f : ι → End (ZMod p) (Additive V) := fun i =>
    (MonoidHom.toAdditive (ψ i)).toZModLinearMap p
  have hf : ∀ i (x : Additive V),
      ((Additive.toMul (f i x) : V) : Q) = φ i (Additive.toMul x : V) := fun _ _ => rfl
  have hfcomm : ∀ i j, Commute (f i) (f j) := fun i j => LinearMap.ext fun x => by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hcomm i j _ (Additive.toMul x).2
  have hiter : ∀ i (k : ℕ) (x : Additive V),
      ((Additive.toMul ((f i ^ k) x) : V) : Q) = (φ i)^[k] (Additive.toMul x : V) := by
    intro i k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply, hf]
  have hfpow : ∀ i, f i ^ (p - 1) = 1 := fun i => LinearMap.ext fun x => by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hiter, hpow i _ (Additive.toMul x).2, Module.End.one_apply]
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors f hfcomm hfpow
  refine ⟨finrank (ZMod p) (Additive V), fun j => (Additive.toMul (b j) : V), μ, ?_,
    fun j => ⟨(Additive.toMul (b j)).2, ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun i j => ⟨?_, ?_⟩⟩
  · exact (FiniteField.pow_finrank_eq_natCard p (Additive V)).symm
  · intro h
    apply b.ne_zero j
    apply Additive.toMul.injective
    rw [toMul_zero]
    exact Subtype.ext h
  · refine (Subgroup.closure_le V).mpr ?_ hx
    rintro _ ⟨j, rfl⟩
    exact (Additive.toMul (b j)).2
  · let H : Subgroup V :=
      (Subgroup.closure (Set.range fun j => ((Additive.toMul (b j) : V) : Q))).comap V.subtype
    let S : Submodule (ZMod p) (Additive V) :=
      AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup H)
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨j, rfl⟩
    have hmem : Additive.ofMul (⟨x, hx⟩ : V) ∈ S := hS ▸ Submodule.mem_top
    exact (show (⟨x, hx⟩ : V) ∈ H from hmem)
  · intro h0
    apply b.ne_zero j
    have h1 : (f i ^ (p - 1)) (b j) = b j := by rw [hfpow, Module.End.one_apply]
    have h2 : f i ^ (p - 1) = f i ^ (p - 2) * f i := by
      rw [← pow_succ]
      congr 1
      have := hp.out.two_le
      omega
    rw [← h1, h2, Module.End.mul_apply, hb, h0, zero_smul, map_zero]
  · have h := congrArg (fun v : Additive V => ((Additive.toMul v : V) : Q)) (hb i j)
    simp only [hf] at h
    rw [h, ← ZMod.natCast_zmod_val (μ i j), Nat.cast_smul_eq_nsmul, toMul_nsmul,
      ZMod.natCast_zmod_val]
    rfl

end Group

end CFSG.ComponentClassification.OutcomeLocal
