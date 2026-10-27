module

public import CFSG.FeitThompson.Representations.ScalarCoordinateDegreeDivisibility
public import CFSG.FeitThompson.OddOrder.ScalarLinesCoordinateEmbedding
public import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality
public import CFSG.FeitThompson.Representations.AbelianGroupIrreducibleCharacters
public import CFSG.FeitThompson.Representations.AbelianInertiaInducedBlock
public import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
public import CFSG.FeitThompson.Representations.FixedFreeKernelMovingCharacterPair
public import CFSG.FeitThompson.Local.CoprimeActionNonnilpotentFixedSection
public import CFSG.FeitThompson.Representations.NormalInducedBlockPartition
public import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Pointwise SemidirectProduct

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open NormalInduction (conjClassFun conjClassFun_apply)

private theorem coprime_sub_one (p : ℕ) (hp : 2 ≤ p) : Nat.Coprime p (p - 1) := by
  have hd1 : Nat.gcd p (p - 1) ∣ p := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd p (p - 1) ∣ p - 1 := Nat.gcd_dvd_right _ _
  have hd3 : Nat.gcd p (p - 1) ∣ p - (p - 1) := Nat.dvd_sub hd1 hd2
  have he : p - (p - 1) = 1 := by omega
  rw [he] at hd3
  exact Nat.eq_one_of_dvd_one hd3

theorem exists_nsmul_eq_of_prime {q : ℕ} [NeZero q] (hq : q.Prime) {m : Fin q} (hm : m ≠ 0)
    (c : Fin q) : ∃ n : ℕ, n • m = c := by
  have : Fact q.Prime := ⟨hq⟩
  set e := ZMod.finEquiv q with he
  have hM : e m ≠ 0 := fun h => hm (by
    simpa using e.injective (show e m = e 0 by simpa using h))
  refine ⟨((e c) * (e m)⁻¹).val, e.injective ?_⟩
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id, inv_mul_cancel_right₀ hM]

section DiagScalar

variable {p q : ℕ} [hp : Fact p.Prime] {V U : Type*} [AddCommGroup V] [Module (ZMod p) V] [Group U]
  {W : Submodule (ZMod p) V} (hW : finrank (ZMod p) W = 1) (act : U →* (V ≃ₗ[ZMod p] V))
  (hmap : ∀ u : U, ∀ v ∈ W, act u v ∈ W)

private noncomputable def diagScalar (u : U) : (ZMod p)ˣ :=
  (existsUnique_units_forall_apply_eq_smul hW (act u) (hmap u)).choose

private theorem diagScalar_spec (u : U) {v : V} (hv : v ∈ W) :
    act u v = (diagScalar hW act hmap u : ZMod p) • v :=
  (existsUnique_units_forall_apply_eq_smul hW (act u) (hmap u)).choose_spec.1 v hv

private theorem diagScalar_unique (u : U) {c : (ZMod p)ˣ}
    (hc : ∀ v ∈ W, act u v = (c : ZMod p) • v) : c = diagScalar hW act hmap u :=
  (existsUnique_units_forall_apply_eq_smul hW (act u) (hmap u)).choose_spec.2 c hc

private noncomputable def diagScalarHom : U →* (ZMod p)ˣ where
  toFun := diagScalar hW act hmap
  map_one' := (diagScalar_unique hW act hmap 1 fun v _ => by simp).symm
  map_mul' u u' := by
    refine (diagScalar_unique hW act hmap (u * u') fun v hv => ?_).symm
    have h1 : act (u * u') v = act u (act u' v) := by rw [map_mul]; rfl
    rw [h1, diagScalar_spec hW act hmap u' hv, map_smul,
      diagScalar_spec hW act hmap u hv, smul_smul]
    push_cast
    rw [mul_comm]

private theorem apply_eq_diagScalarHom_smul (u : U) {v : V} (hv : v ∈ W) :
    act u v = (diagScalarHom hW act hmap u : ZMod p) • v := diagScalar_spec hW act hmap u hv

end DiagScalar

theorem coprime_natCard_of_diagonal_faithful {p q : ℕ} [hp : Fact p.Prime] {V U : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [Group U] [Finite U]
    {line : Fin q → Submodule (ZMod p) V} (hrank : ∀ i, finrank (ZMod p) (line i) = 1)
    (hsup : ⨆ i, line i = ⊤) (act : U →* (V ≃ₗ[ZMod p] V))
    (hmap : ∀ (u : U) (i : Fin q), ∀ v ∈ line i, act u v ∈ line i)
    (hfaithful : Function.Injective act) : Nat.Coprime p (Nat.card U) := by
  classical
  set F : U →* (Fin q → (ZMod p)ˣ) :=
    MonoidHom.pi fun i => diagScalarHom (hrank i) act (fun u => hmap u i) with hF
  have hFapply : ∀ (u : U) (i : Fin q),
      F u i = diagScalarHom (hrank i) act (fun u => hmap u i) u := fun _ _ => rfl
  have hFinj : Function.Injective F := by
    intro u u' huu'
    refine hfaithful ?_
    have hle : (⊤ : Submodule (ZMod p) V) ≤
        LinearMap.eqLocus (act u : V →ₗ[ZMod p] V) (act u' : V →ₗ[ZMod p] V) := by
      rw [← hsup]
      refine iSup_le fun i v hv => ?_
      change act u v = act u' v
      rw [apply_eq_diagScalarHom_smul (hrank i) act (fun u => hmap u i) u hv,
        apply_eq_diagScalarHom_smul (hrank i) act (fun u => hmap u i) u' hv]
      congr 2
      rw [← hFapply u i, ← hFapply u' i, congrFun huu' i]
    exact LinearEquiv.toLinearMap_injective (LinearMap.ext fun v => hle Submodule.mem_top (x := v))
  have hdvd : Nat.card U ∣ (p - 1) ^ q := by
    have h1 : Nat.card U ∣ Nat.card (Fin q → (ZMod p)ˣ) := Subgroup.card_dvd_of_injective F hFinj
    rwa [Nat.card_eq_fintype_card (α := Fin q → (ZMod p)ˣ), Fintype.card_fun, ZMod.card_units p,
      Fintype.card_fin] at h1
  exact Nat.Coprime.coprime_dvd_right hdvd ((coprime_sub_one p hp.out.two_le).pow_right q)

namespace ScalarCoordinateSystem

variable {p q : ℕ} [hp : Fact p.Prime] {V U : Type*} [AddCommGroup V] [Module (ZMod p) V]
  [Group U] (S : ScalarCoordinateSystem p q V U)

noncomputable def lineVec (i : Fin q) : V :=
  ((finrank_eq_one_iff'.1 (S.finrank_line i)).choose : V)

theorem lineVec_mem (i : Fin q) : S.lineVec i ∈ S.line i :=
  (finrank_eq_one_iff'.1 (S.finrank_line i)).choose.2

theorem lineVec_ne_zero (i : Fin q) : S.lineVec i ≠ 0 := by
  have h := (finrank_eq_one_iff'.1 (S.finrank_line i)).choose_spec.1
  simpa [lineVec, Submodule.coe_eq_zero] using h

theorem span_lineVec : ⊤ ≤ Submodule.span (ZMod p) (Set.range S.lineVec) := by
  rw [Submodule.span_range_eq_iSup, ← S.iSup_line]
  refine iSup_le fun i => ?_
  have h1 : (ZMod p) ∙ S.lineVec i ≤ S.line i :=
    (Submodule.span_singleton_le_iff_mem _ _).2 (S.lineVec_mem i)
  have h2 : finrank (ZMod p) ((ZMod p) ∙ S.lineVec i) = finrank (ZMod p) (S.line i) := by
    rw [finrank_span_singleton (S.lineVec_ne_zero i), S.finrank_line i]
  have : FiniteDimensional (ZMod p) (S.line i) :=
    Module.finite_of_finrank_eq_succ (n := 0) (S.finrank_line i)
  rw [← Submodule.eq_of_le_of_finrank_eq h1 h2]
  exact le_iSup (fun i => (ZMod p) ∙ S.lineVec i) i

noncomputable def lineBasis : Basis (Fin q) (ZMod p) V :=
  Basis.mk (S.indep_line.linearIndependent S.line S.lineVec_mem S.lineVec_ne_zero) S.span_lineVec

@[simp] theorem lineBasis_apply (i : Fin q) : S.lineBasis i = S.lineVec i := by
  simp [lineBasis]

theorem lineBasis_coord (i k : Fin q) :
    S.lineBasis.coord i (S.lineVec k) = if i = k then 1 else 0 := by
  rw [← S.lineBasis_apply k, Basis.coord_apply, Basis.repr_self]
  simp only [Finsupp.single_apply]
  exact if_congr eq_comm rfl rfl

theorem exists_smul_lineVec {k : Fin q} {v : V} (hv : v ∈ S.line k) :
    ∃ c : ZMod p, v = c • S.lineVec k := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff'.1 (S.finrank_line k)).choose_spec.2 ⟨v, hv⟩
  exact ⟨c, by simpa [lineVec, eq_comm] using congrArg Subtype.val hc⟩

noncomputable def twoCoordForm (i j : Fin q) : V →ₗ[ZMod p] ZMod p :=
  S.lineBasis.coord i + S.lineBasis.coord j

theorem twoCoordForm_lineVec_self {i j : Fin q} (hij : i ≠ j) :
    S.twoCoordForm i j (S.lineVec i) = 1 := by
  rw [twoCoordForm, LinearMap.add_apply, S.lineBasis_coord, S.lineBasis_coord, if_pos rfl,
    if_neg (Ne.symm hij), add_zero]

theorem twoCoordForm_lineVec_other {i j : Fin q} (hij : i ≠ j) :
    S.twoCoordForm i j (S.lineVec j) = 1 := by
  rw [twoCoordForm, LinearMap.add_apply, S.lineBasis_coord, S.lineBasis_coord, if_pos rfl,
    if_neg hij, zero_add]

theorem twoCoordForm_eq_zero_of_mem {i j k : Fin q} (hki : k ≠ i) (hkj : k ≠ j)
    {v : V} (hv : v ∈ S.line k) : S.twoCoordForm i j v = 0 := by
  obtain ⟨c, rfl⟩ := S.exists_smul_lineVec hv
  rw [twoCoordForm, LinearMap.add_apply, map_smul, map_smul, S.lineBasis_coord, S.lineBasis_coord,
    if_neg (Ne.symm hki), if_neg (Ne.symm hkj)]
  simp

theorem exists_baseHom_eq (x : S.base) : ∃ y : Multiplicative V, S.baseHom y = x :=
  ⟨S.baseEquiv.symm x, by rw [← S.baseEquiv_apply, MulEquiv.apply_symm_apply]⟩

theorem base_eq_range_inl :
    S.base = (SemidirectProduct.inl : Multiplicative V →* S.grp).range := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨y, hy⟩ := S.exists_baseHom_eq ⟨g, hg⟩
    exact ⟨y, by simpa using congrArg (fun x : S.base => (x : S.grp)) hy⟩
  · obtain ⟨y, rfl⟩ := hg
    exact S.inl_mem_base y

theorem base_sup_range_inr : S.base ⊔ (inr : U →* S.grp).range = ⊤ := by
  rw [S.base_eq_range_inl]; exact range_inl_sup_range_inr S.mulAutHom

theorem base_inf_range_inr : S.base ⊓ (inr : U →* S.grp).range = ⊥ := by
  rw [S.base_eq_range_inl]; exact range_inl_inf_range_inr S.mulAutHom

omit [AddCommGroup V] in
theorem natCard_multiplicative_eq : Nat.card (Multiplicative V) = Nat.card V :=
  Nat.card_congr (Equiv.refl _)

theorem natCard_base : Nat.card S.base = Nat.card V := by
  rw [Nat.card_congr S.baseEquiv.toEquiv.symm]
  exact natCard_multiplicative_eq

theorem natCard_range_inr : Nat.card ((inr : U →* S.grp).range) = Nat.card U :=
  (Nat.card_congr (Equiv.ofInjective _ (inr_injective (φ := S.mulAutHom)))).symm

theorem natCard_grp [Finite U] : Nat.card S.grp = Nat.card S.base * Nat.card U := by
  rw [S.natCard_base, ← natCard_multiplicative_eq (V := V)]
  exact SemidirectProduct.card

include S in
theorem finiteDimensional : FiniteDimensional (ZMod p) V := by
  have h1 : ∀ i, FiniteDimensional (ZMod p) (S.line i) := fun i =>
    Module.finite_of_finrank_eq_succ (n := 0) (S.finrank_line i)
  have h2 : FiniteDimensional (ZMod p) (⨆ i, S.line i : Submodule (ZMod p) V) :=
    Submodule.finiteDimensional_iSup _
  rw [S.iSup_line] at h2
  exact Module.Finite.equiv Submodule.topEquiv

include S in
theorem coprime_natCard_base_range_inr [Finite U] :
    (Nat.card S.base).Coprime (Nat.card ((inr : U →* S.grp).range)) := by
  have : FiniteDimensional (ZMod p) V := S.finiteDimensional
  rw [S.natCard_base, S.natCard_range_inr,
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := V), Nat.card_eq_fintype_card, ZMod.card]
  exact Nat.Coprime.pow_left _ S.coprime_card

theorem isMulCommutative_of_le_range_inr [IsMulCommutative U] {W : Subgroup S.grp}
    (hW : W ≤ (inr : U →* S.grp).range) : IsMulCommutative W := by
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨u, hu⟩ := hW x.2
  obtain ⟨u', hu'⟩ := hW y.2
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hu', ← map_mul, ← map_mul,
    isMulCommutative_iff.1 ‹IsMulCommutative U› u u']

theorem index_inertiaGroup_mul_natCard_inf [Finite U] {lam : S.base → ℂ}
    (hlam : lam ∈ Irr S.base) :
    (inertiaGroup S.base lam).index *
        Nat.card ((inr : U →* S.grp).range ⊓ inertiaGroup S.base lam : Subgroup S.grp)
      = Nat.card U := by
  have hV : Finite V := S.finite_of_finite_line
  set I := inertiaGroup S.base lam with hI
  have hbaseI : S.base ≤ I := le_inertiaGroup S.base (Irr_subset_classFun hlam)
  have hsub : Nat.card (S.base.subgroupOf I) = Nat.card S.base :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbaseI).toEquiv
  have hIcard : Nat.card S.base *
      Nat.card ((inr : U →* S.grp).range ⊓ I : Subgroup S.grp) = Nat.card I := by
    rw [← hsub, ← AbelianInertiaBlock.index_subgroupOf_inertiaGroup
      (U := (inr : U →* S.grp).range) hlam S.base_sup_range_inr S.base_inf_range_inr]
    exact Subgroup.card_mul_index (S.base.subgroupOf I)
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := S.base)) ?_
  calc Nat.card S.base * (I.index *
      Nat.card ((inr : U →* S.grp).range ⊓ I : Subgroup S.grp))
      = (Nat.card S.base *
          Nat.card ((inr : U →* S.grp).range ⊓ I : Subgroup S.grp)) * I.index := by ring
    _ = Nat.card I * I.index := by rw [hIcard]
    _ = Nat.card S.grp := Subgroup.card_mul_index I
    _ = Nat.card S.base * Nat.card U := S.natCard_grp

theorem not_subset_charValueKernel_of_mem_finset [Fintype S.grp]
    {lam : S.base → ℂ} (hlam : lam ∈ Irr S.base) (hlam1 : lam ≠ 1)
    {T : Finset (S.grp → ℂ)} (hT : ↑T ⊆ Irr S.grp)
    (hsum : indClassFun S.base lam = ∑ χ ∈ T, χ) {θ : S.grp → ℂ} (hθT : θ ∈ T) :
    ¬ ((S.base : Set S.grp) ⊆ charValueKernel θ) := by
  classical
  intro hker
  have hθ : θ ∈ Irr S.grp := hT (Finset.mem_coe.2 hθT)
  have h1 : cfInner (indClassFun S.base lam) θ = cfInner (resClassFun S.base θ) lam :=
    cfInner_indClassFun_eq_cfInner_resClassFun hθ hlam
  have h2 : cfInner (indClassFun S.base lam) θ = 1 := by
    rw [hsum, cfInner_sum_left, Finset.sum_congr rfl fun χ hχ =>
      cfInner_eq_ite_of_mem_Irr (hT (Finset.mem_coe.2 hχ)) hθ,
      Finset.sum_ite_eq' T θ (fun _ => (1 : ℂ)), if_pos hθT]
  have h3 : cfInner (resClassFun S.base θ) lam = 0 := by
    rw [resClassFun_eq_smul_one_of_subset_charValueKernel hker, cfInner_smul_left,
      cfInner_eq_ite_of_mem_Irr one_mem_Irr hlam, if_neg (Ne.symm hlam1), mul_zero]
  rw [h1, h3] at h2
  exact zero_ne_one h2

noncomputable def twoCoordChar (i j : Fin q) : Multiplicative V →* ℂˣ :=
  FixedFreeImage.dualChar (S.twoCoordForm i j)

theorem twoCoordChar_apply_eq_iff (i j : Fin q) (v w : V) :
    S.twoCoordChar i j (Multiplicative.ofAdd v)
      = S.twoCoordChar i j (Multiplicative.ofAdd w)
      ↔ S.twoCoordForm i j v = S.twoCoordForm i j w := by
  rw [twoCoordChar, FixedFreeImage.dualChar_apply, FixedFreeImage.dualChar_apply]
  exact ⟨FixedFreeImage.zmodCharUnit_ofAdd_inj, fun h => by rw [h]⟩

noncomputable def twoCoordBaseChar (i j : Fin q) : S.base → ℂ :=
  fun x => (S.twoCoordChar i j (S.baseEquiv.symm x) : ℂ)

theorem twoCoordBaseChar_baseHom (i j : Fin q) (y : Multiplicative V) :
    S.twoCoordBaseChar i j (S.baseHom y) = (S.twoCoordChar i j y : ℂ) := by
  rw [twoCoordBaseChar, ← S.baseEquiv_apply, MulEquiv.symm_apply_apply]

theorem twoCoordBaseChar_mem_Irr (i j : Fin q) : S.twoCoordBaseChar i j ∈ Irr S.base := by
  refine mem_Irr_of_comp_mulEquiv S.baseEquiv ?_
  have h : S.twoCoordBaseChar i j ∘ S.baseEquiv = linearCharFun (S.twoCoordChar i j) := by
    funext y
    rw [Function.comp_apply, S.baseEquiv_apply, S.twoCoordBaseChar_baseHom, linearCharFun_apply]
  rw [h]
  exact linearCharFun_mem_Irr _

@[simp] theorem twoCoordBaseChar_one (i j : Fin q) : S.twoCoordBaseChar i j 1 = 1 := by
  rw [twoCoordBaseChar]; simp

theorem twoCoordBaseChar_ne_one {i j : Fin q} (hij : i ≠ j) :
    S.twoCoordBaseChar i j ≠ (1 : S.base → ℂ) := by
  intro h
  have h1 := congrFun h (S.baseHom (Multiplicative.ofAdd (S.lineVec i)))
  rw [S.twoCoordBaseChar_baseHom] at h1
  have h2 : S.twoCoordChar i j (Multiplicative.ofAdd (S.lineVec i))
      = S.twoCoordChar i j (Multiplicative.ofAdd 0) := by
    refine Units.ext ?_
    rw [h1]
    simp
  rw [S.twoCoordChar_apply_eq_iff, map_zero, S.twoCoordForm_lineVec_self hij] at h2
  exact one_ne_zero h2

theorem act_eq_self_of_mem_lineCentralizer {i : Fin q} {u : U} (hu : u ∈ S.lineCentralizer i)
    {v : V} (hv : v ∈ S.line i) : S.act u v = v := S.mem_lineCentralizer.1 hu v hv

theorem twoCoordForm_act_of_mem_inf {u : U} {i j : Fin q}
    (hi : u ∈ S.lineCentralizer i) (hj : u ∈ S.lineCentralizer j) (v : V) :
    S.twoCoordForm i j (S.act u v) = S.twoCoordForm i j v := by
  have hmem : v ∈ ⨆ k, S.line k := by rw [S.iSup_line]; exact Submodule.mem_top
  refine Submodule.iSup_induction S.line
    (motive := fun w => S.twoCoordForm i j (S.act u w) = S.twoCoordForm i j w) hmem
    (fun k x hx => ?_) (by simp) (fun x y hx hy => by rw [map_add, map_add, map_add, hx, hy])
  by_cases hki : k = i
  · subst hki; rw [S.act_eq_self_of_mem_lineCentralizer hi hx]
  · by_cases hkj : k = j
    · subst hkj; rw [S.act_eq_self_of_mem_lineCentralizer hj hx]
    · rw [S.twoCoordForm_eq_zero_of_mem hki hkj hx,
        S.twoCoordForm_eq_zero_of_mem hki hkj (S.map_line u k x hx)]

theorem mem_inf_lineCentralizer_iff {i j : Fin q} (hij : i ≠ j) {u : U} :
    u ∈ S.lineCentralizer i ⊓ S.lineCentralizer j ↔
      ∀ v : V, S.twoCoordForm i j (S.act u v) = S.twoCoordForm i j v := by
  rw [Subgroup.mem_inf]
  refine ⟨fun h => S.twoCoordForm_act_of_mem_inf h.1 h.2, fun h => ?_⟩
  have key : ∀ k : Fin q, S.twoCoordForm i j (S.lineVec k) = 1 → u ∈ S.lineCentralizer k := by
    intro k hk
    have h1 := h (S.lineVec k)
    rw [S.act_apply_eq_lineScalar_smul k u (S.lineVec_mem k), map_smul, smul_eq_mul, hk,
      mul_one] at h1
    rw [S.lineCentralizer_eq_ker, MonoidHom.mem_ker]
    exact Units.ext (by simpa using h1)
  exact ⟨key i (S.twoCoordForm_lineVec_self hij), key j (S.twoCoordForm_lineVec_other hij)⟩

theorem inr_mem_inertiaGroup_iff {i j : Fin q} (hij : i ≠ j) (u : U) :
    (inr u : S.grp) ∈ inertiaGroup S.base (S.twoCoordBaseChar i j) ↔
      u⁻¹ ∈ S.lineCentralizer i ⊓ S.lineCentralizer j := by
  rw [mem_inertiaGroup, S.mem_inf_lineCentralizer_iff hij]
  constructor
  · intro h v
    have h1 := congrFun h (S.baseHom (Multiplicative.ofAdd v))
    rw [S.conjClassFun_inr_apply _ u (Multiplicative.ofAdd v), S.mulAutHom_apply,
      S.twoCoordBaseChar_baseHom, S.twoCoordBaseChar_baseHom] at h1
    exact (S.twoCoordChar_apply_eq_iff i j _ v).1 (Units.ext h1)
  · intro h
    funext x
    obtain ⟨y, rfl⟩ := S.exists_baseHom_eq x
    rw [S.conjClassFun_inr_apply _ u y]
    have hy : y = Multiplicative.ofAdd (Multiplicative.toAdd y) := rfl
    rw [hy, S.mulAutHom_apply, S.twoCoordBaseChar_baseHom, S.twoCoordBaseChar_baseHom]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) ((S.twoCoordChar_apply_eq_iff i j _ _).2 (h _))

theorem range_inr_inf_inertiaGroup_twoCoordBaseChar {i j : Fin q} (hij : i ≠ j) :
    (inr : U →* S.grp).range ⊓ inertiaGroup S.base (S.twoCoordBaseChar i j)
      = (S.lineCentralizer i ⊓ S.lineCentralizer j).map (inr : U →* S.grp) := by
  refine le_antisymm ?_ ?_
  · rintro g ⟨⟨u, rfl⟩, hg⟩
    exact ⟨u, by simpa using ((S.inr_mem_inertiaGroup_iff hij u).1 hg), rfl⟩
  · rintro g ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (S.inr_mem_inertiaGroup_iff hij u).2 (by simpa using hu)⟩

theorem natCard_range_inr_inf_inertiaGroup {i j : Fin q} (hij : i ≠ j) :
    Nat.card ((inr : U →* S.grp).range ⊓ inertiaGroup S.base (S.twoCoordBaseChar i j)
        : Subgroup S.grp)
      = Nat.card (S.lineCentralizer i ⊓ S.lineCentralizer j : Subgroup U) := by
  rw [S.range_inr_inf_inertiaGroup_twoCoordBaseChar hij]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ (inr_injective (φ := S.mulAutHom))).symm.toEquiv

theorem exists_mem_Irr_detecting_base_apply_one_eq_index [Finite U] [IsMulCommutative U]
    {i j : Fin q} (hij : i ≠ j) :
    ∃ θ ∈ Irr S.grp, ¬ ((S.base : Set S.grp) ⊆ charValueKernel θ) ∧
      θ 1 = ((S.lineCentralizer i ⊓ S.lineCentralizer j : Subgroup U).index : ℂ) := by
  classical
  have hV : Finite V := S.finite_of_finite_line
  have hgrpFin : Finite S.grp := inferInstance
  have : Fintype S.grp := Fintype.ofFinite _
  set lam := S.twoCoordBaseChar i j with hlamdef
  have hlam : lam ∈ Irr S.base := S.twoCoordBaseChar_mem_Irr i j
  have hcomm : IsMulCommutative
      ((inr : U →* S.grp).range ⊓ inertiaGroup S.base lam : Subgroup S.grp) :=
    S.isMulCommutative_of_le_range_inr inf_le_left
  obtain ⟨T, hTIrr, hTcard, hTsum, hTdeg⟩ :=
    AbelianInertiaBlock.exists_finset_Irr_indClassFun (U := (inr : U →* S.grp).range) hlam
      S.base_sup_range_inr S.base_inf_range_inr S.coprime_natCard_base_range_inr
  have hTne : T.Nonempty := by
    rw [← Finset.card_pos, hTcard]
    exact Nat.card_pos
  obtain ⟨θ, hθT⟩ := hTne
  refine ⟨θ, hTIrr (Finset.mem_coe.2 hθT),
    S.not_subset_charValueKernel_of_mem_finset hlam (S.twoCoordBaseChar_ne_one hij) hTIrr
      hTsum hθT, ?_⟩
  have hdeg : θ 1 = ((inertiaGroup S.base lam).index : ℂ) := by
    rw [hTdeg θ hθT, hlamdef, S.twoCoordBaseChar_one, mul_one]
  set A := S.lineCentralizer i ⊓ S.lineCentralizer j with hA
  have h1 : (inertiaGroup S.base lam).index * Nat.card A = Nat.card U := by
    rw [hA, ← S.natCard_range_inr_inf_inertiaGroup hij]
    exact S.index_inertiaGroup_mul_natCard_inf hlam
  have h2 : A.index * Nat.card A = Nat.card U := by
    rw [mul_comm]; exact Subgroup.card_mul_index A
  have hindex : (inertiaGroup S.base lam).index = A.index :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := A)) (h1.trans h2.symm)
  rw [hdeg, hindex]

end ScalarCoordinateSystem

theorem natCard_le_sq_of_inf_eq_bot {U : Type*} [Group U] [Finite U] {A B : Subgroup U} {a : ℕ}
    (hA : A.index = a) (hB : B.index = a) (hAB : A ⊓ B = ⊥) : Nat.card U ≤ a * a := by
  classical
  have hcardA : Nat.card A * a = Nat.card U := by rw [← hA]; exact Subgroup.card_mul_index A
  have hcardB : Nat.card B * a = Nat.card U := by rw [← hB]; exact Subgroup.card_mul_index B
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      rw [h, mul_zero] at hcardA
      exact (Nat.card_pos (α := U)).ne hcardA
    · exact h
  have hAeqB : Nat.card A = Nat.card B :=
    Nat.eq_of_mul_eq_mul_right ha0 (hcardA.trans hcardB.symm)
  have hprod : Nat.card ((A : Set U) * (B : Set U)) = Nat.card A * Nat.card B := by
    have h := natCard_mul_mul_natCard_inf A B
    rw [hAB] at h
    simpa using h
  have hle : Nat.card ((A : Set U) * (B : Set U)) ≤ Nat.card U :=
    Nat.card_le_card_of_injective (fun x : ((A : Set U) * (B : Set U)) => (x : U))
      Subtype.val_injective
  rw [hprod, hAeqB, ← hcardB, mul_comm (Nat.card B) a] at hle
  have hBle : Nat.card B ≤ a := Nat.le_of_mul_le_mul_right hle Nat.card_pos
  calc Nat.card U = Nat.card B * a := hcardB.symm
    _ ≤ a * a := Nat.mul_le_mul_right a hBle

structure TwoCoordinateKernelSetup (p q : ℕ) [Fact p.Prime] [NeZero q] (V U : Type*)
    [AddCommGroup V] [Module (ZMod p) V] [Group U] where
  three_le_q : 3 ≤ q
  q_prime : q.Prime
  q_ne_p : q ≠ p
  line : Fin q → Submodule (ZMod p) V
  finrank_line : ∀ i, finrank (ZMod p) (line i) = 1
  indep_line : iSupIndep line
  iSup_line : ⨆ i, line i = ⊤
  isMulCommutative : IsMulCommutative U
  act : U →* (V ≃ₗ[ZMod p] V)
  map_line : ∀ (u : U) (i : Fin q), ∀ v ∈ line i, act u v ∈ line i
  faithful : Function.Injective act
  shiftAct : V ≃ₗ[ZMod p] V
  shiftAct_pow : shiftAct ^ q = 1
  map_line_shift : ∀ i, (line i).map (shiftAct : V →ₗ[ZMod p] V) = line (i + 1)
  shiftAut : MulAut U
  act_shiftAut : ∀ u, act (shiftAut u) = shiftAct * act u * shiftAct⁻¹
  coprime_q : Nat.Coprime q (p * Nat.card U)
  centralizer_shift : ∀ u : U, shiftAut u = u → u = 1

namespace TwoCoordinateKernelSetup

variable {p q : ℕ} [hp : Fact p.Prime] [NeZero q] {V U : Type*} [AddCommGroup V]
  [Module (ZMod p) V] [Group U] [Finite U] (T : TwoCoordinateKernelSetup p q V U)

noncomputable def toScalar : ScalarCoordinateSystem p q V U where
  two_le_q := by have := T.three_le_q; omega
  line := T.line
  finrank_line := T.finrank_line
  indep_line := T.indep_line
  iSup_line := T.iSup_line
  act := T.act
  map_line := T.map_line
  coprime_card :=
    coprime_natCard_of_diagonal_faithful T.finrank_line T.iSup_line T.act T.map_line T.faithful

@[simp] theorem toScalar_line : T.toScalar.line = T.line := (rfl)

@[simp] theorem toScalar_act : T.toScalar.act = T.act := (rfl)

noncomputable abbrev lineCentralizer (i : Fin q) : Subgroup U :=
  T.toScalar.lineCentralizer i

theorem iInf_lineCentralizer_eq_bot : (⨅ i, T.lineCentralizer i) = ⊥ := by
  rw [← T.toScalar.totalCentralizer_eq_iInf]
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  refine T.faithful ?_
  rw [map_one]
  exact LinearEquiv.ext (T.toScalar.mem_totalCentralizer.1 hu)

theorem mem_lineCentralizer_iff {i : Fin q} {u : U} :
    u ∈ T.lineCentralizer i ↔ ∀ v ∈ T.line i, T.act u v = v := by
  rw [lineCentralizer, T.toScalar.mem_lineCentralizer]
  simp only [T.toScalar_line, T.toScalar_act]

omit [Finite U] in
theorem shiftAct_act_comm (u : U) (v : V) :
    T.act (T.shiftAut u) (T.shiftAct v) = T.shiftAct (T.act u v) := by
  rw [T.act_shiftAut]
  simp

theorem shiftAut_mem_lineCentralizer_iff (u : U) (i : Fin q) :
    T.shiftAut u ∈ T.lineCentralizer (i + 1) ↔ u ∈ T.lineCentralizer i := by
  rw [T.mem_lineCentralizer_iff, T.mem_lineCentralizer_iff]
  constructor
  · intro h v hv
    have h1 : T.shiftAct v ∈ T.line (i + 1) := by
      rw [← T.map_line_shift i]
      exact ⟨v, hv, rfl⟩
    have h2 := h _ h1
    rw [T.shiftAct_act_comm] at h2
    exact T.shiftAct.injective h2
  · intro h v' hv'
    rw [← T.map_line_shift i] at hv'
    obtain ⟨w, hw, rfl⟩ := hv'
    change T.act (T.shiftAut u) (T.shiftAct w) = T.shiftAct w
    rw [T.shiftAct_act_comm, h w hw]

theorem map_shiftAut_lineCentralizer (i : Fin q) :
    (T.lineCentralizer i).map (T.shiftAut : U →* U) = T.lineCentralizer (i + 1) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (T.shiftAut_mem_lineCentralizer_iff u i).2 hu
  · intro hx
    refine ⟨T.shiftAut.symm x, ?_, by simp⟩
    refine (T.shiftAut_mem_lineCentralizer_iff (T.shiftAut.symm x) i).1 ?_
    simpa using hx

private theorem eq_of_le_of_index_eq {A B : Subgroup U} (hAB : A ≤ B) {a : ℕ} (hA : A.index = a)
    (hB : B.index = a) : A = B := by
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso
      have h1 : Nat.card A * a = Nat.card U := by rw [← hA]; exact Subgroup.card_mul_index A
      rw [h, mul_zero] at h1
      exact (Nat.card_pos (α := U)).ne h1
    · exact h
  have h1 : Nat.card A * a = Nat.card U := by rw [← hA]; exact Subgroup.card_mul_index A
  have h2 : Nat.card B * a = Nat.card U := by rw [← hB]; exact Subgroup.card_mul_index B
  have hcard : Nat.card A = Nat.card B := Nat.eq_of_mul_eq_mul_right ha0 (h1.trans h2.symm)
  refine SetLike.coe_set_eq.1 (Set.eq_of_subset_of_ncard_le (by exact_mod_cast hAB) ?_
    (Set.toFinite _))
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact hcard.ge

theorem inf_lineCentralizer_eq_bot {a : ℕ} (ha : ∀ i, (T.lineCentralizer i).index = a)
    (ha1 : 1 < a) (hua : a < Nat.card U)
    (hDeg : ∀ θ ∈ Irr T.toScalar.grp,
      ¬ ((T.toScalar.base : Set T.toScalar.grp) ⊆ charValueKernel θ) →
        θ 1 = (a : ℂ) ∨ θ 1 = (Nat.card U : ℂ))
    {i j : Fin q} (hij : i ≠ j) :
    T.lineCentralizer i ⊓ T.lineCentralizer j = ⊥ := by
  classical
  have : IsMulCommutative U := T.isMulCommutative
  have hConj : ∀ i : Fin q, (T.lineCentralizer i).map (T.shiftAut : U →* U)
      = T.lineCentralizer (i + 1) := T.map_shiftAut_lineCentralizer
  obtain ⟨θ, hθ, hker, hθ1⟩ :=
    T.toScalar.exists_mem_Irr_detecting_base_apply_one_eq_index hij
  set A := T.lineCentralizer i ⊓ T.lineCentralizer j with hA
  have hcase := hDeg θ hθ hker
  rw [hθ1] at hcase
  have hcase' : A.index = a ∨ A.index = Nat.card U := by
    rcases hcase with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  rcases hcase' with hAa | hAu
  ·
    exfalso
    have hAieq : A = T.lineCentralizer i := eq_of_le_of_index_eq inf_le_left hAa (ha i)
    have hAjeq : A = T.lineCentralizer j := eq_of_le_of_index_eq inf_le_right hAa (ha j)
    have hij' : T.lineCentralizer i = T.lineCentralizer j := hAieq ▸ hAjeq
    have hmap : ∀ (n : ℕ) (l : Fin q),
        (T.lineCentralizer l).map ((T.shiftAut ^ n : MulAut U) : U →* U)
          = T.lineCentralizer (l + n • (1 : Fin q)) := by
      intro n
      induction n with
      | zero => intro l; simp [show ((1 : MulAut U) : U →* U) = MonoidHom.id U from rfl]
      | succ n ih =>
        intro l
        have hpow : ((T.shiftAut ^ (n + 1) : MulAut U) : U →* U)
            = ((T.shiftAut : MulAut U) : U →* U).comp
              ((T.shiftAut ^ n : MulAut U) : U →* U) := by
          ext x
          simp [pow_succ']
        rw [hpow, ← Subgroup.map_map, ih l, hConj]
        congr 1
        rw [succ_nsmul]
        abel
    have hstep : ∀ k : Fin q, T.lineCentralizer k = T.lineCentralizer (k + (j - i)) := by
      intro k
      obtain ⟨n, hn⟩ := exists_nsmul_eq_of_prime T.q_prime
        (show (1 : Fin q) ≠ 0 from by
          intro hcon
          have hval := congrArg Fin.val hcon
          rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by have := T.three_le_q; omega)] at hval
          omega) (k - i)
      have h1 := hmap n i
      have h2 := hmap n j
      rw [hij', h2, hn] at h1
      have hik : i + (k - i) = k := by abel
      have hjk : j + (k - i) = k + (j - i) := by abel
      rw [hik, hjk] at h1
      exact h1.symm
    have hm : j - i ≠ 0 := sub_ne_zero_of_ne (Ne.symm hij)
    have hiter : ∀ (n : ℕ) (k : Fin q),
        T.lineCentralizer k = T.lineCentralizer (k + n • (j - i)) := by
      intro n
      induction n with
      | zero => intro k; simp
      | succ n ih =>
        intro k
        rw [ih k, hstep (k + n • (j - i))]
        congr 1
        rw [succ_nsmul]
        abel
    have hall : ∀ k : Fin q, T.lineCentralizer i = T.lineCentralizer k := by
      intro k
      obtain ⟨n, hn⟩ := exists_nsmul_eq_of_prime T.q_prime hm (k - i)
      have h := hiter n i
      rw [hn] at h
      have hik : i + (k - i) = k := by abel
      rwa [hik] at h
    have hbot : T.lineCentralizer i = ⊥ := by
      have hiInf : T.lineCentralizer i = ⨅ k, T.lineCentralizer k :=
        le_antisymm (le_iInf fun k => (hall k).le) (iInf_le _ i)
      rw [hiInf, T.iInf_lineCentralizer_eq_bot]
    have hcontra : a = Nat.card U := by
      have h := ha i
      rw [hbot, Subgroup.index_bot] at h
      exact h.symm
    omega
  ·
    have hcardA : Nat.card A * A.index = Nat.card U := Subgroup.card_mul_index A
    rw [hAu] at hcardA
    have h1 : Nat.card A = 1 := by
      have hU := Nat.card_pos (α := U)
      have hAp := Nat.card_pos (α := A)
      nlinarith
    exact Subgroup.card_eq_one.1 h1

theorem natCard_le_sq {a : ℕ} (ha : ∀ i, (T.lineCentralizer i).index = a)
    (ha1 : 1 < a) (hua : a < Nat.card U)
    (hDeg : ∀ θ ∈ Irr T.toScalar.grp,
      ¬ ((T.toScalar.base : Set T.toScalar.grp) ⊆ charValueKernel θ) →
        θ 1 = (a : ℂ) ∨ θ 1 = (Nat.card U : ℂ)) :
    Nat.card U ≤ a * a := by
  have hq : 3 ≤ q := T.three_le_q
  have h01 : (0 : Fin q) ≠ (1 : Fin q) := by
    intro h
    have hval := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at hval
    omega
  exact natCard_le_sq_of_inf_eq_bot (ha 0) (ha 1)
    (T.inf_lineCentralizer_eq_bot ha ha1 hua hDeg h01)

end TwoCoordinateKernelSetup

end CFSG.FeitThompson
