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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open Module

section Heisenberg

variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U] [FiniteDimensional E U]

theorem three_dvd_finrank_of_heisenberg (b c : U ≃ₗ[E] U) (μ : E) (hμ : μ ^ 3 = 1) (hμ1 : μ ≠ 1)
    (h : (b : U →ₗ[E] U) ∘ₗ (c : U →ₗ[E] U) = μ • ((c : U →ₗ[E] U) ∘ₗ (b : U →ₗ[E] U))) :
    3 ∣ Module.finrank E U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdet := congrArg LinearMap.det h
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_comp] at hdet
  have hb : LinearMap.det (b : U →ₗ[E] U) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact (LinearEquiv.det b).ne_zero
  have hc : LinearMap.det (c : U →ₗ[E] U) ≠ 0 := by
    rw [← LinearEquiv.coe_det]; exact (LinearEquiv.det c).ne_zero
  have hne : LinearMap.det (b : U →ₗ[E] U) * LinearMap.det (c : U →ₗ[E] U) ≠ 0 :=
    mul_ne_zero hb hc
  have hpow : μ ^ Module.finrank E U = 1 := by
    apply mul_right_cancel₀ hne
    rw [one_mul]
    calc μ ^ Module.finrank E U * (LinearMap.det (b : U →ₗ[E] U) * LinearMap.det (c : U →ₗ[E] U))
        = μ ^ Module.finrank E U *
            (LinearMap.det (c : U →ₗ[E] U) * LinearMap.det (b : U →ₗ[E] U)) := by
          rw [mul_comm (LinearMap.det (b : U →ₗ[E] U))]
      _ = LinearMap.det (b : U →ₗ[E] U) * LinearMap.det (c : U →ₗ[E] U) := hdet.symm
  have hord : orderOf μ = 3 := orderOf_eq_prime hμ hμ1
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hpow

theorem false_of_commute_lowRank (a b : U ≃ₗ[E] U) (ω : E) (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1)
    (hab : ∀ u, a (b u) = ω • b (a u)) (N : U →ₗ[E] U) (hNa : ∀ u, N (a u) = a (N u))
    (hNb : ∀ u, N (b u) = b (N u)) (h0 : 0 < finrank E (LinearMap.range N))
    (h3 : finrank E (LinearMap.range N) < 3) : False := by
  set W := LinearMap.range N with hW
  have hmap : ∀ e : U ≃ₗ[E] U, (∀ u, N (e u) = e (N u)) → W.map (e : U →ₗ[E] U) = W := by
    intro e he
    apply le_antisymm
    · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, he u⟩
    · rintro w ⟨u, rfl⟩
      refine ⟨N (e.symm u), ⟨e.symm u, rfl⟩, ?_⟩
      show e (N (e.symm u)) = N u
      rw [← he, e.apply_symm_apply]
  let a' : W ≃ₗ[E] W := LinearEquiv.ofSubmodules a W W (hmap a hNa)
  let b' : W ≃ₗ[E] W := LinearEquiv.ofSubmodules b W W (hmap b hNb)
  have h' : (a' : W →ₗ[E] W) ∘ₗ (b' : W →ₗ[E] W) = ω • ((b' : W →ₗ[E] W) ∘ₗ (a' : W →ₗ[E] W)) := by
    ext w
    simp [a', b', hab]
  have := three_dvd_finrank_of_heisenberg a' b' ω hω3 hω1 h'
  omega

end Heisenberg

section PseudoReflection

variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U]

@[expose] noncomputable def pseudoReflection (φ : U →ₗ[E] E) (v : U) (h : 1 + φ v ≠ 0) :
    LinearMap.GeneralLinearGroup E U :=
  Units.mk (LinearMap.id + φ.smulRight v) (LinearMap.id - (1 + φ v)⁻¹ • φ.smulRight v)
    (by
      ext x
      have : (1 + φ v) * (1 + φ v)⁻¹ = 1 := mul_inv_cancel₀ h
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.id_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_sub, map_add,
        map_smul, smul_eq_mul, Module.End.one_apply]
      match_scalars
      · ring
      · linear_combination (-(φ x)) * this)
    (by
      ext x
      have : (1 + φ v) * (1 + φ v)⁻¹ = 1 := mul_inv_cancel₀ h
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.id_apply,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_sub, map_add,
        map_smul, smul_eq_mul, Module.End.one_apply]
      match_scalars
      · ring
      · linear_combination (-(φ x)) * this)

theorem pseudoReflection_apply (φ : U →ₗ[E] E) (v : U) (h : 1 + φ v ≠ 0) (x : U) :
    ((pseudoReflection φ v h : LinearMap.GeneralLinearGroup E U) : Module.End E U) x =
      x + φ x • v := rfl

end PseudoReflection

section LowRank

variable {E U ι : Type*} [Field E] [AddCommGroup U] [Module E U]

theorem gl_apply_inv_apply (g : LinearMap.GeneralLinearGroup E U) (x : U) :
    (g : Module.End E U) (((g⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) x) = x := by
  rw [← Module.End.mul_apply, Units.mul_inv]; rfl

theorem commutator_pseudoReflection_apply (g h : LinearMap.GeneralLinearGroup E U) (φ : U →ₗ[E] E)
    (v : U) (hh : ∀ x, (h : Module.End E U) x = x + φ x • v) (x : U) :
    ∃ c₁ c₂ : E, ((g * h * g⁻¹ * h⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) x - x =
      c₁ • v + c₂ • (g : Module.End E U) v := by
  set y : U := ((h⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) x with hy
  have hhy : (h : Module.End E U) y = x := gl_apply_inv_apply h x
  refine ⟨-φ y, φ (((g⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) y), ?_⟩
  have h1 : y + φ y • v = x := by rw [← hh y]; exact hhy
  have h2 : ((g * h * g⁻¹ * h⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) x =
      (g : Module.End E U) ((h : Module.End E U)
        (((g⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) y)) := by
    simp [Units.val_mul, hy]
  rw [h2, hh, map_add, map_smul, gl_apply_inv_apply g y]
  rw [← h1]
  module

theorem finrank_range_commutator_sub_one_le_two [FiniteDimensional E U]
    (g h : LinearMap.GeneralLinearGroup E U) (φ : U →ₗ[E] E) (v : U)
    (hh : ∀ x, (h : Module.End E U) x = x + φ x • v) :
    finrank E (LinearMap.range
      (((g * h * g⁻¹ * h⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) - 1)) ≤ 2 := by
  classical
  have hle : LinearMap.range
      (((g * h * g⁻¹ * h⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) - 1) ≤
      Submodule.span E (({v, (g : Module.End E U) v} : Finset U) : Set U) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨c₁, c₂, hc⟩ := commutator_pseudoReflection_apply g h φ v hh x
    have hx : ((((g * h * g⁻¹ * h⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) - 1) x) =
        ((g * h * g⁻¹ * h⁻¹ : LinearMap.GeneralLinearGroup E U) : Module.End E U) x - x := by
      simp
    rw [hx, hc]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  calc _ ≤ finrank E (Submodule.span E (({v, (g : Module.End E U) v} : Finset U) : Set U)) :=
        Submodule.finrank_mono hle
    _ ≤ ({v, (g : Module.End E U) v} : Finset U).card := finrank_span_finset_le_card _
    _ ≤ 2 := Finset.card_le_two

variable [Fintype ι] [DecidableEq ι]

theorem coord_basis_apply (e : Basis ι E U) (i j : ι) :
    e.coord i (e j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h; simp [Basis.coord_apply, Basis.repr_self]
  · simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, h, Ne.symm h]

theorem eq_smul_one_of_commute_pseudoReflections (e : Basis ι E U) {μ : E} (hμ : μ ≠ 1)
    (n : Module.End E U) (d : ι → Module.End E U)
    (hd : ∀ i x, d i x = x + ((μ - 1) * e.coord i x) • e i)
    (t : ∀ i j : ι, i ≠ j → Module.End E U)
    (ht : ∀ i j (hij : i ≠ j) x, t i j hij x = x + (e.coord i x - e.coord j x) • (e j - e i))
    (hnd : ∀ i x, n (d i x) = d i (n x))
    (hnt : ∀ i j (hij : i ≠ j) x, n (t i j hij x) = t i j hij (n x)) :
    ∃ c : E, n = c • (1 : Module.End E U) := by
  have hμ' : μ - 1 ≠ 0 := sub_ne_zero.mpr hμ
  have h1 : ∀ i, n (e i) = (e.coord i (n (e i))) • e i := by
    intro i
    have h := hnd i (e i)
    rw [hd, hd, coord_basis_apply] at h
    simp only [if_true, mul_one, map_add, map_smul] at h
    have h2 : (μ - 1) • n (e i) = ((μ - 1) * e.coord i (n (e i))) • e i := add_left_cancel h
    rw [mul_smul] at h2
    exact smul_right_injective U hμ' h2
  have h2 : ∀ i j, i ≠ j → e.coord i (n (e i)) = e.coord j (n (e j)) := by
    intro i j hij
    have h := hnt i j hij (e i)
    have hti : t i j hij (e i) = e j := by
      rw [ht, coord_basis_apply, coord_basis_apply, if_pos rfl, if_neg (Ne.symm hij)]
      simp
    rw [hti, h1 i, map_smul, hti] at h
    have h3 : (e.coord i (n (e i))) • e j = (e.coord j (n (e j))) • e j := by
      rw [← h1 j, ← h]
    have hne : e j ≠ 0 := e.ne_zero j
    exact smul_left_injective E hne h3
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, e.ext fun i => (hι.false i).elim⟩
  · refine ⟨e.coord i₀ (n (e i₀)), e.ext fun i => ?_⟩
    by_cases hi : i = i₀
    · subst hi
      rw [LinearMap.smul_apply, Module.End.one_apply, ← h1]
    · rw [LinearMap.smul_apply, Module.End.one_apply, h2 i₀ i (Ne.symm hi)]
      exact h1 i

theorem exists_lowRank_of_normal_nonabelian [FiniteDimensional E U] (e : Basis ι E U) {μ : E}
    (hμ : μ ≠ 1) {F N : Subgroup (LinearMap.GeneralLinearGroup E U)}
    (hnormal : ∀ f ∈ F, ∀ n ∈ N, f * n * f⁻¹ ∈ N)
    (hδ : ∀ i, ∃ d ∈ F, ∀ x, (d : Module.End E U) x = x + ((μ - 1) * e.coord i x) • e i)
    (hτ : ∀ i j, i ≠ j → ∃ t ∈ F, ∀ x,
      (t : Module.End E U) x = x + (e.coord i x - e.coord j x) • (e j - e i))
    (hna : ∃ n₁ ∈ N, ∃ n₂ ∈ N, n₁ * n₂ ≠ n₂ * n₁) :
    ∃ n ∈ N, 0 < finrank E (LinearMap.range ((n : Module.End E U) - 1)) ∧
      finrank E (LinearMap.range ((n : Module.End E U) - 1)) < 3 := by
  classical
  choose d hdF hd using hδ
  choose t htF ht using hτ
  have hA : ∃ n ∈ N, ∃ h ∈ F, ∃ (φ : U →ₗ[E] E) (v : U),
      (∀ x, (h : Module.End E U) x = x + φ x • v) ∧ n * h ≠ h * n := by
    by_contra hcon
    push Not at hcon
    obtain ⟨n₁, hn₁, n₂, hn₂, hne⟩ := hna
    have hscalar : ∀ n ∈ N, ∃ c : E, (n : Module.End E U) = c • 1 := by
      intro n hn
      refine eq_smul_one_of_commute_pseudoReflections e hμ (n : Module.End E U)
        (fun i => (d i : Module.End E U)) (fun i x => hd i x)
        (fun i j hij => (t i j hij : Module.End E U)) (fun i j hij x => ht i j hij x)
        (fun i x => ?_) (fun i j hij x => ?_)
      · have := hcon n hn (d i) (hdF i) ((μ - 1) • e.coord i) (e i) (fun x => by
          rw [hd]; simp)
        have h2 := congrArg
          (fun u : LinearMap.GeneralLinearGroup E U => (u : Module.End E U) x) this
        simpa using h2
      · have := hcon n hn (t i j hij) (htF i j hij) (e.coord i - e.coord j) (e j - e i)
          (fun x => by rw [ht]; simp)
        have h2 := congrArg
          (fun u : LinearMap.GeneralLinearGroup E U => (u : Module.End E U) x) this
        simpa using h2
    obtain ⟨c₁, h₁⟩ := hscalar n₁ hn₁
    obtain ⟨c₂, h₂⟩ := hscalar n₂ hn₂
    apply hne
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, h₁, h₂]
    ext x
    simp [smul_smul, mul_comm]
  obtain ⟨n, hn, h, hF, φ, v, hh, hnh⟩ := hA
  have hc : n * h * n⁻¹ * h⁻¹ ∈ N := by
    have := N.mul_mem hn (hnormal h hF n⁻¹ (N.inv_mem hn))
    simpa [mul_assoc] using this
  have hc1 : n * h * n⁻¹ * h⁻¹ ≠ 1 := by
    intro h1
    apply hnh
    have : n * h * n⁻¹ = h := by
      have := congrArg (fun u => u * h) h1
      simpa [mul_assoc] using this
    calc n * h = n * h * n⁻¹ * n := by group
      _ = h * n := by rw [this]
  refine ⟨n * h * n⁻¹ * h⁻¹, hc, ?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot, sub_eq_zero]
    intro h1
    apply hc1
    apply Units.ext
    rw [h1]; rfl
  · have := finrank_range_commutator_sub_one_le_two n h φ v hh
    omega

theorem exists_pseudoReflection_diag [FiniteDimensional E U] (e : Basis ι E U) {μ : E}
    (hμ0 : μ ≠ 0) (i : ι) :
    ∃ d : LinearMap.GeneralLinearGroup E U,
      (∀ x, (d : Module.End E U) x = x + ((μ - 1) * e.coord i x) • e i) ∧
      ∀ k, (d : Module.End E U) (e k) = (if k = i then μ else 1) • e k := by
  have h : 1 + ((μ - 1) • e.coord i) (e i) ≠ 0 := by
    simpa [coord_basis_apply] using hμ0
  refine ⟨pseudoReflection ((μ - 1) • e.coord i) (e i) h, fun x => ?_, fun k => ?_⟩
  · rw [pseudoReflection_apply]; simp
  · rw [pseudoReflection_apply]
    by_cases hk : k = i
    · subst hk; simp [coord_basis_apply]; module
    · simp [coord_basis_apply, hk, Ne.symm hk]

theorem exists_pseudoReflection_swap [FiniteDimensional E U] (e : Basis ι E U) {i j : ι}
    (hij : i ≠ j) :
    ∃ t : LinearMap.GeneralLinearGroup E U,
      (∀ x, (t : Module.End E U) x = x + (e.coord i x - e.coord j x) • (e j - e i)) ∧
      ∀ k, (t : Module.End E U) (e k) = e (Equiv.swap i j k) := by
  have h : 1 + (e.coord i - e.coord j) (e j - e i) ≠ 0 := by
    have : (1 : E) + (e.coord i - e.coord j) (e j - e i) = -1 := by
      simp [coord_basis_apply, hij, Ne.symm hij]
    rw [this]; exact neg_ne_zero.mpr one_ne_zero
  refine ⟨pseudoReflection (e.coord i - e.coord j) (e j - e i) h, fun x => ?_, fun k => ?_⟩
  · rw [pseudoReflection_apply]; simp
  · rw [pseudoReflection_apply]
    by_cases hki : k = i
    · subst hki
      simp [coord_basis_apply, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [coord_basis_apply, hij, Ne.symm hij, Equiv.swap_apply_right]
      · simp [coord_basis_apply, hki, hkj, Ne.symm hki, Ne.symm hkj,
          Equiv.swap_apply_of_ne_of_ne hki hkj]

theorem exists_lowRank_of_normal_nonabelian_gl [FiniteDimensional E U] (e : Basis ι E U) {μ : E}
    (hμ : μ ≠ 1) (hμ0 : μ ≠ 0) {N : Subgroup (LinearMap.GeneralLinearGroup E U)}
    (hnormal : ∀ f n, n ∈ N → f * n * f⁻¹ ∈ N)
    (hna : ∃ n₁ ∈ N, ∃ n₂ ∈ N, n₁ * n₂ ≠ n₂ * n₁) :
    ∃ n ∈ N, 0 < finrank E (LinearMap.range ((n : Module.End E U) - 1)) ∧
      finrank E (LinearMap.range ((n : Module.End E U) - 1)) < 3 := by
  refine exists_lowRank_of_normal_nonabelian e hμ (F := ⊤) (N := N)
    (fun f _ n hn => hnormal f n hn) ?_ ?_ hna
  · intro i
    obtain ⟨d, hd, -⟩ := exists_pseudoReflection_diag e hμ0 i
    exact ⟨d, Subgroup.mem_top _, hd⟩
  · intro i j hij
    obtain ⟨t, ht, -⟩ := exists_pseudoReflection_swap e hij
    exact ⟨t, Subgroup.mem_top _, ht⟩

end LowRank

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
