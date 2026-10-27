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
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

section Module

variable (A : Type*) [Ring A]
variable {M : Type*} [AddCommGroup M] [Module A M]

@[expose] def SubquotientIso (S : Type*) [AddCommGroup S] [Module A S]
    (X : Submodule A M × Submodule A M) : Prop :=
  Nonempty ((X.2 ⧸ X.1.comap X.2.subtype) ≃ₗ[A] S)

@[expose] noncomputable def factorCount (s : CompositionSeries (Submodule A M)) (S : Type*)
    [AddCommGroup S] [Module A S] : ℕ :=
  (Finset.univ.filter fun i : Fin s.length => SubquotientIso A S (s i.castSucc, s i.succ)).card

variable (M) in
@[expose] noncomputable def compositionMultiplicity (S : Type*) [AddCommGroup S] [Module A S] :
    ℕ :=
  if h : ∃ s : CompositionSeries (Submodule A M), s.head = ⊥ ∧ s.last = ⊤ then
    factorCount A h.choose S else 0

variable {A}

theorem subquotientIso_congr {S S' : Type*} [AddCommGroup S] [Module A S] [AddCommGroup S']
    [Module A S'] (e : S ≃ₗ[A] S') (X : Submodule A M × Submodule A M) :
    SubquotientIso A S X ↔ SubquotientIso A S' X :=
  ⟨fun ⟨f⟩ => ⟨f.trans e⟩, fun ⟨f⟩ => ⟨f.trans e.symm⟩⟩

theorem subquotientIso_iff_of_iso {S : Type*} [AddCommGroup S] [Module A S]
    {X Y : Submodule A M × Submodule A M} (h : JordanHolderLattice.Iso X Y) :
    SubquotientIso A S X ↔ SubquotientIso A S Y :=
  ⟨fun ⟨e⟩ => ⟨(JordanHolderLattice.Iso.linearEquiv h).symm.trans e⟩,
    fun ⟨e⟩ => ⟨(JordanHolderLattice.Iso.linearEquiv h).trans e⟩⟩

theorem factorCount_eq_of_equivalent {s₁ s₂ : CompositionSeries (Submodule A M)}
    (h : s₁.Equivalent s₂) (S : Type*) [AddCommGroup S] [Module A S] :
    factorCount A s₁ S = factorCount A s₂ S := by
  obtain ⟨e, he⟩ := h
  unfold factorCount
  exact Finset.card_equiv e fun i => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact subquotientIso_iff_of_iso (he i)

theorem compositionMultiplicity_eq_factorCount (s : CompositionSeries (Submodule A M))
    (h₁ : s.head = ⊥) (h₂ : s.last = ⊤) (S : Type*) [AddCommGroup S] [Module A S] :
    compositionMultiplicity A M S = factorCount A s S := by
  have h : ∃ s : CompositionSeries (Submodule A M), s.head = ⊥ ∧ s.last = ⊤ := ⟨s, h₁, h₂⟩
  rw [compositionMultiplicity, dite_eq_left h]
  exact factorCount_eq_of_equivalent (CompositionSeries.jordan_holder _ _
    (h.choose_spec.1.trans h₁.symm) (h.choose_spec.2.trans h₂.symm)) S

theorem compositionMultiplicity_congr_right {S S' : Type*} [AddCommGroup S] [Module A S]
    [AddCommGroup S'] [Module A S'] (e : S ≃ₗ[A] S') :
    compositionMultiplicity A M S = compositionMultiplicity A M S' := by
  unfold compositionMultiplicity
  split_ifs with h
  · unfold factorCount
    congr 1
    exact Finset.filter_congr fun i _ => subquotientIso_congr e _
  · rfl

theorem factorCount_smash (p q : CompositionSeries (Submodule A M)) (h : p.last = q.head)
    (S : Type*) [AddCommGroup S] [Module A S] :
    factorCount A (p.smash q h) S = factorCount A p S + factorCount A q S := by
  unfold factorCount
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  change ∑ j : Fin (p.length + q.length), _ = _
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    change (if SubquotientIso A S ((p.smash q h).toFun (Fin.castAdd q.length i).castSucc,
      (p.smash q h).toFun (Fin.castAdd q.length i).succ) then 1 else 0) = _
    rw [RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd]
  · refine Finset.sum_congr rfl fun i _ => ?_
    change (if SubquotientIso A S ((p.smash q h).toFun (Fin.natAdd p.length i).castSucc,
      (p.smash q h).toFun (Fin.natAdd p.length i).succ) then 1 else 0) = _
    rw [RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd]

variable (A) in
noncomputable def subquotientMapEquiv {N : Type*} [AddCommGroup N] [Module A N]
    (f : N →ₗ[A] M) (hf : Function.Injective f) (P Q : Submodule A N) :
    (Q ⧸ P.comap Q.subtype) ≃ₗ[A] (Q.map f ⧸ (P.map f).comap (Q.map f).subtype) :=
  Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Q) (by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hxQ⟩, hxP, hxy⟩
      refine ⟨x, hxP, ?_⟩
      have := congrArg Subtype.val hxy
      simpa using this
    · rintro ⟨x, hxP, hxy⟩
      obtain ⟨x', hx'Q, hx'y⟩ := hy
      have hxx' : x = x' := hf (hxy.trans hx'y.symm)
      subst hxx'
      exact ⟨⟨x, hx'Q⟩, hxP, Subtype.ext (by simpa using hxy)⟩)

variable (A) in
noncomputable def subquotientComapEquiv {P : Type*} [AddCommGroup P] [Module A P]
    (g : M →ₗ[A] P) (hg : Function.Surjective g) (Q₁ Q₂ : Submodule A P) :
    (Q₂.comap g ⧸ (Q₁.comap g).comap (Q₂.comap g).subtype) ≃ₗ[A] (Q₂ ⧸ Q₁.comap Q₂.subtype) :=
  let φ : Q₂.comap g →ₗ[A] Q₂ := g.restrict fun _ hx => hx
  let ψ := (Q₁.comap Q₂.subtype).mkQ ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : LinearMap.ker ψ = (Q₁.comap g).comap (Q₂.comap g).subtype := by
    ext ⟨x, hx⟩
    simp [ψ, φ, Submodule.Quotient.mk_eq_zero]
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective ψ hψ)

theorem factorCount_map_injective {N : Type*} [AddCommGroup N] [Module A N]
    (f : N →ₗ[A] M) (hf : Function.Injective f) (t : CompositionSeries (Submodule A N))
    (S : Type*) [AddCommGroup S] [Module A S] :
    factorCount A (t.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩) S =
      factorCount A t S := by
  unfold factorCount
  refine Finset.card_equiv (Equiv.refl _) fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨e⟩ => ⟨(subquotientMapEquiv A f hf _ _).trans e⟩,
    fun ⟨e⟩ => ⟨(subquotientMapEquiv A f hf _ _).symm.trans e⟩⟩

theorem factorCount_map_surjective {P : Type*} [AddCommGroup P] [Module A P]
    (g : M →ₗ[A] P) (hg : Function.Surjective g) (s : CompositionSeries (Submodule A P))
    (S : Type*) [AddCommGroup S] [Module A S] :
    factorCount A (s.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩) S =
      factorCount A s S := by
  unfold factorCount
  refine Finset.card_equiv (Equiv.refl _) fun i => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun ⟨e⟩ => ⟨(subquotientComapEquiv A g hg _ _).symm.trans e⟩,
    fun ⟨e⟩ => ⟨(subquotientComapEquiv A g hg _ _).trans e⟩⟩

theorem compositionMultiplicity_eq_add_of_exact {N P : Type*} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] [IsNoetherian A N] [IsArtinian A N] [IsNoetherian A P]
    [IsArtinian A P] (f : N →ₗ[A] M) (g : M →ₗ[A] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g) (S : Type*) [AddCommGroup S]
    [Module A S] :
    compositionMultiplicity A M S =
      compositionMultiplicity A N S + compositionMultiplicity A P S := by
  obtain ⟨t, ht₁, ht₂⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A N
  obtain ⟨s, hs₁, hs₂⟩ := exists_compositionSeries_of_isNoetherian_isArtinian A P
  let t' : CompositionSeries (Submodule A M) :=
    t.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩
  let s' : CompositionSeries (Submodule A M) :=
    s.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩
  have hfg : t'.last = s'.head := by
    simp only [t', s', RelSeries.last_map, RelSeries.head_map, ht₂, hs₁]
    change Submodule.map f ⊤ = Submodule.comap g ⊥
    rw [Submodule.map_top, Submodule.comap_bot, LinearMap.exact_iff.mp H]
  have hr₁ : (t'.smash s' hfg).head = ⊥ := by
    rw [RelSeries.head_smash]
    simp only [t', RelSeries.head_map, ht₁]
    exact Submodule.map_bot f
  have hr₂ : (t'.smash s' hfg).last = ⊤ := by
    rw [RelSeries.last_smash]
    simp only [s', RelSeries.last_map, hs₂]
    exact Submodule.comap_top g
  rw [compositionMultiplicity_eq_factorCount _ hr₁ hr₂,
    compositionMultiplicity_eq_factorCount t ht₁ ht₂,
    compositionMultiplicity_eq_factorCount s hs₁ hs₂, factorCount_smash,
    factorCount_map_injective f hf, factorCount_map_surjective g hg]

theorem compositionMultiplicity_of_subsingleton [Subsingleton M] (S : Type*) [AddCommGroup S]
    [Module A S] : compositionMultiplicity A M S = 0 := by
  have h₂ : (RelSeries.singleton _ (⊥ : Submodule A M) : CompositionSeries (Submodule A M)).last =
      ⊤ := Subsingleton.elim _ _
  rw [compositionMultiplicity_eq_factorCount _ rfl h₂]
  unfold factorCount
  simp

theorem compositionMultiplicity_of_isSimpleModule [IsSimpleModule A M] (S : Type*)
    [AddCommGroup S] [Module A S] :
    compositionMultiplicity A M S = if Nonempty (M ≃ₗ[A] S) then 1 else 0 := by
  have : IsSimpleOrder (Submodule A M) := (isSimpleModule_iff A M).mp inferInstance
  let s : CompositionSeries (Submodule A M) :=
    { length := 1
      toFun := ![⊥, ⊤]
      step := fun i => by
        fin_cases i
        exact bot_covBy_top }
  rw [compositionMultiplicity_eq_factorCount s rfl rfl]
  unfold factorCount
  have e : (((⊤ : Submodule A M) ⧸ (⊥ : Submodule A M).comap (⊤ : Submodule A M).subtype)) ≃ₗ[A]
      M := (Submodule.quotEquivOfEqBot _ (by rw [Submodule.comap_bot, Submodule.ker_subtype])).trans
        Submodule.topEquiv
  have hiff : SubquotientIso A S (s (0 : Fin 1).castSucc, s (0 : Fin 1).succ) ↔
      Nonempty (M ≃ₗ[A] S) :=
    ⟨fun ⟨f⟩ => ⟨e.symm.trans f⟩, fun ⟨f⟩ => ⟨e.trans f⟩⟩
  by_cases hS : Nonempty (M ≃ₗ[A] S)
  · rw [ite_eq_left hS, Finset.card_eq_one]
    refine ⟨0, ?_⟩
    ext i
    fin_cases i
    simpa using hiff.mpr hS
  · rw [ite_eq_right hS, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _
    fin_cases i
    exact fun h => hS (hiff.mp h)

theorem compositionMultiplicity_congr_left {M' : Type*} [AddCommGroup M'] [Module A M']
    (e : M ≃ₗ[A] M') (S : Type*) [AddCommGroup S] [Module A S] :
    compositionMultiplicity A M S = compositionMultiplicity A M' S := by
  by_cases h : ∃ s : CompositionSeries (Submodule A M), s.head = ⊥ ∧ s.last = ⊤
  · obtain ⟨s, hs₁, hs₂⟩ := h
    let s' : CompositionSeries (Submodule A M') :=
      s.map ⟨Submodule.map e.toLinearMap, Submodule.map_covBy_of_injective e.injective⟩
    have hs'₁ : s'.head = ⊥ := by
      simp only [s', RelSeries.head_map, hs₁]
      exact Submodule.map_bot _
    have hs'₂ : s'.last = ⊤ := by
      simp only [s', RelSeries.last_map, hs₂]
      exact (Submodule.map_top _).trans (LinearMap.range_eq_top.mpr e.surjective)
    rw [compositionMultiplicity_eq_factorCount s hs₁ hs₂,
      compositionMultiplicity_eq_factorCount s' hs'₁ hs'₂,
      factorCount_map_injective e.toLinearMap e.injective]
  · have h' : ¬ ∃ s : CompositionSeries (Submodule A M'), s.head = ⊥ ∧ s.last = ⊤ := by
      rintro ⟨s, hs₁, hs₂⟩
      refine h ⟨s.map ⟨Submodule.map e.symm.toLinearMap,
        Submodule.map_covBy_of_injective e.symm.injective⟩, ?_, ?_⟩
      · simp only [RelSeries.head_map, hs₁]
        exact Submodule.map_bot _
      · simp only [RelSeries.last_map, hs₂]
        exact (Submodule.map_top _).trans (LinearMap.range_eq_top.mpr e.symm.surjective)
    unfold compositionMultiplicity
    rw [dite_eq_right h, dite_eq_right h']

theorem compositionMultiplicity_eq_submodule_add_quotient [IsNoetherian A M] [IsArtinian A M]
    (N : Submodule A M) (S : Type*) [AddCommGroup S] [Module A S] :
    compositionMultiplicity A M S =
      compositionMultiplicity A N S + compositionMultiplicity A (M ⧸ N) S :=
  compositionMultiplicity_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
    N.mkQ_surjective (LinearMap.exact_subtype_mkQ N) S

end Module

section Algebra

variable (k : Type*) [Field k] {A : Type*} [Ring A] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

theorem isNoetherian_of_finiteDimensional [FiniteDimensional k M] : IsNoetherian A M :=
  isNoetherian_of_tower k inferInstance

theorem isArtinian_of_finiteDimensional [FiniteDimensional k M] : IsArtinian A M :=
  isArtinian_of_tower k inferInstance

omit [Field k] in
theorem fin_telescope {n : ℕ} (f : Fin (n + 1) → ℕ) (a : Fin n → ℕ)
    (h : ∀ i : Fin n, f i.succ = f i.castSucc + a i) : f (Fin.last n) = f 0 + ∑ i, a i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h' := ih (fun i => f i.castSucc) (fun i => a i.castSucc) fun i => by
      have := h i.castSucc
      rw [Fin.succ_castSucc] at this
      exact this
    rw [Fin.castSucc_zero] at h'
    rw [Fin.sum_univ_castSucc, ← add_assoc, ← h']
    have := h (Fin.last n)
    rw [Fin.succ_last] at this
    exact this

theorem finrank_eq_sum_finrank_factor [FiniteDimensional k M]
    (s : CompositionSeries (Submodule A M)) (h₁ : s.head = ⊥) (h₂ : s.last = ⊤) :
    Module.finrank k M = ∑ i : Fin s.length,
      Module.finrank k (s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype) := by
  have hfin : ∀ Q : Submodule A M, FiniteDimensional k Q := fun Q =>
    Module.Finite.of_injective (Q.subtype.restrictScalars k) Q.injective_subtype
  have hstep : ∀ i : Fin s.length, Module.finrank k (s i.succ) = Module.finrank k (s i.castSucc) +
      Module.finrank k (s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype) := by
    intro i
    have hle : s i.castSucc ≤ s i.succ := (s.lt_succ i).le
    set N := (s i.castSucc).comap (s i.succ).subtype
    have h1 := Submodule.finrank_quotient_add_finrank (N.restrictScalars k)
    have h2 : Module.finrank k (s i.succ ⧸ N.restrictScalars k) =
        Module.finrank k (s i.succ ⧸ N) :=
      (Submodule.Quotient.restrictScalarsEquiv k N).finrank_eq
    have h3 : Module.finrank k (N.restrictScalars k) = Module.finrank k (s i.castSucc) :=
      ((Submodule.comapSubtypeEquivOfLe hle).restrictScalars k).finrank_eq
    lia
  have h := fin_telescope (fun j => Module.finrank k (s j)) _ hstep
  have hb : Module.finrank k (s 0) = 0 := by
    change Module.finrank k s.head = 0
    rw [h₁]
    exact Module.finrank_zero_of_subsingleton
  have ht : Module.finrank k (s (Fin.last s.length)) = Module.finrank k M := by
    change Module.finrank k s.last = _
    rw [h₂]
    exact (Submodule.topEquiv.restrictScalars k).finrank_eq
  simp only at h
  rw [hb, zero_add, ht] at h
  exact h

end Algebra

section Representation

open Representation

variable {k G : Type*} [CommRing k] [Monoid G]
variable {V W V' W' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup V'] [Module k V'] [AddCommGroup W'] [Module k W']

@[expose] noncomputable def repMultiplicity (ρ : Representation k G V)
    (σ : Representation k G W) : ℕ :=
  compositionMultiplicity (MonoidAlgebra k G) ρ.asModule σ.asModule

noncomputable def asModuleEquivOfEquiv {ρ : Representation k G V} {σ : Representation k G W}
    (φ : ρ.Equiv σ) : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule :=
  LinearEquiv.ofLinearMap (IntertwiningMap.equivLinearMapAsModule ρ σ φ.toIntertwiningMap)
    (IntertwiningMap.equivLinearMapAsModule σ ρ φ.symm.toIntertwiningMap)
    (LinearMap.ext fun x => φ.apply_symm_apply x) (LinearMap.ext fun x => φ.symm_apply_apply x)

noncomputable def equivOfAsModuleEquiv {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) : ρ.Equiv σ :=
  Representation.Equiv.mk ((ρ.asModuleEquiv.symm.trans (e.restrictScalars k)).trans
    σ.asModuleEquiv) fun g => by
      ext x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
        LinearEquiv.restrictScalars_apply]
      rw [ρ.asModuleEquiv_symm_map_rho, e.map_smul, σ.asModuleEquiv_map_smul, asAlgebraHom_of]

theorem nonempty_equiv_iff (ρ : Representation k G V) (σ : Representation k G W) :
    Nonempty (ρ.Equiv σ) ↔ Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule) :=
  ⟨fun ⟨φ⟩ => ⟨asModuleEquivOfEquiv φ⟩, fun ⟨e⟩ => ⟨equivOfAsModuleEquiv e⟩⟩

theorem repMultiplicity_congr_left {ρ : Representation k G V} {ρ' : Representation k G V'}
    (φ : ρ.Equiv ρ') (σ : Representation k G W) :
    repMultiplicity ρ σ = repMultiplicity ρ' σ :=
  compositionMultiplicity_congr_left (asModuleEquivOfEquiv φ) _

theorem repMultiplicity_congr_right (ρ : Representation k G V) {σ : Representation k G W}
    {σ' : Representation k G W'} (φ : σ.Equiv σ') :
    repMultiplicity ρ σ = repMultiplicity ρ σ' :=
  compositionMultiplicity_congr_right (asModuleEquivOfEquiv φ)

end Representation

section FieldRepresentation

open Representation

variable {k G : Type*} [Field k] [Monoid G]
variable {V₁ V₂ V₃ W : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃] [AddCommGroup W] [Module k W]

theorem repMultiplicity_eq_add_of_exact [FiniteDimensional k V₁] [FiniteDimensional k V₃]
    {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂} {ρ₃ : Representation k G V₃}
    (f : ρ₁.IntertwiningMap ρ₂) (g : ρ₂.IntertwiningMap ρ₃) (hf : Function.Injective f)
    (hg : Function.Surjective g) (H : Function.Exact f g) (σ : Representation k G W) :
    repMultiplicity ρ₂ σ = repMultiplicity ρ₁ σ + repMultiplicity ρ₃ σ := by
  have := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ₁.asModule)
  have := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ₁.asModule)
  have := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ₃.asModule)
  have := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ₃.asModule)
  exact compositionMultiplicity_eq_add_of_exact (IntertwiningMap.equivLinearMapAsModule ρ₁ ρ₂ f)
    (IntertwiningMap.equivLinearMapAsModule ρ₂ ρ₃ g) hf hg H σ.asModule

theorem repMultiplicity_of_isIrreducible {ρ : Representation k G V₁} (hρ : ρ.IsIrreducible)
    (σ : Representation k G W) :
    repMultiplicity ρ σ = if Nonempty (ρ.Equiv σ) then 1 else 0 := by
  have : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp hρ
  rw [repMultiplicity, compositionMultiplicity_of_isSimpleModule]
  exact if_congr (nonempty_equiv_iff ρ σ).symm rfl rfl

theorem exists_invariant_fixed_mod_of_repMultiplicity_trivial_pos {ρ : Representation k G V₁}
    (h : 0 < repMultiplicity ρ (Representation.trivial k G k)) :
    ∃ N : Submodule k V₁, (∀ g, ∀ x ∈ N, ρ g x ∈ N) ∧ ∃ v ∉ N, ∀ g, ρ g v - v ∈ N := by
  unfold repMultiplicity compositionMultiplicity at h
  split_ifs at h with hs
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp h
    obtain ⟨e₀⟩ := (Finset.mem_filter.mp hi).2
    let P : Submodule (MonoidAlgebra k G) ρ.asModule := hs.choose i.castSucc
    let Q : Submodule (MonoidAlgebra k G) ρ.asModule := hs.choose i.succ
    let e : (Q ⧸ P.comap Q.subtype) ≃ₗ[MonoidAlgebra k G] (Representation.trivial k G k).asModule :=
      e₀
    let t : (Representation.trivial k G k).asModule :=
      (Representation.trivial k G k).asModuleEquiv.symm 1
    obtain ⟨q, hq⟩ := Submodule.mkQ_surjective (P.comap Q.subtype) (e.symm t)
    refine ⟨(P.restrictScalars k).map ρ.asModuleEquiv.toLinearMap, ?_,
      ρ.asModuleEquiv (q : ρ.asModule), ?_, ?_⟩
    · rintro g x ⟨p, hp, rfl⟩
      refine ⟨MonoidAlgebra.of k G g • p, P.smul_mem _ hp, ?_⟩
      change ρ.asModuleEquiv (MonoidAlgebra.of k G g • p) = ρ g (ρ.asModuleEquiv p)
      rw [ρ.asModuleEquiv_map_smul, asAlgebraHom_of]
    · rintro ⟨p, hp, hpq⟩
      have hqp : (q : ρ.asModule) = p := ρ.asModuleEquiv.injective hpq.symm
      have hq0 : Submodule.mkQ (P.comap Q.subtype) q = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (by
          change (q : ρ.asModule) ∈ P
          rw [hqp]
          exact hp)
      rw [hq] at hq0
      have ht : t = 0 := by simpa using congrArg e hq0
      have h10 : (1 : k) = 0 := by
        simpa [t] using congrArg (Representation.trivial k G k).asModuleEquiv ht
      exact one_ne_zero h10
    · intro g
      have hfix : MonoidAlgebra.of k G g • t = t := by
        apply (Representation.trivial k G k).asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul, asAlgebraHom_of]
        simp
      have hmem : (MonoidAlgebra.of k G g • q - q : Q) ∈ P.comap Q.subtype := by
        rw [← Submodule.Quotient.mk_eq_zero]
        change Submodule.mkQ (P.comap Q.subtype) (MonoidAlgebra.of k G g • q - q) = 0
        rw [map_sub, map_smul, hq]
        apply e.injective
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, hfix, sub_self, map_zero]
      refine ⟨((MonoidAlgebra.of k G g • q - q : Q) : ρ.asModule), hmem, ?_⟩
      change ρ.asModuleEquiv (MonoidAlgebra.of k G g • (q : ρ.asModule) - q) = _
      rw [map_sub, ρ.asModuleEquiv_map_smul, asAlgebraHom_of]
  · exact absurd h (lt_irrefl 0)

end FieldRepresentation

end CFSG.Semidihedral.Principal
