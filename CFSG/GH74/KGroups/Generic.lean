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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

namespace CFSG.GH74.KGroups

@[expose] def ElemAb {G : Type*} [Group G] (p : ℕ) (A : Subgroup G) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ p = 1

@[expose] def pow3list {G : Type*} [Group G] (x y : G) : List G :=
  [1, x, x ^ 2, y, x * y, x ^ 2 * y, y ^ 2, x * y ^ 2, x ^ 2 * y ^ 2]

theorem exists_mem_notMem_list {G : Type*} [Group G] (R : Subgroup G) (L : List G)
    (h : L.length < Nat.card R) : ∃ z ∈ R, z ∉ L := by
  classical
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by omega)
  by_contra hcon
  push Not at hcon
  have : Nat.card R ≤ L.length := by
    have hinj : Function.Injective
        (fun z : R => (⟨z.1, List.mem_toFinset.2 (hcon z.1 z.2)⟩ : L.toFinset)) := by
      intro a b hab
      have h2 : a.1 = b.1 := congrArg (Subtype.val : L.toFinset → G) hab
      exact Subtype.ext h2
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card (α := L.toFinset), Fintype.card_coe] at h1
    exact h1.trans (List.toFinset_card_le L)
  omega

theorem elemAb_card_le {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (R : Subgroup G)
    (hR : ElemAb p R) (k : ℕ) (hk : ¬ p ^ (k + 1) ∣ Nat.card G) : Nat.card R ≤ p ^ k := by
  have hp : IsPGroup p R := by
    intro g
    refine ⟨1, ?_⟩
    have := hR.2 g g.2
    apply Subtype.ext
    simpa using this
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have hdvd : Nat.card R ∣ Nat.card G := Subgroup.card_subgroup_dvd_card R
  rw [hm] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hmk : k + 1 ≤ m := by
    by_contra hc
    push Not at hc
    have : m ≤ k := by omega
    exact absurd (Nat.pow_le_pow_right (Fact.out : p.Prime).pos this) (by omega)
  exact hk ((pow_dvd_pow p hmk).trans hdvd)

theorem exists_two_independent {G : Type*} [Group G] (R : Subgroup G)
    (hcard : 3 < Nat.card R) :
    ∃ x ∈ R, ∃ y ∈ R, x ≠ 1 ∧ y ∉ ([1, x, x ^ 2] : List G) := by
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ R, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card R ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
    omega
  obtain ⟨y, hy, hyn⟩ := exists_mem_notMem_list R [1, x, x ^ 2] (by simp; omega)
  exact ⟨x, hx, y, hy, hx1, hyn⟩

theorem exists_three_independent {G : Type*} [Group G] (R : Subgroup G)
    (hcard : 9 < Nat.card R) :
    ∃ x ∈ R, ∃ y ∈ R, ∃ z ∈ R, x ≠ 1 ∧ y ∉ ([1, x, x ^ 2] : List G) ∧ z ∉ pow3list x y := by
  obtain ⟨x, hx, y, hy, hx1, hyn⟩ := exists_two_independent R (by omega)
  obtain ⟨z, hz, hzn⟩ := exists_mem_notMem_list R (pow3list x y) (by simp [pow3list]; omega)
  exact ⟨x, hx, y, hy, z, hz, hx1, hyn, hzn⟩

theorem pow3list_map {G H : Type*} [Group G] [Group H] (f : G →* H) (x y : G) :
    (pow3list x y).map f = pow3list (f x) (f y) := by
  simp [pow3list, map_mul, map_pow]

theorem mem_pow3list_of_inj {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (x y z : G) (h : f z ∈ pow3list (f x) (f y)) :
    z ∈ pow3list x y := by
  rw [← pow3list_map] at h
  exact (List.mem_map_of_injective hf).1 h

theorem pow3list_subset {G : Type*} [Group G] (B : Subgroup G) {x y : G} (hx : x ∈ B) (hy : y ∈ B)
    {w : G} (hw : w ∈ pow3list x y) : w ∈ B := by
  simp only [pow3list, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact B.one_mem
    | exact hx
    | exact B.pow_mem hx 2
    | exact hy
    | exact B.mul_mem hx hy
    | exact B.mul_mem (B.pow_mem hx 2) hy
    | exact B.pow_mem hy 2
    | exact B.mul_mem hx (B.pow_mem hy 2)
    | exact B.mul_mem (B.pow_mem hx 2) (B.pow_mem hy 2)

@[expose] def evalW {M : Type*} [Monoid M] (a b : M) : List Bool → M
  | [] => 1
  | false :: w => a * evalW a b w
  | true :: w => b * evalW a b w

theorem map_evalW {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (a b : M) (w : List Bool) :
    f (evalW a b w) = evalW (f a) (f b) w := by
  induction w with
  | nil => simp [evalW]
  | cons c w ih => cases c <;> simp [evalW, ih]

@[expose] def PairInv {M : Type*} [Monoid M] (ws : List (List Bool × ℕ)) (a b : M) : Prop :=
  ∀ wk ∈ ws, orderOf (evalW a b wk.1) = wk.2

theorem pairInv_map {G : Type*} [Group G] (φ : G ≃* G) (ws : List (List Bool × ℕ)) {a b : G}
    (h : PairInv ws a b) : PairInv ws (φ a) (φ b) := by
  intro wk hwk
  have h1 := h wk hwk
  have h2 := map_evalW φ.toMonoidHom a b wk.1
  have h3 : φ (evalW a b wk.1) = evalW (φ a) (φ b) wk.1 := h2
  rw [← h3, ← h1]
  exact MulEquiv.orderOf_eq φ _

theorem card_mulAut_le {G : Type*} [Group G] [Finite G] (a b : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (I : G → G → Prop)
    (hI : ∀ φ : MulAut G, I a b → I (φ a) (φ b)) (hab : I a b) :
    Nat.card (MulAut G) ≤ Nat.card {p : G × G // I p.1 p.2} := by
  classical
  refine Nat.card_le_card_of_injective (fun φ => ⟨(φ a, φ b), hI φ hab⟩) ?_
  intro φ ψ h
  simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
  apply MulEquiv.ext
  intro x
  have heq : (φ : G →* G) = (ψ : G →* G) :=
    MonoidHom.eq_of_eqOn_dense hgen (by
      intro y hy
      rcases hy with rfl | hy
      · exact h.1
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact h.2)
  exact DFunLike.congr_fun heq x

@[expose] def blockHom (n m : ℕ) :
    Equiv.Perm (Fin n) × Equiv.Perm (Fin m) →* Equiv.Perm (Fin (n + m)) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin n) (Fin m))

theorem blockHom_injective (n m : ℕ) : Function.Injective (blockHom n m) := by
  intro x y h
  have h1 : (Equiv.permCongrHom finSumFinEquiv) (Equiv.Perm.sumCongrHom (Fin n) (Fin m) x) =
      (Equiv.permCongrHom finSumFinEquiv) (Equiv.Perm.sumCongrHom (Fin n) (Fin m) y) := h
  exact Equiv.Perm.sumCongrHom_injective ((Equiv.permCongrHom finSumFinEquiv).injective h1)

theorem blockIso {n m : ℕ} (a b : Equiv.Perm (Fin n)) (a' b' : Equiv.Perm (Fin m))
    (A B : Equiv.Perm (Fin (n + m))) (hA : blockHom n m (a, a') = A)
    (hB : blockHom n m (b, b') = B) (P Q : Subgroup _) (hP : P = Subgroup.closure {a, b})
    (hQ : Q = Subgroup.closure {A, B}) (ha : a ∈ P) (hb : b ∈ P)
    (hcard : Nat.card Q = Nat.card P) :
    ∃ φ : P ≃* Q, ((φ ⟨a, ha⟩ : Q) : Equiv.Perm (Fin (n + m))) = A ∧
      ((φ ⟨b, hb⟩ : Q) : Equiv.Perm (Fin (n + m))) = B := by
  classical
  set H : Subgroup (Equiv.Perm (Fin n) × Equiv.Perm (Fin m)) :=
    Subgroup.closure {(a, a'), (b, b')} with hH
  have hmapθ : H.map (blockHom n m) = Q := by
    rw [hH, MonoidHom.map_closure, hQ]
    congr 1
    ext x
    simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rw [hA, hB]
  have hmem1 : (a, a') ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have hmem2 : (b, b') ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hfst : H.map (MonoidHom.fst _ _) = P := by
    rw [hH, MonoidHom.map_closure, hP]
    congr 1
    ext x
    simp
  have hHP : ∀ h : H, h.1.1 ∈ P := by
    intro h
    rw [← hfst]
    exact ⟨h.1, h.2, rfl⟩
  let f : H →* P := ((MonoidHom.fst _ _).comp H.subtype).codRestrict P hHP
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hfst] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨y, hy⟩, rfl⟩
  have hcardH : Nat.card H = Nat.card Q := by
    rw [← hmapθ]
    exact (Subgroup.card_map_of_injective (blockHom_injective n m)).symm
  have hbij : Function.Bijective f := by
    have : Finite P := inferInstance
    exact hsurj.bijective_of_nat_card_le (by rw [hcardH, hcard])
  let e1 := MulEquiv.ofBijective f hbij
  let e2 : H ≃* Q := (Subgroup.equivMapOfInjective H (blockHom n m) (blockHom_injective n m)).trans
    (MulEquiv.subgroupCongr hmapθ)
  refine ⟨e1.symm.trans e2, ?_, ?_⟩
  · have h1 : e1.symm ⟨a, ha⟩ = ⟨(a, a'), hmem1⟩ := by
      apply e1.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    have h2 : ((e2 ⟨(a, a'), hmem1⟩ : Q) : Equiv.Perm (Fin (n + m))) = blockHom n m (a, a') := rfl
    rw [MulEquiv.trans_apply, h1, h2, hA]
  · have h1 : e1.symm ⟨b, hb⟩ = ⟨(b, b'), hmem2⟩ := by
      apply e1.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    have h2 : ((e2 ⟨(b, b'), hmem2⟩ : Q) : Equiv.Perm (Fin (n + m))) = blockHom n m (b, b') := rfl
    rw [MulEquiv.trans_apply, h1, h2, hB]

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] (P : Subgroup G) [Finite P] (σ : G)
    (h : ∀ x ∈ P, σ * x * σ⁻¹ ∈ P) : σ ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : P → P := fun y => ⟨σ * y * σ⁻¹, h y y.2⟩
  have hinj : Function.Injective f := by
    intro y z hyz
    have := congrArg Subtype.val hyz
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨σ * x * σ⁻¹, hx⟩
  have := congrArg Subtype.val hy
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact y.2

theorem exists_mulEquiv_of_squeeze {G : Type*} [Group G] (P A : Subgroup G) [Finite P] [Finite A]
    (hnorm : A ≤ Subgroup.normalizer (P : Set G))
    (hcent : ∀ σ ∈ A, (∀ x ∈ P, σ * x = x * σ) → σ = 1)
    (hcard : Nat.card (MulAut P) ≤ Nat.card A) :
    ∃ Φ : A ≃* MulAut P, ∀ (σ : A) (x : P), ((Φ σ x : P) : G) = σ * x * (σ : G)⁻¹ := by
  let ρ : A →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hρ : ∀ (σ : A) (x : P), ((ρ σ x : P) : G) = σ * x * (σ : G)⁻¹ := by
    intro σ x
    rfl
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro σ hσ
    have h1 : ρ σ = 1 := hσ
    apply Subtype.ext
    apply hcent σ σ.2
    intro x hx
    have h2 := hρ σ ⟨x, hx⟩
    rw [h1] at h2
    simp only [MulAut.one_apply] at h2
    have h3 : x = (σ : G) * x * (σ : G)⁻¹ := h2
    calc (σ : G) * x = (σ : G) * x * (σ : G)⁻¹ * σ := by group
      _ = x * σ := by rw [← h3]
  have hbij : Function.Bijective ρ := hinj.bijective_of_nat_card_le hcard
  exact ⟨MulEquiv.ofBijective ρ hbij, fun σ x => hρ σ x⟩

structure AutModel (K : Type*) [Group K] (G : Type*) [Group G] where
  P : Subgroup G
  A : Subgroup G
  e : K ≃* P
  Φ : MulAut K ≃* A
  spec : ∀ (φ : MulAut K) (x : K),
    ((e (φ x) : P) : G) = (Φ φ : G) * (e x : G) * (Φ φ : G)⁻¹

@[expose] def AutModel.ofRealization {K G : Type*} [Group K] [Group G] (P A : Subgroup G)
    (e : K ≃* P) (Φ' : A ≃* MulAut P)
    (hΦ' : ∀ (σ : A) (x : P), ((Φ' σ x : P) : G) = σ * x * (σ : G)⁻¹) : AutModel K G where
  P := P
  A := A
  e := e
  Φ := (MulAut.congr e).trans Φ'.symm
  spec := by
    intro φ x
    have h := hΦ' (Φ'.symm (MulAut.congr e φ)) (e x)
    rw [MulEquiv.apply_symm_apply] at h
    have h2 : (MulAut.congr e φ) (e x) = e (φ x) := by
      simp [MulAut.congr_apply]
    rw [h2] at h
    exact h

variable {K : Type*} [Group K] {G : Type*} [Group G] (M : AutModel K G)

theorem AutModel.Φ_pow (φ : MulAut K) (k : ℕ) : (M.Φ (φ ^ k) : G) = (M.Φ φ : G) ^ k := by
  rw [map_pow]; rfl

theorem AutModel.Φ_one : (M.Φ 1 : G) = 1 := by
  rw [map_one]; rfl

theorem AutModel.Φ_mul (φ ψ : MulAut K) : (M.Φ (φ * ψ) : G) = (M.Φ φ : G) * (M.Φ ψ : G) := by
  rw [map_mul]; rfl

theorem AutModel.Φ_eq_one {φ : MulAut K} : (M.Φ φ : G) = 1 ↔ φ = 1 := by
  constructor
  · intro h
    apply M.Φ.injective
    apply Subtype.ext
    rw [h, M.Φ_one]
  · rintro rfl
    exact M.Φ_one

theorem AutModel.Φ_comm {φ ψ : MulAut K} (h : φ * ψ = ψ * φ) :
    (M.Φ φ : G) * (M.Φ ψ : G) = (M.Φ ψ : G) * (M.Φ φ : G) := by
  rw [← M.Φ_mul, ← M.Φ_mul, h]

@[expose] def AutModel.ι : MulAut K →* G := M.A.subtype.comp M.Φ.toMonoidHom

theorem AutModel.ι_injective : Function.Injective M.ι := by
  intro a b h
  exact M.Φ.injective (Subtype.ext h)

theorem AutModel.ι_mem (φ : MulAut K) : M.ι φ ∈ M.A := (M.Φ φ).2

theorem AutModel.card_mulAut : Nat.card (MulAut K) = Nat.card M.A :=
  Nat.card_congr M.Φ.toEquiv

theorem AutModel.inner_of_mem (φ : MulAut K) (h : (M.Φ φ : G) ∈ M.P) :
    ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  refine ⟨M.e.symm ⟨_, h⟩, fun x => ?_⟩
  apply M.e.injective
  apply Subtype.ext
  rw [M.spec]
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]

theorem AutModel.inner3 (h : ∀ g ∈ M.A, g ^ 3 = 1 → g ∈ M.P) (φ : MulAut K) (hφ : φ ^ 3 = 1) :
    ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹ := by
  apply M.inner_of_mem
  apply h _ (M.Φ φ).2
  rw [← M.Φ_pow, hφ, M.Φ_one]

theorem AutModel.autCentralizer
    (h : ∀ τ ∈ M.A, τ ^ 2 = 1 → τ ≠ 1 → ∀ X ∈ M.A, X ≠ 1 → ∀ Y ∈ M.A, X ^ 3 = 1 →
      Y ^ 3 = 1 → X * Y = Y * X → X * τ = τ * X → Y * τ = τ * Y → Y = 1 ∨ Y = X ∨ Y = X ^ 2)
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) (hcard : Nat.card R = 9)
    (ψ : MulAut K) (hψ : ψ ^ 2 = 1) (hc : ∀ r ∈ R, ψ * r = r * ψ) : ψ = 1 := by
  by_contra hne
  obtain ⟨x, hx, y, hy, hx1, hyn⟩ := exists_two_independent R (by omega)
  have key := h (M.Φ ψ) (M.Φ ψ).2 (by rw [← M.Φ_pow, hψ, M.Φ_one])
    (fun h1 => hne ((M.Φ_eq_one).1 h1)) (M.Φ x) (M.Φ x).2 (fun h1 => hx1 ((M.Φ_eq_one).1 h1))
    (M.Φ y) (M.Φ y).2
    (by rw [← M.Φ_pow, hR.2 x hx, M.Φ_one]) (by rw [← M.Φ_pow, hR.2 y hy, M.Φ_one])
    (M.Φ_comm (hR.1 x hx y hy)) (M.Φ_comm (hc x hx).symm) (M.Φ_comm (hc y hy).symm)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyn
  rcases key with h1 | h1 | h1
  · exact hyn.1 ((M.Φ_eq_one).1 h1)
  · have : y = x := by
      apply M.Φ.injective
      exact Subtype.ext h1
    exact hyn.2.1 this
  · have : y = x ^ 2 := by
      apply M.Φ.injective
      apply Subtype.ext
      rw [h1, M.Φ_pow]
    exact hyn.2.2 this

theorem AutModel.autRank3_le_two
    (h : ∀ X ∈ M.A, ∀ Y ∈ M.A, ∀ Z ∈ M.A, X ^ 3 = 1 → Y ^ 3 = 1 → Z ^ 3 = 1 →
      X * Y = Y * X → X * Z = Z * X → Y * Z = Z * Y →
      X = 1 ∨ Y ∈ ([1, X, X ^ 2] : List G) ∨ Z ∈ pow3list X Y)
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 9 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨x, hx, y, hy, z, hz, hx1, hyn, hzn⟩ := exists_three_independent R hlt
  have hpow : ∀ w ∈ R, M.ι w ^ 3 = 1 := fun w hw => by
    rw [← map_pow, hR.2 w hw, map_one]
  have key := h (M.ι x) (M.ι_mem x) (M.ι y) (M.ι_mem y) (M.ι z) (M.ι_mem z)
    (hpow x hx) (hpow y hy) (hpow z hz)
    (by rw [← map_mul, ← map_mul, hR.1 x hx y hy])
    (by rw [← map_mul, ← map_mul, hR.1 x hx z hz])
    (by rw [← map_mul, ← map_mul, hR.1 y hy z hz])
  rcases key with h1 | h1 | h1
  · exact hx1 (M.ι_injective (by rw [h1, map_one]))
  · apply hyn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 ⊢
    rcases h1 with h1 | h1 | h1
    · exact Or.inl (M.ι_injective (by rw [h1, map_one]))
    · exact Or.inr (Or.inl (M.ι_injective h1))
    · exact Or.inr (Or.inr (M.ι_injective (by rw [h1, map_pow])))
  · exact hzn (mem_pow3list_of_inj M.ι M.ι_injective x y z h1)

theorem AutModel.autRank3_le_one
    (h : ∀ X ∈ M.A, X ≠ 1 → ∀ Y ∈ M.A, X ^ 3 = 1 → Y ^ 3 = 1 → X * Y = Y * X →
      Y ∈ ([1, X, X ^ 2] : List G))
    (R : Subgroup (MulAut K)) (hR : ElemAb 3 R) : Nat.card R ≤ 3 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨x, hx, y, hy, hx1, hyn⟩ := exists_two_independent R hlt
  have hpow : ∀ w ∈ R, M.ι w ^ 3 = 1 := fun w hw => by
    rw [← map_pow, hR.2 w hw, map_one]
  have key := h (M.ι x) (M.ι_mem x) (fun h1 => hx1 (M.ι_injective (by rw [h1, map_one])))
    (M.ι y) (M.ι_mem y) (hpow x hx) (hpow y hy)
    (by rw [← map_mul, ← map_mul, hR.1 x hx y hy])
  apply hyn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at key ⊢
  rcases key with h1 | h1 | h1
  · exact Or.inl (M.ι_injective (by rw [h1, map_one]))
  · exact Or.inr (Or.inl (M.ι_injective h1))
  · exact Or.inr (Or.inr (M.ι_injective (by rw [h1, map_pow])))

theorem centralizer3_of_model {K G : Type*} [Group K] [Group G] (P : Subgroup G) (e : K ≃* P)
    (h : ∀ x ∈ P, ∀ y ∈ P, x ^ 3 = 1 → y ^ 3 = 1 → x * y = y * x → x ≠ 1 →
      y ∉ ([1, x, x ^ 2] : List G) → ∀ k ∈ P, k * x = x * k → k * y = y * k →
      k ∈ pow3list x y)
    (B : Subgroup K) (hB : ElemAb 3 B) (hcard : Nat.card B = 9) (k : K)
    (hk : ∀ b ∈ B, k * b = b * k) : k ∈ B := by
  obtain ⟨x, hx, y, hy, hx1, hyn⟩ := exists_two_independent B (by omega)
  let ι : K →* G := P.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := fun a b hab => e.injective (Subtype.ext hab)
  have key := h (ι x) (e x).2 (ι y) (e y).2
    (by rw [← map_pow, hB.2 x hx, map_one]) (by rw [← map_pow, hB.2 y hy, map_one])
    (by rw [← map_mul, ← map_mul, hB.1 x hx y hy])
    (fun h1 => hx1 (hι (by rw [h1, map_one])))
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hyn ⊢
      refine ⟨fun h1 => hyn.1 (hι (by rw [h1, map_one])), fun h1 => hyn.2.1 (hι h1),
        fun h1 => hyn.2.2 (hι (by rw [h1, map_pow]))⟩)
    (ι k) (e k).2
    (by rw [← map_mul, ← map_mul, hk x hx]) (by rw [← map_mul, ← map_mul, hk y hy])
  exact pow3list_subset B hx hy (mem_pow3list_of_inj ι hι x y k key)

theorem AutModel.fixed_solvable
    (h : ∀ τ ∈ M.A, τ ^ 2 = 1 → τ ≠ 1 →
      Group.IsSolvable ↥(M.P ⊓ Subgroup.centralizer ({τ} : Set G)))
    (α : MulAut K) (hα2 : α ^ 2 = 1) (hα1 : α ≠ 1) (L : Subgroup K)
    (hL : ∀ x ∈ L, α x = x) : Group.IsSolvable L := by
  have hsol := h (M.Φ α) (M.Φ α).2 (by rw [← M.Φ_pow, hα2, M.Φ_one])
    (fun h1 => hα1 ((M.Φ_eq_one).1 h1))
  have hmem : ∀ x : L, ((M.e x.1 : M.P) : G) ∈ Subgroup.centralizer ({(M.Φ α : G)} : Set G) := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := M.spec α x.1
    rw [hL x.1 x.2] at h1
    calc (M.e x.1 : G) * (M.Φ α : G)
        = ((M.Φ α : G) * (M.e x.1 : G) * (M.Φ α : G)⁻¹) * M.Φ α := by rw [← h1]
      _ = (M.Φ α : G) * (M.e x.1 : G) := by group
  let f : L →* ↥(M.P ⊓ Subgroup.centralizer ({(M.Φ α : G)} : Set G)) :=
    { toFun := fun x => ⟨((M.e x.1 : M.P) : G), ⟨(M.e x.1).2, hmem x⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp }
  have hinj : Function.Injective f := by
    intro a b hab
    have h : ((f a : ↥(M.P ⊓ Subgroup.centralizer ({(M.Φ α : G)} : Set G))) : G) = f b :=
      congrArg Subtype.val hab
    have h' : ((M.e a.1 : M.P) : G) = ((M.e b.1 : M.P) : G) := h
    exact Subtype.ext (M.e.injective (Subtype.ext h'))
  exact Group.isSolvable_of_isSolvable_injective hinj

end CFSG.GH74.KGroups
