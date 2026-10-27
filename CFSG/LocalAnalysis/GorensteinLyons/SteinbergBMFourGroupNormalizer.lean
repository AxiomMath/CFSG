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
public import Mathlib.Order.CompletePartialOrder
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup

variable {G : Type*} [Group G]

section Four

variable {z a : G}

@[expose] def fourVec (z a : G) : Fin 3 → G := ![z, a, z * a]

@[expose] def fourIdx [DecidableEq G] (z a : G) (x : G) : Fin 3 :=
  if x = a then 1 else if x = z * a then 2 else 0

variable (hz : z * z = 1) (ha : a * a = 1) (hcomm : z * a = a * z)

include hz ha hcomm in
theorem mem_four_iff {x : G} :
    x ∈ closure ({z, a} : Set G) ↔ x = 1 ∨ x = z ∨ x = a ∨ x = z * a := by
  have e1 : z * (z * a) = a := by rw [← mul_assoc, hz, one_mul]
  have e2 : a * (z * a) = z := by rw [← mul_assoc, ← hcomm, mul_assoc, ha, mul_one]
  have e3 : z * a * z = a := by rw [hcomm, mul_assoc, hz, mul_one]
  have e4 : z * a * a = z := by rw [mul_assoc, ha, mul_one]
  have e5 : z * a * (z * a) = 1 := by rw [← mul_assoc, e3, ha]
  have e6 : a * z = z * a := hcomm.symm
  let V : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = z ∨ x = a ∨ x = z * a}
      mul_mem' := by
        rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
          simp [hz, ha, e1, e2, e3, e4, e5, e6]
      one_mem' := Or.inl rfl
      inv_mem' := by
        rintro x (rfl | rfl | rfl | rfl)
        · simp
        · right; left; exact inv_eq_of_mul_eq_one_right hz
        · right; right; left; exact inv_eq_of_mul_eq_one_right ha
        · right; right; right; exact inv_eq_of_mul_eq_one_right e5 }
  constructor
  · intro hx
    have hle : closure ({z, a} : Set G) ≤ V := by
      rw [closure_le]
      rintro y (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    exact hle hx
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ rfl))

variable (hz1 : z ≠ 1) (ha1 : a ≠ 1) (hza : z ≠ a) [DecidableEq G]

include hz1 ha1 hza in
theorem fourIdx_fourVec (i : Fin 3) : fourIdx z a (fourVec z a i) = i := by
  have h1 : z ≠ z * a := fun h => ha1 (by simpa using congrArg (z⁻¹ * ·) h.symm)
  have h2 : z * a ≠ a := fun h => hz1 (by simpa using congrArg (· * a⁻¹) h)
  fin_cases i <;> simp [fourIdx, fourVec, hza, h1, h2]

include hz ha hcomm in
theorem fourVec_fourIdx {x : G} (hx : x ∈ closure ({z, a} : Set G)) (hx1 : x ≠ 1) :
    fourVec z a (fourIdx z a x) = x := by
  unfold fourIdx
  split_ifs with h1 h2
  · simp [fourVec, h1]
  · simp [fourVec, h2]
  · rcases (mem_four_iff hz ha hcomm).mp hx with h | h | h | h
    · exact absurd h hx1
    · simp [fourVec, h]
    · exact absurd h h1
    · exact absurd h h2

omit [DecidableEq G] in
include hz ha hcomm in
theorem fourVec_mem (i : Fin 3) : fourVec z a i ∈ closure ({z, a} : Set G) := by
  rw [mem_four_iff hz ha hcomm]
  fin_cases i <;> simp [fourVec]

omit [DecidableEq G] in
include ha hz1 ha1 hza in
theorem fourVec_ne_one (i : Fin 3) : fourVec z a i ≠ 1 := by
  have h3 : z * a ≠ 1 := fun h => hza (by
    rw [← mul_one z, ← ha, ← mul_assoc, h, one_mul])
  fin_cases i <;> simp [fourVec, hz1, ha1, h3]

omit [Group G] [DecidableEq G] in
theorem aut_ne_one {G : Type*} [Group G] {U : Subgroup G} (σ : MulAut U) {u : U}
    (hu : (u : G) ≠ 1) : (σ u : G) ≠ 1 := fun h => hu (by
  have : σ u = σ 1 := by rw [map_one]; exact Subtype.ext h
  rw [σ.injective this]
  rfl)

@[expose] noncomputable def fourPermFun (σ : MulAut (closure ({z, a} : Set G))) :
    Equiv.Perm (Fin 3) where
  toFun i := fourIdx z a (σ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩)
  invFun i := fourIdx z a (σ⁻¹ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩)
  left_inv i := by
    have e : (⟨fourVec z a (fourIdx z a (σ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩)),
        fourVec_mem hz ha hcomm _⟩ : closure ({z, a} : Set G)) =
        σ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩ :=
      Subtype.ext (fourVec_fourIdx hz ha hcomm (σ _).2
        (aut_ne_one σ (fourVec_ne_one ha hz1 ha1 hza i)))
    simp only
    rw [e, MulAut.inv_apply_self]
    exact fourIdx_fourVec hz1 ha1 hza i
  right_inv i := by
    have e : (⟨fourVec z a (fourIdx z a (σ⁻¹ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩)),
        fourVec_mem hz ha hcomm _⟩ : closure ({z, a} : Set G)) =
        σ⁻¹ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩ :=
      Subtype.ext (fourVec_fourIdx hz ha hcomm (σ⁻¹ _).2
        (aut_ne_one σ⁻¹ (fourVec_ne_one ha hz1 ha1 hza i)))
    simp only
    rw [e, MulAut.apply_inv_self]
    exact fourIdx_fourVec hz1 ha1 hza i

@[expose] noncomputable def fourPerm : MulAut (closure ({z, a} : Set G)) →* Equiv.Perm (Fin 3) where
  toFun := fourPermFun hz ha hcomm hz1 ha1 hza
  map_one' := Equiv.ext fun i => by
    change fourIdx z a ((1 : MulAut (closure ({z, a} : Set G)))
      ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩) = i
    rw [MulAut.one_apply]
    exact fourIdx_fourVec hz1 ha1 hza i
  map_mul' σ τ := Equiv.ext fun i => by
    change fourIdx z a ((σ * τ) ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩) =
      fourIdx z a (σ ⟨fourVec z a (fourIdx z a (τ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩)),
        fourVec_mem hz ha hcomm _⟩)
    have e : (⟨fourVec z a (fourIdx z a (τ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩)),
        fourVec_mem hz ha hcomm _⟩ : closure ({z, a} : Set G)) =
        τ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩ :=
      Subtype.ext (fourVec_fourIdx hz ha hcomm (τ _).2
        (aut_ne_one τ (fourVec_ne_one ha hz1 ha1 hza i)))
    rw [e, MulAut.mul_apply]

theorem fourPerm_apply (σ : MulAut (closure ({z, a} : Set G))) (i : Fin 3) :
    fourPerm hz ha hcomm hz1 ha1 hza σ i =
      fourIdx z a (σ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩) := rfl

theorem fourPerm_injective : Function.Injective (fourPerm hz ha hcomm hz1 ha1 hza) := by
  intro σ τ h
  have hw : ∀ i, σ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩ =
      τ ⟨fourVec z a i, fourVec_mem hz ha hcomm i⟩ := by
    intro i
    have h1 := congrArg (fun π : Equiv.Perm (Fin 3) => fourVec z a (π i)) h
    simp only [fourPerm_apply] at h1
    rw [fourVec_fourIdx hz ha hcomm (σ _).2 (aut_ne_one σ (fourVec_ne_one ha hz1 ha1 hza i)),
      fourVec_fourIdx hz ha hcomm (τ _).2 (aut_ne_one τ (fourVec_ne_one ha hz1 ha1 hza i))] at h1
    exact Subtype.ext h1
  refine MulEquiv.ext fun u => ?_
  by_cases hu : (u : G) = 1
  · rw [show u = 1 from Subtype.ext hu, map_one, map_one]
  · have hu' : u = ⟨fourVec z a (fourIdx z a u), fourVec_mem hz ha hcomm _⟩ :=
      Subtype.ext (fourVec_fourIdx hz ha hcomm u.2 hu).symm
    rw [hu', hw]

end Four

theorem two_cyclic_four_roots_full_four_group_normalizer [Finite G] {z a : G}
    (hz : orderOf z = 2) (ha : orderOf a = 2) (hza : z ≠ a) (hcomm : z * a = a * z)
    {U N C : Subgroup G} (hU : U = closure ({z, a} : Set G)) (hN : N = normalizer (U : Set G))
    (hC : C = centralizer (U : Set G)) {t s : G} (ht : t ^ 2 = z) (hs : s ^ 2 = a)
    (hta : a⁻¹ * t * a = t⁻¹) (hsz : z⁻¹ * s * z = s⁻¹) :
    orderOf t = 4 ∧ orderOf s = 4 ∧ t ∈ N ∧ s ∈ N ∧
    (t⁻¹ * z * t = z ∧ t⁻¹ * a * t = a * z ∧ t⁻¹ * (a * z) * t = a) ∧
    (s⁻¹ * a * s = a ∧ s⁻¹ * z * s = z * a ∧ s⁻¹ * (z * a) * s = z) ∧
    (∃ _ : (C.subgroupOf N).Normal, Nonempty (N ⧸ C.subgroupOf N ≃* MulAut U) ∧
      Nonempty (MulAut U ≃* Equiv.Perm (Fin 3))) ∧
    N ⊓ centralizer ({z} : Set G) = C ⊔ zpowers t ∧
    N ⊓ centralizer ({a} : Set G) = C ⊔ zpowers s ∧
    (N ⊓ centralizer ({z} : Set G)).relIndex N = 3 ∧
    (N ⊓ centralizer ({a} : Set G)).relIndex N = 3 ∧
    U ⊓ (center N).map N.subtype = ⊥ ∧
    (∀ Q : Subgroup G, Q ≤ centralizer ({z} : Set G) → a ∈ Q → t ∈ Q →
      Q ⊓ N = (Q ⊓ centralizer ({a} : Set G)) ⊔ zpowers t ∧
        (Q ⊓ centralizer ({a} : Set G)).relIndex (Q ⊓ N) = 2) ∧
    (∀ R : Subgroup G, R ≤ centralizer ({a} : Set G) → z ∈ R → s ∈ R →
      R ⊓ N = (R ⊓ centralizer ({z} : Set G)) ⊔ zpowers s ∧
        (R ⊓ centralizer ({z} : Set G)).relIndex (R ⊓ N) = 2) := by
  classical
  subst hU hN hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by norm_num)
  have hzaz : z * a ≠ z := fun h => ha1 (by simpa using congrArg (z⁻¹ * ·) h)
  have hzaa : z * a ≠ a := fun h => hz1 (by simpa using congrArg (· * a⁻¹) h)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have htt : t * t = z := by rw [← pow_two, ht]
  have hss : s * s = a := by rw [← pow_two, hs]
  have htz : t * z = z * t := by rw [← htt, mul_assoc]
  have hsa : s * a = a * s := by rw [← hss, mul_assoc]
  have hta' : t * a = a * t⁻¹ := by
    calc t * a = a * (a⁻¹ * t * a) := by group
      _ = a * t⁻¹ := by rw [hta]
  have hsz' : s * z = z * s⁻¹ := by
    calc s * z = z * (z⁻¹ * s * z) := by group
      _ = z * s⁻¹ := by rw [hsz]
  have c1 : t⁻¹ * z * t = z := by rw [mul_assoc, ← htz, ← mul_assoc, inv_mul_cancel, one_mul]
  have c2 : t⁻¹ * a * t = a * z := by
    calc t⁻¹ * a * t = t⁻¹ * (a * t⁻¹) * (t * t) := by group
      _ = a * z := by rw [← hta', htt]; group
  have c3 : t⁻¹ * (a * z) * t = a := by
    calc t⁻¹ * (a * z) * t = (t⁻¹ * a * t) * (t⁻¹ * z * t) := by group
      _ = a := by rw [c1, c2, mul_assoc, hzz, mul_one]
  have d1 : s⁻¹ * a * s = a := by rw [mul_assoc, ← hsa, ← mul_assoc, inv_mul_cancel, one_mul]
  have d2 : s⁻¹ * z * s = z * a := by
    calc s⁻¹ * z * s = s⁻¹ * (z * s⁻¹) * (s * s) := by group
      _ = z * a := by rw [← hsz', hss]; group
  have d3 : s⁻¹ * (z * a) * s = z := by
    calc s⁻¹ * (z * a) * s = (s⁻¹ * z * s) * (s⁻¹ * a * s) := by group
      _ = z := by rw [d1, d2, mul_assoc, haa, mul_one]
  have c1' : t * z * t⁻¹ = z := by rw [htz, mul_inv_cancel_right]
  have c2' : t * a * t⁻¹ = z * a := by
    calc t * a * t⁻¹ = t * (a * t⁻¹) := by group
      _ = z * a := by rw [← hta', ← mul_assoc, htt]
  have c3' : t * (z * a) * t⁻¹ = a := by
    calc t * (z * a) * t⁻¹ = (t * z * t⁻¹) * (t * a * t⁻¹) := by group
      _ = a := by rw [c1', c2', ← mul_assoc, hzz, one_mul]
  have d1' : s * a * s⁻¹ = a := by rw [hsa, mul_inv_cancel_right]
  have d2' : s * z * s⁻¹ = z * a := by
    calc s * z * s⁻¹ = s * (z * s⁻¹) := by group
      _ = z * a := by rw [← hsz', ← mul_assoc, hss, hcomm]
  have d3' : s * (z * a) * s⁻¹ = z := by
    calc s * (z * a) * s⁻¹ = (s * z * s⁻¹) * (s * a * s⁻¹) := by group
      _ = z := by rw [d1', d2', mul_assoc, haa, mul_one]
  have hzU : z ∈ closure ({z, a} : Set G) := subset_closure (Set.mem_insert _ _)
  have haU : a ∈ closure ({z, a} : Set G) := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hconjU : ∀ g : G, g * z * g⁻¹ ∈ closure ({z, a} : Set G) →
      g * a * g⁻¹ ∈ closure ({z, a} : Set G) →
      ∀ x ∈ closure ({z, a} : Set G), g * x * g⁻¹ ∈ closure ({z, a} : Set G) := by
    intro g hgz hga x hx
    induction hx using closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hgz
      · exact hga
    | one => simp
    | mul x y _ _ hx hy =>
      rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
      exact inv_mem hx
  have hnormU : ∀ g : G, g * z * g⁻¹ ∈ closure ({z, a} : Set G) →
      g * a * g⁻¹ ∈ closure ({z, a} : Set G) → g⁻¹ * z * g ∈ closure ({z, a} : Set G) →
      g⁻¹ * a * g ∈ closure ({z, a} : Set G) →
        g ∈ normalizer (closure ({z, a} : Set G) : Set G) := by
    intro g h1 h2 h3 h4
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact hconjU g h1 h2 x
    · intro hx
      have := hconjU g⁻¹ (by rwa [inv_inv]) (by rwa [inv_inv]) _ hx
      rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  have hzaU : z * a ∈ closure ({z, a} : Set G) := mul_mem hzU haU
  have htN : t ∈ normalizer (closure ({z, a} : Set G) : Set G) :=
    hnormU t (by rw [c1']; exact hzU) (by rw [c2']; exact hzaU) (by rw [c1]; exact hzU)
      (by rw [c2]; exact mul_mem haU hzU)
  have hsN : s ∈ normalizer (closure ({z, a} : Set G) : Set G) :=
    hnormU s (by rw [d2']; exact hzaU) (by rw [d1']; exact haU) (by rw [d2]; exact hzaU)
      (by rw [d1]; exact haU)
  set ψ : normalizer (closure ({z, a} : Set G) : Set G) →* Equiv.Perm (Fin 3) :=
    (fourPerm hzz haa hcomm hz1 ha1 hza).comp (closure ({z, a} : Set G)).normalizerMonoidHom
    with hψ
  have hψapp : ∀ n i, ψ n i = fourIdx z a (n * fourVec z a i * (n : G)⁻¹) := fun n i => rfl
  have hψker : ∀ n, ψ n = 1 ↔ (n : G) ∈ centralizer (closure ({z, a} : Set G) : Set G) := by
    intro n
    rw [← mem_subgroupOf, ← normalizerMonoidHom_ker, MonoidHom.mem_ker, hψ, MonoidHom.comp_apply,
      ← map_one (fourPerm hzz haa hcomm hz1 ha1 hza)]
    exact (fourPerm_injective hzz haa hcomm hz1 ha1 hza).eq_iff
  have hfix : ∀ (n : normalizer (closure ({z, a} : Set G) : Set G)) (i : Fin 3),
      ψ n i = i ↔ (n : G) * fourVec z a i * (n : G)⁻¹ = fourVec z a i := by
    intro n i
    rw [hψapp]
    constructor
    · intro h
      have hmem : (n : G) * fourVec z a i * (n : G)⁻¹ ∈ closure ({z, a} : Set G) :=
        (mem_normalizer_iff.mp n.2 _).mp (fourVec_mem hzz haa hcomm i)
      have hne : (n : G) * fourVec z a i * (n : G)⁻¹ ≠ 1 := fun h1 =>
        fourVec_ne_one haa hz1 ha1 hza i (by
          rw [mul_inv_eq_one] at h1
          exact mul_eq_left.mp h1)
      rw [← fourVec_fourIdx hzz haa hcomm hmem hne, h]
    · intro h
      rw [h, fourIdx_fourVec hz1 ha1 hza]
  have hC_z : ∀ n : normalizer (closure ({z, a} : Set G) : Set G),
      ψ n 0 = 0 ↔ (n : G) ∈ centralizer ({z} : Set G) := by
    intro n
    rw [hfix, mem_centralizer_singleton_iff]
    simp only [fourVec, Matrix.cons_val_zero]
    rw [mul_inv_eq_iff_eq_mul]
  have hC_a : ∀ n : normalizer (closure ({z, a} : Set G) : Set G),
      ψ n 1 = 1 ↔ (n : G) ∈ centralizer ({a} : Set G) := by
    intro n
    rw [hfix, mem_centralizer_singleton_iff]
    simp only [fourVec, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [mul_inv_eq_iff_eq_mul]
  set t' : normalizer (closure ({z, a} : Set G) : Set G) := ⟨t, htN⟩ with ht'
  set s' : normalizer (closure ({z, a} : Set G) : Set G) := ⟨s, hsN⟩ with hs'
  have hψt : ψ t' = Equiv.swap 1 2 := by
    have e0 : ψ t' 0 = 0 := by
      rw [hψapp]
      change fourIdx z a (t * z * t⁻¹) = 0
      rw [c1']
      exact fourIdx_fourVec hz1 ha1 hza 0
    have e1 : ψ t' 1 = 2 := by
      rw [hψapp]
      change fourIdx z a (t * a * t⁻¹) = 2
      rw [c2']
      exact fourIdx_fourVec hz1 ha1 hza 2
    have e2 : ψ t' 2 = 1 := by
      rw [hψapp]
      change fourIdx z a (t * (z * a) * t⁻¹) = 1
      rw [c3']
      exact fourIdx_fourVec hz1 ha1 hza 1
    have key : ∀ π : Equiv.Perm (Fin 3), π 0 = 0 → π 1 = 2 → π 2 = 1 → π = Equiv.swap 1 2 := by
      decide
    exact key _ e0 e1 e2
  have hψs : ψ s' = Equiv.swap 0 2 := by
    have e0 : ψ s' 0 = 2 := by
      rw [hψapp]
      change fourIdx z a (s * z * s⁻¹) = 2
      rw [d2']
      exact fourIdx_fourVec hz1 ha1 hza 2
    have e1 : ψ s' 1 = 1 := by
      rw [hψapp]
      change fourIdx z a (s * a * s⁻¹) = 1
      rw [d1']
      exact fourIdx_fourVec hz1 ha1 hza 1
    have e2 : ψ s' 2 = 0 := by
      rw [hψapp]
      change fourIdx z a (s * (z * a) * s⁻¹) = 0
      rw [d3']
      exact fourIdx_fourVec hz1 ha1 hza 0
    have key : ∀ π : Equiv.Perm (Fin 3), π 0 = 2 → π 1 = 1 → π 2 = 0 → π = Equiv.swap 0 2 := by
      decide
    exact key _ e0 e1 e2
  have hψsurj : Function.Surjective ψ := by
    intro π
    have hπ : π ∈ ({1, Equiv.swap 1 2, Equiv.swap 0 2, Equiv.swap 1 2 * Equiv.swap 0 2,
        Equiv.swap 0 2 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 2 * Equiv.swap 1 2} :
        Finset (Equiv.Perm (Fin 3))) := by
      revert π
      decide
    simp only [Finset.mem_insert, Finset.mem_singleton] at hπ
    rcases hπ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, map_one ψ⟩
    · exact ⟨t', hψt⟩
    · exact ⟨s', hψs⟩
    · exact ⟨t' * s', by rw [map_mul, hψt, hψs]⟩
    · exact ⟨s' * t', by rw [map_mul, hψt, hψs]⟩
    · exact ⟨t' * s' * t', by rw [map_mul, map_mul, hψt, hψs]⟩
  have hCN : centralizer (closure ({z, a} : Set G) : Set G) ≤
      normalizer (closure ({z, a} : Set G) : Set G) := centralizer_le_normalizer _
  have hC_le_z : centralizer (closure ({z, a} : Set G) : Set G) ≤ centralizer ({z} : Set G) :=
    fun c hc => mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hc z hzU).symm)
  have hC_le_a : centralizer (closure ({z, a} : Set G) : Set G) ≤ centralizer ({a} : Set G) :=
    fun c hc => mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hc a haU).symm)
  have hCza : ∀ x : G, x ∈ centralizer ({z} : Set G) → x ∈ centralizer ({a} : Set G) →
      x ∈ centralizer (closure ({z, a} : Set G) : Set G) := by
    intro x hxz hxa
    rw [centralizer_closure, mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (mem_centralizer_singleton_iff.mp hxz).symm
    · exact (mem_centralizer_singleton_iff.mp hxa).symm
  have hfix0 : ∀ π : Equiv.Perm (Fin 3), π 0 = 0 → π = 1 ∨ π = Equiv.swap 1 2 := by decide
  have hfix1 : ∀ π : Equiv.Perm (Fin 3), π 1 = 1 → π = 1 ∨ π = Equiv.swap 0 2 := by decide
  have hot : orderOf t = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := t) (by rw [pow_one, ht]; exact hz1)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, ht, pow_two, hzz])
    simpa using h
  have hos : orderOf s = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := s) (by rw [pow_one, hs]; exact ha1)
      (by rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hs, pow_two, haa])
    simpa using h
  have hφsurj : Function.Surjective (closure ({z, a} : Set G)).normalizerMonoidHom := by
    intro σ
    obtain ⟨n, hn⟩ := hψsurj (fourPerm hzz haa hcomm hz1 ha1 hza σ)
    exact ⟨n, fourPerm_injective hzz haa hcomm hz1 ha1 hza hn⟩
  have hnorm : ((centralizer (closure ({z, a} : Set G) : Set G)).subgroupOf
      (normalizer (closure ({z, a} : Set G) : Set G))).Normal := by
    rw [← normalizerMonoidHom_ker]
    exact MonoidHom.normal_ker _
  have hiso : ∃ _ : ((centralizer (closure ({z, a} : Set G) : Set G)).subgroupOf
      (normalizer (closure ({z, a} : Set G) : Set G))).Normal,
      Nonempty (normalizer (closure ({z, a} : Set G) : Set G) ⧸
        (centralizer (closure ({z, a} : Set G) : Set G)).subgroupOf
          (normalizer (closure ({z, a} : Set G) : Set G)) ≃* MulAut (closure ({z, a} : Set G))) ∧
      Nonempty (MulAut (closure ({z, a} : Set G)) ≃* Equiv.Perm (Fin 3)) := by
    refine ⟨hnorm, ⟨(QuotientGroup.quotientMulEquivOfEq (normalizerMonoidHom_ker _).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hφsurj)⟩,
      ⟨MulEquiv.ofBijective (fourPerm hzz haa hcomm hz1 ha1 hza)
        ⟨fourPerm_injective hzz haa hcomm hz1 ha1 hza, fun π => ?_⟩⟩⟩
    obtain ⟨n, hn⟩ := hψsurj π
    exact ⟨_, hn⟩
  have hNz : normalizer (closure ({z, a} : Set G) : Set G) ⊓ centralizer ({z} : Set G) =
      centralizer (closure ({z, a} : Set G) : Set G) ⊔ zpowers t := by
    apply le_antisymm
    · rintro x ⟨hxN, hxz⟩
      rcases hfix0 _ ((hC_z ⟨x, hxN⟩).mpr hxz) with h | h
      · exact mem_sup_left ((hψker ⟨x, hxN⟩).mp h)
      · have h3 := (hψker (t'⁻¹ * ⟨x, hxN⟩)).mp (by rw [map_mul, map_inv, hψt, h, inv_mul_cancel])
        rw [show x = t * (t⁻¹ * x) by group]
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h3)
    · refine sup_le (fun c hc => ⟨hCN hc, hC_le_z hc⟩) ?_
      rw [zpowers_le]
      exact ⟨htN, mem_centralizer_singleton_iff.mpr htz⟩
  have hNa : normalizer (closure ({z, a} : Set G) : Set G) ⊓ centralizer ({a} : Set G) =
      centralizer (closure ({z, a} : Set G) : Set G) ⊔ zpowers s := by
    apply le_antisymm
    · rintro x ⟨hxN, hxa⟩
      rcases hfix1 _ ((hC_a ⟨x, hxN⟩).mpr hxa) with h | h
      · exact mem_sup_left ((hψker ⟨x, hxN⟩).mp h)
      · have h3 := (hψker (s'⁻¹ * ⟨x, hxN⟩)).mp (by rw [map_mul, map_inv, hψs, h, inv_mul_cancel])
        rw [show x = s * (s⁻¹ * x) by group]
        exact mul_mem (mem_sup_right (mem_zpowers s)) (mem_sup_left h3)
    · refine sup_le (fun c hc => ⟨hCN hc, hC_le_a hc⟩) ?_
      rw [zpowers_le]
      exact ⟨hsN, mem_centralizer_singleton_iff.mpr hsa⟩
  have hidx : ∀ (i : Fin 3) (w : G), (∀ n : normalizer (closure ({z, a} : Set G) : Set G),
      ψ n i = i ↔ (n : G) ∈ centralizer ({w} : Set G)) →
      (normalizer (closure ({z, a} : Set G) : Set G) ⊓ centralizer ({w} : Set G)).relIndex
        (normalizer (closure ({z, a} : Set G) : Set G)) = 3 := by
    intro i w hiw
    have hcomap : (normalizer (closure ({z, a} : Set G) : Set G) ⊓
        centralizer ({w} : Set G)).subgroupOf (normalizer (closure ({z, a} : Set G) : Set G)) =
        (MulAction.stabilizer (Equiv.Perm (Fin 3)) i).comap ψ := by
      ext n
      rw [mem_subgroupOf, mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, mem_inf]
      exact ⟨fun h => (hiw n).mpr h.2, fun h => ⟨n.2, (hiw n).mp h⟩⟩
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hψsurj,
      MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hUZ : closure ({z, a} : Set G) ⊓
      (center (normalizer (closure ({z, a} : Set G) : Set G))).map
        (normalizer (closure ({z, a} : Set G) : Set G)).subtype = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxU, c, hc, rfl⟩
    rw [mem_bot]
    have hct : t * (c : G) = c * t := congrArg Subtype.val ((mem_center_iff.mp hc) t')
    have hcs : s * (c : G) = c * s := congrArg Subtype.val ((mem_center_iff.mp hc) s')
    have hct' : t * (c : G) * t⁻¹ = c := by rw [hct, mul_inv_cancel_right]
    have hcs' : s * (c : G) * s⁻¹ = c := by rw [hcs, mul_inv_cancel_right]
    have hxU' : (c : G) ∈ closure ({z, a} : Set G) := hxU
    rcases (mem_four_iff hzz haa hcomm).mp hxU' with h | h | h | h
    · exact h
    · rw [h, d2'] at hcs'
      exact absurd hcs' hzaz
    · rw [h, c2'] at hct'
      exact absurd hct' hzaa
    · rw [h, c3'] at hct'
      exact absurd hct'.symm hzaa
  refine ⟨hot, hos, htN, hsN, ⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩, hiso, hNz, hNa,
    hidx 0 z hC_z, hidx 1 a hC_a, hUZ, fun Q hQz haQ htQ => ⟨?_, ?_⟩,
    fun R hRa hzR hsR => ⟨?_, ?_⟩⟩
  ·
    apply le_antisymm
    · rintro x ⟨hxQ, hxN⟩
      rcases hfix0 _ ((hC_z ⟨x, hxN⟩).mpr (hQz hxQ)) with h | h
      · exact mem_sup_left ⟨hxQ, hC_le_a ((hψker ⟨x, hxN⟩).mp h)⟩
      · have h3 := (hψker (t'⁻¹ * ⟨x, hxN⟩)).mp (by rw [map_mul, map_inv, hψt, h, inv_mul_cancel])
        rw [show x = t * (t⁻¹ * x) by group]
        exact mul_mem (mem_sup_right (mem_zpowers t))
          (mem_sup_left (mem_inf.mpr ⟨Q.mul_mem (Q.inv_mem htQ) hxQ, hC_le_a h3⟩))
    · refine sup_le (fun x hx => ⟨hx.1, hCN (hCza x (hQz hx.1) hx.2)⟩) ?_
      rw [zpowers_le]
      exact ⟨htQ, htN⟩
  ·
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨t, ⟨htQ, htN⟩, fun b hb => ?_⟩
    rcases hfix0 _ ((hC_z ⟨b, hb.2⟩).mpr (hQz hb.1)) with h | h
    · refine Or.inr ⟨⟨hb.1, hC_le_a ((hψker ⟨b, hb.2⟩).mp h)⟩, fun hbt => ?_⟩
      have h4 := (hC_a (⟨b, hb.2⟩ * t')).mpr hbt.2
      rw [map_mul, h, hψt, one_mul] at h4
      exact absurd h4 (by decide)
    · refine Or.inl ⟨⟨mul_mem hb.1 htQ, (hC_a (⟨b, hb.2⟩ * t')).mp (by
        rw [map_mul, h, hψt]; decide)⟩, fun hba => ?_⟩
      have h4 := (hC_a ⟨b, hb.2⟩).mpr hba.2
      rw [h] at h4
      exact absurd h4 (by decide)
  ·
    apply le_antisymm
    · rintro x ⟨hxR, hxN⟩
      rcases hfix1 _ ((hC_a ⟨x, hxN⟩).mpr (hRa hxR)) with h | h
      · exact mem_sup_left ⟨hxR, hC_le_z ((hψker ⟨x, hxN⟩).mp h)⟩
      · have h3 := (hψker (s'⁻¹ * ⟨x, hxN⟩)).mp (by rw [map_mul, map_inv, hψs, h, inv_mul_cancel])
        rw [show x = s * (s⁻¹ * x) by group]
        exact mul_mem (mem_sup_right (mem_zpowers s))
          (mem_sup_left (mem_inf.mpr ⟨R.mul_mem (R.inv_mem hsR) hxR, hC_le_z h3⟩))
    · refine sup_le (fun x hx => ⟨hx.1, hCN (hCza x hx.2 (hRa hx.1))⟩) ?_
      rw [zpowers_le]
      exact ⟨hsR, hsN⟩
  ·
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨s, ⟨hsR, hsN⟩, fun b hb => ?_⟩
    rcases hfix1 _ ((hC_a ⟨b, hb.2⟩).mpr (hRa hb.1)) with h | h
    · refine Or.inr ⟨⟨hb.1, hC_le_z ((hψker ⟨b, hb.2⟩).mp h)⟩, fun hbs => ?_⟩
      have h4 := (hC_z (⟨b, hb.2⟩ * s')).mpr hbs.2
      rw [map_mul, h, hψs, one_mul] at h4
      exact absurd h4 (by decide)
    · refine Or.inl ⟨⟨mul_mem hb.1 hsR, (hC_z (⟨b, hb.2⟩ * s')).mp (by
        rw [map_mul, h, hψs]; decide)⟩, fun hbz => ?_⟩
      have h4 := (hC_z ⟨b, hb.2⟩).mpr hbz.2
      rw [h] at h4
      exact absurd h4 (by decide)

end CFSG.LocalAnalysis.GorensteinLyons
