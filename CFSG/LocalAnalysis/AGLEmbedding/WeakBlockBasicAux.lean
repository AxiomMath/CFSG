module

import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment
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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.AGLEmbedding

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem le_of_perfect_of_le_sup_of_normal {H K R P : Subgroup X} [R.Normal]
    [Group.IsSolvable R] (hHK : H ≤ K) (hn : (H.subgroupOf K).Normal) (hP : ⁅P, P⁆ = P)
    (hPK : P ≤ K) (hPHR : P ≤ H ⊔ R) : P ≤ H := by
  let N := R.subgroupOf K
  have hsol : Group.IsSolvable (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    let f : N →* R := (K.subtype.comp N.subtype).codRestrict R fun x => x.2
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
    have h : ((f x : R) : X) = ((f y : R) : X) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h)
  have hperf : Group.IsPerfect (P.subgroupOf K) := by
    rw [Subgroup.isPerfect_iff]
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPK, hP]
  have hle : P.subgroupOf K ≤ H.subgroupOf K ⊔ N := by
    intro x hx
    obtain ⟨h, hh, r, hr, hhr⟩ := (Subgroup.mem_sup_of_normal_right (s := H) (t := R)).1
      (hPHR (Subgroup.mem_subgroupOf.mp hx))
    have hrK : r ∈ K := by
      rw [show r = h⁻¹ * x by rw [← hhr, inv_mul_cancel_left]]
      exact K.mul_mem (K.inv_mem (hHK hh)) x.2
    have hx' : x = ⟨h, hHK hh⟩ * ⟨r, hrK⟩ := Subtype.ext hhr.symm
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hh))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hr))
  have key := CFSG.ComponentClassification.SolvableKernelContainment.perfect_containment
    (QuotientGroup.mk' N) (P.subgroupOf K) (H.subgroupOf K) (by
      rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact hle)
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (key (Subgroup.mem_subgroupOf.mpr (show (⟨x, hPK hx⟩ : K).1 ∈ P
    from hx)))

theorem le_of_perfect_of_le_sup_of_isSubnormal {K R P : Subgroup X} [R.Normal]
    [Group.IsSolvable R] (hK : K.IsSubnormal) (hP : ⁅P, P⁆ = P) (hPKR : P ≤ K ⊔ R) :
    P ≤ K := by
  suffices key : ∀ H : Subgroup X, H.IsSubnormal → K ≤ H → P ≤ H from key K hK le_rfl
  intro H hH
  induction hH with
  | top => exact fun _ => le_top
  | step H K' hHK' _ hn ih =>
    intro hKH
    exact le_of_perfect_of_le_sup_of_normal hHK' hn hP (ih (hKH.trans hHK'))
      (hPKR.trans (sup_le_sup_right hKH R))

theorem commutator_le_left_of_le_normalizer {V L : Subgroup X}
    (hLV : L ≤ Subgroup.normalizer (V : Set X)) : ⁅V, L⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have e : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hLV hl) _).mp (V.inv_mem hv))

theorem le_normalizer_commutator_of_le_normalizer {V L : Subgroup X}
    (hLV : L ≤ Subgroup.normalizer (V : Set X)) :
    L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup X) : Set X) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLV hl),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)]

private theorem commutatorElement_mul_right_conj (v a b : X) :
    ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

private theorem commutatorElement_inv_right_conj (v a : X) :
    ⁅v, a⁻¹⁆ = a⁻¹ * ⁅v, a⁆⁻¹ * a⁻¹⁻¹ := by
  simp only [commutatorElement_def]
  group

private theorem commutatorElement_conj_right_conj (v g n : X) :
    ⁅v, g * n * g⁻¹⁆ = g * ⁅g⁻¹ * v * g, n⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

private theorem commutatorElement_mul_right_succ (v y x : X) :
    ⁅v, y * x⁆ = ⁅v, y⁆ * (⁅y, ⁅v, x⁆⁆ * ⁅v, x⁆) := by
  simp only [commutatorElement_def]
  group

theorem commutator_le_commutator_commutator_of_twoGroup [Finite X] {V L : Subgroup X}
    (hres : ∀ (N : Subgroup L) [N.Normal], IsPGroup 2 (L ⧸ N) → N = ⊤)
    (hLV : L ≤ Subgroup.normalizer (V : Set X)) (hV : IsMulCommutative V)
    (h2 : IsPGroup 2 (⁅V, L⁆ : Subgroup X)) : ⁅V, L⁆ ≤ ⁅⁅V, L⁆, L⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup X := ⁅V, L⁆ with hW
  set K : Subgroup X := ⁅W, L⁆ with hK
  have hWV : W ≤ V := commutator_le_left_of_le_normalizer hLV
  have hLW : L ≤ Subgroup.normalizer (W : Set X) := le_normalizer_commutator_of_le_normalizer hLV
  have hKW : K ≤ W := commutator_le_left_of_le_normalizer hLW
  have hLK : L ≤ Subgroup.normalizer (K : Set X) := le_normalizer_commutator_of_le_normalizer hLW
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hconjK : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K := fun l hl k hk =>
    (Subgroup.mem_normalizer_iff.mp (hLK hl) k).mp hk
  let N : Subgroup L :=
    { carrier := {x | ∀ v ∈ V, ⁅v, (x : X)⁆ ∈ K}
      mul_mem' := fun {a b} ha hb v hv => by
        show ⁅v, (a : X) * b⁆ ∈ K
        rw [commutatorElement_mul_right_conj]
        exact K.mul_mem (ha v hv) (hconjK _ a.2 _ (hb v hv))
      one_mem' := fun v _ => by
        show ⁅v, (1 : X)⁆ ∈ K
        rw [commutatorElement_one_right]
        exact K.one_mem
      inv_mem' := fun {a} ha v hv => by
        show ⁅v, (a : X)⁻¹⁆ ∈ K
        rw [commutatorElement_inv_right_conj]
        exact hconjK _ (L.inv_mem a.2) _ (K.inv_mem (ha v hv)) }
  have hNn : N.Normal := ⟨fun n hn g v hv => by
    show ⁅v, (g : X) * n * (g : X)⁻¹⁆ ∈ K
    rw [commutatorElement_conj_right_conj]
    have hu : (g : X)⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hLV (L.inv_mem g.2)) v).mp hv
      rwa [inv_inv] at this
    exact hconjK _ g.2 _ (hn _ hu)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp h2
  have hpowW : ∀ w ∈ W, w ^ (2 ^ a) = 1 := fun w hw => by
    have := pow_card_eq_one' (x := (⟨w, hw⟩ : W))
    rw [ha] at this
    simpa using congrArg Subtype.val this
  have hstep : ∀ x ∈ L, ∀ v ∈ V, ∀ n : ℕ, ⁅v, x ^ n⁆ * (⁅v, x⁆ ^ n)⁻¹ ∈ K := by
    intro x hx v hv n
    induction n with
    | zero => simp [K.one_mem]
    | succ n ih =>
      have hw : ⁅v, x⁆ ∈ W := Subgroup.commutator_mem_commutator hv hx
      have hB : ⁅x ^ n, ⁅v, x⁆⁆ ∈ K := by
        rw [hK, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (L.pow_mem hx n) hw
      have hBV : ⁅x ^ n, ⁅v, x⁆⁆ ∈ V := hWV (hKW hB)
      have hCV : (⁅v, x⁆ ^ n)⁻¹ ∈ V := V.inv_mem (V.pow_mem (hWV hw) n)
      have e : ⁅v, x ^ (n + 1)⁆ * (⁅v, x⁆ ^ (n + 1))⁻¹ =
          (⁅v, x ^ n⁆ * (⁅v, x⁆ ^ n)⁻¹) * ⁅x ^ n, ⁅v, x⁆⁆ := by
        rw [pow_succ x n, commutatorElement_mul_right_succ, pow_succ ⁅v, x⁆ n]
        calc _ = ⁅v, x ^ n⁆ * (⁅x ^ n, ⁅v, x⁆⁆ * (⁅v, x⁆ ^ n)⁻¹) := by
              simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
          _ = ⁅v, x ^ n⁆ * ((⁅v, x⁆ ^ n)⁻¹ * ⁅x ^ n, ⁅v, x⁆⁆) := by rw [hcomm _ hBV _ hCV]
          _ = _ := by rw [mul_assoc]
      rw [e]
      exact K.mul_mem ih hB
  have hNpow : ∀ x : L, x ^ (2 ^ a) ∈ N := fun x v hv => by
    show ⁅v, ((x ^ 2 ^ a : L) : X)⁆ ∈ K
    have := hstep x x.2 v hv (2 ^ a)
    rwa [hpowW _ (Subgroup.commutator_mem_commutator hv x.2), inv_one, mul_one] at this
  have hp : IsPGroup 2 (L ⧸ N) := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨a, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hNpow x⟩
  have htop := hres N hp
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hlN : (⟨l, hl⟩ : L) ∈ N := by rw [htop]; exact Subgroup.mem_top _
  exact hlN v hv

end CFSG.AGLEmbedding
