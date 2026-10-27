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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod

abbrev Vec : Type := ZMod 3 × ZMod 3 × ZMod 3

def mv (i : ZMod 3) (c : Vec) : Vec := (i * c.1, i * c.2.1, i * c.2.2)

theorem mv_add (i j : ZMod 3) (c : Vec) : mv (i + j) c = mv i c + mv j c := by
  simp only [mv, add_mul]; rfl

theorem mv_zero (c : Vec) : mv 0 c = 0 := by simp [mv]

theorem mv_one (c : Vec) : mv 1 c = c := by simp [mv]

def cv : Fin 3 → Vec := ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]

def dv : Fin 4 → Vec := ![(1, 1, 1), (1, 1, 2), (1, 2, 1), (1, 2, 2)]

def hyp : Fin 13 → Vec × Vec :=
  ![((0, 1, 0), (0, 0, 1)), ((1, 0, 0), (0, 0, 1)), ((1, 0, 0), (0, 1, 0)),
    ((0, 0, 1), (1, 2, 0)), ((0, 0, 1), (1, 1, 0)), ((0, 1, 0), (1, 0, 2)),
    ((0, 1, 0), (1, 0, 1)), ((1, 0, 0), (0, 1, 2)), ((1, 0, 0), (0, 1, 1)),
    ((1, 1, 1), (1, 2, 0)), ((1, 1, 2), (1, 2, 0)), ((1, 2, 1), (1, 0, 2)),
    ((1, 2, 2), (0, 1, 2))]

theorem hyp_fst (k : Fin 13) : (∃ l, (hyp k).1 = cv l) ∨ ∃ i, (hyp k).1 = dv i := by
  revert k; decide

theorem hyp_count (u : Vec) :
    (Finset.univ.filter (fun p : Fin 13 × ZMod 3 × ZMod 3 =>
      mv p.2.1 (hyp p.1).1 + mv p.2.2 (hyp p.1).2 = u)).card = if u = 0 then 13 else 4 := by
  revert u; decide

theorem diag_pair (i j : Fin 4) (hij : i ≠ j) :
    ∃ a b : ZMod 3, ∃ l : Fin 3, mv a (dv i) + mv b (dv j) = cv l := by
  revert i j; decide

variable {V : Type} [AddCommGroup V]

structure ModData (T : Vec → V →+ V) : Prop where
  zero : T 0 = AddMonoidHom.id V
  add : ∀ a b, T (a + b) = (T a).comp (T b)
  two : ∀ v : V, v + v = 0

namespace ModData

variable {T : Vec → V →+ V} (h : ModData T)
include h

theorem apply_apply (a b : Vec) (v : V) : T a (T b v) = T (a + b) v := by
  rw [h.add a b]; rfl

theorem apply_zero (v : V) : T 0 v = v := by rw [h.zero]; rfl

theorem two2 (v : V) : (2 : ℕ) • v = 0 := by rw [two_nsmul]; exact h.two v

theorem comm (a b : Vec) (v : V) : T a (T b v) = T b (T a v) := by
  rw [h.apply_apply, h.apply_apply, add_comm]

theorem injective (a : Vec) : Function.Injective (T a) := by
  intro u v huv
  have h0 : (-a + a : Vec) = 0 := neg_add_cancel a
  have := congrArg (T (-a)) huv
  rw [h.apply_apply, h.apply_apply, h0, h.apply_zero, h.apply_zero] at this
  exact this

theorem fixed_mv {c : Vec} {v : V} (hv : T c v = v) (i : ZMod 3) : T (mv i c) v = v := by
  have hn : ∀ n : ℕ, T (mv (n : ZMod 3) c) v = v := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, mv_zero, h.apply_zero]
    | succ n ih =>
      rw [Nat.cast_succ, mv_add, mv_one, ← h.apply_apply, hv, ih]
  simpa using hn i.val

end ModData

def fixedSub (T : Vec → V →+ V) (c : Vec) : AddSubgroup V where
  carrier := {v | T c v = v}
  zero_mem' := map_zero _
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, ha, hb]
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_neg, ha]

def nrmHom (T : Vec → V →+ V) (c : Vec) : V →+ V := ∑ i : ZMod 3, T (mv i c)

theorem nrmHom_apply (T : Vec → V →+ V) (c : Vec) (v : V) :
    nrmHom T c v = ∑ i : ZMod 3, T (mv i c) v := by
  simp [nrmHom, AddMonoidHom.finsetSum_apply]

namespace ModData

variable {T : Vec → V →+ V} (h : ModData T)
include h

theorem apply_nrmHom (c : Vec) (v : V) : T c (nrmHom T c v) = nrmHom T c v := by
  rw [nrmHom_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod 3)) _ _ fun i => ?_
  rw [h.apply_apply]
  congr 1
  simp only [Equiv.coe_addRight, mv_add, mv_one]
  rw [add_comm]

theorem nrmHom_of_fixed {c : Vec} {v : V} (hv : T c v = v) : nrmHom T c v = v := by
  rw [nrmHom_apply]
  have hk : ∀ i : ZMod 3, T (mv i c) v = v := fun i => h.fixed_mv hv i
  simp only [hk]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card]
  have h3 : (3 : ℕ) • v = v := by
    rw [(by norm_num : (3 : ℕ) = 2 + 1), add_nsmul, h.two2, zero_add, one_nsmul]
  exact h3

theorem hyp_identity (v : V) :
    ∑ p : Fin 13 × ZMod 3 × ZMod 3,
      T (mv p.2.1 (hyp p.1).1 + mv p.2.2 (hyp p.1).2) v = v := by
  classical
  have hfib := Finset.sum_fiberwise (Finset.univ : Finset (Fin 13 × ZMod 3 × ZMod 3))
    (fun p : Fin 13 × ZMod 3 × ZMod 3 => mv p.2.1 (hyp p.1).1 + mv p.2.2 (hyp p.1).2)
    (fun p => T (mv p.2.1 (hyp p.1).1 + mv p.2.2 (hyp p.1).2) v)
  rw [← hfib]
  have hinner : ∀ u : Vec, ∑ p ∈ Finset.univ.filter
      (fun p : Fin 13 × ZMod 3 × ZMod 3 => mv p.2.1 (hyp p.1).1 + mv p.2.2 (hyp p.1).2 = u),
        T (mv p.2.1 (hyp p.1).1 + mv p.2.2 (hyp p.1).2) v =
      (if u = 0 then 13 else 4) • T u v := by
    intro u
    rw [← hyp_count u]
    rw [← Finset.sum_const]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(Finset.mem_filter.mp hp).2]
  simp only [hinner]
  have h4 : ∀ w : V, (4 : ℕ) • w = 0 := fun w => by
    rw [(by norm_num : (4 : ℕ) = 2 * 2), mul_nsmul, h.two2]
  have h13 : (13 : ℕ) • v = v := by
    rw [(by norm_num : (13 : ℕ) = 2 * 6 + 1), add_nsmul, mul_nsmul, h.two2, nsmul_zero, zero_add,
      one_nsmul]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Vec))]
  have herase : ∀ u ∈ Finset.univ.erase (0 : Vec),
      (if u = 0 then 13 else 4) • T u v = 0 := by
    intro u hu
    rw [if_neg (Finset.ne_of_mem_erase hu), h4]
  rw [Finset.sum_eq_zero herase, add_zero, if_pos rfl, h.apply_zero, h13]

end ModData

theorem mem_fixedSub {T : Vec → V →+ V} {c : Vec} {v : V} :
    v ∈ fixedSub T c ↔ T c v = v := Iff.rfl

namespace ModData

variable {T : Vec → V →+ V} (h : ModData T)
include h

theorem eq_zero_of_fixed_bot (hcoord : ∀ l v, T (cv l) v = v → v = 0)
    (hdiag : ∀ i v, T (dv i) v = v → v = 0) (v : V) : v = 0 := by
  have hid := h.hyp_identity v
  have hz : ∀ k : Fin 13, ∀ j : ZMod 3,
      ∑ i : ZMod 3, T (mv i (hyp k).1 + mv j (hyp k).2) v = 0 := by
    intro k j
    have hc : ∀ w, T (hyp k).1 w = w → w = 0 := by
      rcases hyp_fst k with ⟨l, hl⟩ | ⟨i, hi⟩
      · rw [hl]; exact hcoord l
      · rw [hi]; exact hdiag i
    have hsum : ∑ i : ZMod 3, T (mv i (hyp k).1 + mv j (hyp k).2) v =
        nrmHom T (hyp k).1 (T (mv j (hyp k).2) v) := by
      rw [nrmHom_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h.apply_apply]
    rw [hsum]
    exact hc _ (h.apply_nrmHom _ _)
  have hsplit : ∑ p : Fin 13 × ZMod 3 × ZMod 3,
      T (mv p.2.1 (hyp p.1).1 + mv p.2.2 (hyp p.1).2) v =
      ∑ k : Fin 13, ∑ j : ZMod 3, ∑ i : ZMod 3, T (mv i (hyp k).1 + mv j (hyp k).2) v := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [hsplit] at hid
  simp only [hz, Finset.sum_const_zero] at hid
  exact hid.symm

theorem card_fixed_ge (hcoord : ∀ l v, T (cv l) v = v → v = 0) [Finite V] (i : Fin 4)
    (hne : fixedSub T (dv i) ≠ ⊥) : 4 ≤ Nat.card (fixedSub T (dv i)) := by
  obtain ⟨⟨v, hv⟩, hv0'⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hne
  have hv0 : v ≠ 0 := fun h0 => hv0' (Subtype.ext h0)
  have hvf : T (dv i) v = v := hv
  set e : Vec := cv 0 with he
  have hef : ∀ w, T e w = w → w = 0 := hcoord 0
  set u : V := T e v with hu
  have huf : T (dv i) u = u := by
    rw [hu, h.comm, hvf]
  have hu0 : u ≠ 0 := by
    intro h0
    apply hv0
    exact h.injective e (by rw [← hu, h0, map_zero])
  have huv : u ≠ v := fun huv => hv0 (hef v (by rw [← hu]; exact huv))
  have hvu : v + u ≠ 0 := by
    intro h0
    apply huv
    have h2 : v + v = 0 := h.two v
    calc u = (v + v) + u := by rw [h2, zero_add]
      _ = v + (v + u) := by rw [add_assoc]
      _ = v := by rw [h0, add_zero]
  let f : Fin 4 → fixedSub T (dv i) :=
    ![0, ⟨v, hv⟩, ⟨u, huf⟩, ⟨v + u, AddSubgroup.add_mem _ hv huf⟩]
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : ((f a : fixedSub T (dv i)) : V) = (f b : V) := congrArg Subtype.val hab
    fin_cases a <;> fin_cases b <;> simp [f] at hab' ⊢ <;>
      first
      | exact absurd hab'.symm hv0
      | exact absurd hab' hv0
      | exact absurd hab'.symm hu0
      | exact absurd hab' hu0
      | exact absurd hab' huv
      | exact absurd hab'.symm huv
      | exact absurd hab' hvu
      | exact absurd hab'.symm hvu
      | skip
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem nrm_dv_eq_zero (hcoord : ∀ l v, T (cv l) v = v → v = 0) {i j : Fin 4} (hij : i ≠ j)
    {w : V} (hw : T (dv j) w = w) : nrmHom T (dv i) w = 0 := by
  set z := nrmHom T (dv i) w with hz
  have hzi : T (dv i) z = z := h.apply_nrmHom _ _
  have hzj : T (dv j) z = z := by
    rw [hz, nrmHom_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h.comm, hw]
  obtain ⟨a, b, l, hl⟩ := diag_pair i j hij
  have hzl : T (cv l) z = z := by
    rw [← hl, ← h.apply_apply, h.fixed_mv hzj b, h.fixed_mv hzi a]
  exact hcoord l z hzl

theorem indep_zero (hcoord : ∀ l v, T (cv l) v = v → v = 0) (w : Fin 4 → V)
    (hw : ∀ i, T (dv i) (w i) = w i) (hsum : ∑ i, w i = 0) (i₀ : Fin 4) : w i₀ = 0 := by
  have h1 : nrmHom T (dv i₀) (∑ i, w i) = ∑ i, nrmHom T (dv i₀) (w i) := map_sum _ _ _
  rw [hsum, map_zero] at h1
  rw [Finset.sum_eq_single i₀ (fun j _ hj => h.nrm_dv_eq_zero hcoord (Ne.symm hj) (hw j))
    (fun hi => absurd (Finset.mem_univ i₀) hi), h.nrmHom_of_fixed (hw i₀)] at h1
  exact h1.symm

theorem card_ge [Finite V] (hcoord : ∀ l v, T (cv l) v = v → v = 0)
    (hsym : ∀ i j : Fin 4, Nat.card (fixedSub T (dv i)) = Nat.card (fixedSub T (dv j)))
    (hne : ∃ v : V, v ≠ 0) : 256 ≤ Nat.card V := by
  have hex : ∃ i, fixedSub T (dv i) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v, hv⟩ := hne
    refine hv (h.eq_zero_of_fixed_bot hcoord (fun i w hw => ?_) v)
    have hw' : w ∈ fixedSub T (dv i) := hw
    rw [hcon i] at hw'
    exact AddSubgroup.mem_bot.mp hw'
  obtain ⟨i₀, hi₀⟩ := hex
  have h4 : ∀ i, 4 ≤ Nat.card (fixedSub T (dv i)) := fun i => by
    rw [hsym i i₀]; exact h.card_fixed_ge hcoord i₀ hi₀
  let Φ : (∀ i : Fin 4, fixedSub T (dv i)) → V := fun f => ∑ i, (f i : V)
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    have hsub : ∑ i, ((f i : V) - (g i : V)) = 0 := by
      rw [Finset.sum_sub_distrib]; exact sub_eq_zero.mpr hfg
    have hfix : ∀ i, T (dv i) ((f i : V) - (g i : V)) = (f i : V) - (g i : V) := fun i =>
      ((fixedSub T (dv i)).sub_mem (f i).2 (g i).2)
    funext i
    exact Subtype.ext (sub_eq_zero.mp (h.indep_zero hcoord _ hfix hsub i))
  have hle := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_pi] at hle
  calc 256 = ∏ i : Fin 4, 4 := by simp
    _ ≤ ∏ i, Nat.card (fixedSub T (dv i)) :=
      Finset.prod_le_prod' fun i _ => h4 i
    _ ≤ Nat.card V := hle

end ModData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Mod
