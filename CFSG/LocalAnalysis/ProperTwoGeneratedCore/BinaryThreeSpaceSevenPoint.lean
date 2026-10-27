module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

namespace CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

open Module

private theorem zmod2_cases : ∀ x : ZMod 2, x = if x = 1 then 1 else 0 := by decide

private theorem zmod2_eq_zero_or_one : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

section Sums

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self_eq_zero' (x : W) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

variable [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
theorem two_mul_card_fiber_one (f : Module.Dual (ZMod 2) W) {w : W} (hw : f w = 1) :
    2 * (Finset.univ.filter fun v => f v = 1).card = Fintype.card W := by
  have hfib := AddMonoidHom.card_fiber_eq_of_mem_range (f : W →+ ZMod 2)
    (x := 1) (y := 0) ⟨w, hw⟩ ⟨0, map_zero f⟩
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset W)) (fun v => f v = 1)
  have hneg : (Finset.univ.filter fun v => ¬f v = 1) = Finset.univ.filter fun v => f v = 0 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases zmod2_eq_zero_or_one (f v) with h | h <;> simp [h]
  have hfib' : (Finset.univ.filter fun v => f v = 1).card =
      (Finset.univ.filter fun v => f v = 0).card := hfib
  rw [hneg, ← hfib', Finset.card_univ] at hpart
  omega

omit [DecidableEq W] in
theorem sum_dual_eq_zero (hW : 4 ∣ Fintype.card W) (f : Module.Dual (ZMod 2) W) :
    ∑ w, f w = 0 := by
  have hsum : ∑ w, f w = ((Finset.univ.filter fun w => f w = 1).card : ZMod 2) := by
    rw [← Finset.sum_boole]
    exact Finset.sum_congr rfl fun w _ => zmod2_cases (f w)
  rw [hsum]
  by_cases h1 : ∃ w, f w = 1
  · obtain ⟨w, hw⟩ := h1
    have h2 := two_mul_card_fiber_one f hw
    obtain ⟨k, hk⟩ := hW
    have h3 : (Finset.univ.filter fun w => f w = 1).card = 2 * k := by omega
    rw [h3, Nat.cast_mul]
    exact mul_eq_zero_of_left (by decide) _
  · have h0 : (Finset.univ.filter fun w => f w = 1) = ∅ :=
      Finset.filter_false_of_mem fun w _ hw => h1 ⟨w, hw⟩
    rw [h0, Finset.card_empty, Nat.cast_zero]

omit [DecidableEq W] in
theorem sum_univ_eq_zero (hW : 4 ∣ Fintype.card W) : ∑ w : W, w = 0 :=
  (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp fun φ => by
    rw [map_sum]; exact sum_dual_eq_zero hW φ

end Sums

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]

abbrev Points (V : Type*) [AddCommGroup V] : Type _ := {v : V // v ≠ 0}

omit [DecidableEq V] in
theorem card_eq_eight (hV : finrank (ZMod 2) V = 3) : Fintype.card V = 8 := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), hV, ZMod.card]
  norm_num

theorem card_points (hV : finrank (ZMod 2) V = 3) : Fintype.card (Points V) = 7 := by
  rw [Fintype.card_subtype_compl, card_eq_eight hV, Fintype.card_unique]

omit [Module (ZMod 2) V] in
theorem sum_points {M : Type*} [AddCommMonoid M] (g : V → M) (hg : g 0 = 0) :
    ∑ p : Points V, g p = ∑ v, g v := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun v : V => v ≠ 0) g]
  have h0 : ∑ v : {v : V // ¬v ≠ 0}, g v = 0 :=
    Finset.sum_eq_zero fun v _ => by rw [show (v : V) = 0 from not_not.mp v.2, hg]
  rw [h0, add_zero]

omit [DecidableEq V] in
theorem sum_smul_self_eq_zero (hV : finrank (ZMod 2) V = 3) (f : Module.Dual (ZMod 2) V) :
    ∑ v, f v • v = 0 := by
  by_cases h1 : ∃ w, f w = 1
  · obtain ⟨w, hw⟩ := h1
    set s := Finset.univ.filter fun v => f v = 1 with hs_def
    have hs : s.card = 4 := by
      have := two_mul_card_fiber_one f hw
      rw [card_eq_eight hV, ← hs_def] at this
      omega
    have : DecidablePred (· ∈ LinearMap.ker f) := fun v =>
      decidable_of_iff (f v = 0) LinearMap.mem_ker.symm
    let i : V → LinearMap.ker f := fun v => ⟨v + f v • w, by
      rw [LinearMap.mem_ker, map_add, map_smul, hw, smul_eq_mul, mul_one]
      exact (by decide : ∀ x : ZMod 2, x + x = 0) (f v)⟩
    let j : LinearMap.ker f → V := fun h => (h : V) + w
    have hj : ∀ h : LinearMap.ker f, j h ∈ s := fun h => by
      have := LinearMap.mem_ker.mp h.2
      simp only [hs_def, Finset.mem_filter, Finset.mem_univ, true_and, j, map_add, this, hw,
        zero_add]
    have hleft : ∀ v ∈ s, j (i v) = v := fun v hv => by
      have hv1 : f v = 1 := (Finset.mem_filter.mp hv).2
      simp only [i, j, hv1, one_smul, add_assoc, add_self_eq_zero', add_zero]
    have hright : ∀ h : LinearMap.ker f, i (j h) = h := fun h => by
      have hh := LinearMap.mem_ker.mp h.2
      apply Subtype.ext
      simp only [i, j, map_add, hh, hw, zero_add, one_smul, add_assoc, add_self_eq_zero', add_zero]
    have hcardK : Fintype.card (LinearMap.ker f) = 4 := by
      rw [← hs, ← Finset.card_univ]
      exact (Finset.card_nbij' i j (fun _ _ => Finset.mem_univ _) (fun h _ => hj h) hleft
        (fun h _ => hright h)).symm
    have hfv : ∀ v, f v • v = if f v = 1 then v else 0 := fun v => by
      rcases zmod2_eq_zero_or_one (f v) with h | h <;> simp [h]
    have hsum : ∑ v, f v • v = ∑ h : LinearMap.ker f, ((h : V) + w) := by
      simp only [hfv]
      rw [← Finset.sum_filter]
      exact Finset.sum_nbij' i j (fun _ _ => Finset.mem_univ _) (fun h _ => hj h) hleft
        (fun h _ => hright h) fun v hv => (hleft v hv).symm
    rw [hsum, Finset.sum_add_distrib, ← Submodule.coe_sum,
      sum_univ_eq_zero (by rw [hcardK]), Submodule.coe_zero, zero_add, Finset.sum_const,
      Finset.card_univ, hcardK, show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, two_nsmul,
      add_self_eq_zero']
  · have h0 : ∀ v, f v = 0 := fun v => by
      rcases zmod2_eq_zero_or_one (f v) with h | h
      · exact h
      · exact absurd ⟨v, h⟩ h1
    simp [h0]

variable (V) in
@[expose] def augmentationMap : (Points V → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ p, x p
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

variable (V) in
@[expose] def augmentation : Submodule (ZMod 2) (Points V → ZMod 2) :=
  LinearMap.ker (augmentationMap V)

omit [Module (ZMod 2) V] in
theorem mem_augmentation {x : Points V → ZMod 2} : x ∈ augmentation V ↔ ∑ p, x p = 0 :=
  LinearMap.mem_ker

@[expose] def pointAct (g : V ≃ₗ[ZMod 2] V) (p : Points V) : Points V :=
  ⟨g p, fun h => p.2 (g.map_eq_zero_iff.mp h)⟩

@[expose] def pointPerm (g : V ≃ₗ[ZMod 2] V) : Equiv.Perm (Points V) where
  toFun := pointAct g
  invFun := pointAct g.symm
  left_inv p := Subtype.ext (g.symm_apply_apply p)
  right_inv p := Subtype.ext (g.apply_symm_apply p)

@[expose] def permAct (g : V ≃ₗ[ZMod 2] V) (x : Points V → ZMod 2) : Points V → ZMod 2 :=
  fun p => x (pointAct g.symm p)

@[expose] def dualAct (g : V ≃ₗ[ZMod 2] V) (f : Module.Dual (ZMod 2) V) :
    Module.Dual (ZMod 2) V :=
  f ∘ₗ g.symm.toLinearMap

theorem sum_permAct (g : V ≃ₗ[ZMod 2] V) (x : Points V → ZMod 2) :
    ∑ p, permAct g x p = ∑ p, x p :=
  Equiv.sum_comp (pointPerm g.symm) x

theorem permAct_mem (g : V ≃ₗ[ZMod 2] V) {x : Points V → ZMod 2} (hx : x ∈ augmentation V) :
    permAct g x ∈ augmentation V := by
  rw [mem_augmentation, sum_permAct]; exact mem_augmentation.mp hx

@[expose] def permActU (g : V ≃ₗ[ZMod 2] V) (x : augmentation V) : augmentation V :=
  ⟨permAct g x, permAct_mem g x.2⟩

theorem kappa_mem (hV : finrank (ZMod 2) V = 3) (f : Module.Dual (ZMod 2) V) :
    (fun p : Points V => f p) ∈ augmentation V := by
  rw [mem_augmentation, sum_points (fun v => f v) (map_zero f)]
  exact sum_dual_eq_zero (by rw [card_eq_eight hV]; norm_num) f

@[expose] def kappa (hV : finrank (ZMod 2) V = 3) :
    Module.Dual (ZMod 2) V →ₗ[ZMod 2] augmentation V where
  toFun f := ⟨fun p => f p, kappa_mem hV f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (V) in
@[expose] def theta : augmentation V →ₗ[ZMod 2] V where
  toFun x := ∑ p, (x : Points V → ZMod 2) p • (p : V)
  map_add' x y := by
    simp only [Submodule.coe_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply,
      Finset.smul_sum]

variable (V) in
@[expose] def thetaFull : (Points V → ZMod 2) →ₗ[ZMod 2] V where
  toFun x := ∑ p, x p • (p : V)
  map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

theorem theta_apply (x : augmentation V) :
    theta V x = thetaFull V (x : Points V → ZMod 2) :=
  rfl

theorem kappa_equivariant (hV : finrank (ZMod 2) V = 3) (g : V ≃ₗ[ZMod 2] V)
    (f : Module.Dual (ZMod 2) V) :
    ((kappa hV (dualAct g f) : augmentation V) : Points V → ZMod 2) =
      permAct g (kappa hV f) :=
  rfl

theorem theta_equivariant (g : V ≃ₗ[ZMod 2] V) (x : augmentation V) :
    theta V (permActU g x) = g (theta V x) := by
  change ∑ p, (x : Points V → ZMod 2) (pointAct g.symm p) • (p : V) =
    g (∑ p, (x : Points V → ZMod 2) p • (p : V))
  rw [map_sum, ← Equiv.sum_comp (pointPerm g)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp : pointAct g.symm (pointAct g p) = p := Subtype.ext (g.symm_apply_apply _)
  change (x : Points V → ZMod 2) (pointAct g.symm (pointAct g p)) • (g p) = _
  rw [hp, map_smul]

theorem kappa_injective (hV : finrank (ZMod 2) V = 3) : Function.Injective (kappa hV) := by
  intro f f' h
  ext v
  by_cases hv : v = 0
  · rw [hv, map_zero, map_zero]
  · exact congrFun (congrArg Subtype.val h) ⟨v, hv⟩

theorem theta_surjective (hV : finrank (ZMod 2) V = 3) : Function.Surjective (theta V) := by
  intro v
  by_cases hv : v = 0
  · exact ⟨0, by rw [hv, map_zero]⟩
  obtain ⟨u, hu⟩ : ∃ u : V, u ∉ Submodule.span (ZMod 2) {v} := by
    by_contra h
    push Not at h
    have htop : Submodule.span (ZMod 2) {v} = ⊤ := eq_top_iff.mpr fun u _ => h u
    have h1 := finrank_span_singleton (K := ZMod 2) hv
    rw [htop, finrank_top, hV] at h1
    exact absurd h1 (by norm_num)
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Submodule.zero_mem _)
  have huv0 : u + v ≠ 0 := fun h => hu (by
    have huv : u = v := by
      calc u = u + (v + v) := by rw [add_self_eq_zero', add_zero]
        _ = (u + v) + v := by rw [add_assoc]
        _ = v := by rw [h, zero_add]
    rw [huv]
    exact Submodule.mem_span_singleton_self v)
  let x : Points V → ZMod 2 := Pi.single ⟨u, hu0⟩ 1 + Pi.single ⟨u + v, huv0⟩ 1
  have hx : x ∈ augmentation V := by
    rw [mem_augmentation]
    simp only [x, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
      ite_true]
    decide
  refine ⟨⟨x, hx⟩, ?_⟩
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk, x, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]
  rw [Finset.sum_eq_single ⟨u, hu0⟩ (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ _) h),
    Finset.sum_eq_single ⟨u + v, huv0⟩ (fun b _ hb => by simp [hb])
      (fun h => absurd (Finset.mem_univ _) h)]
  simp only [Pi.single_eq_same, one_smul]
  rw [← add_assoc, add_self_eq_zero', zero_add]

theorem natCard_augmentation (hV : finrank (ZMod 2) V = 3) :
    Nat.card (augmentation V) = 64 := by
  have hsurj : Function.Surjective (augmentationMap V) := by
    intro c
    have hpos : 0 < Fintype.card (Points V) := by rw [card_points hV]; norm_num
    obtain ⟨p⟩ := Fintype.card_pos_iff.mp hpos
    refine ⟨Pi.single p c, ?_⟩
    simp [augmentationMap, Finset.sum_pi_single']
  have hker := AddSubgroup.card_ker_mul_card_range (augmentationMap V).toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card (α := Points V), card_points hV] at hker
  have heq : Nat.card (augmentation V) = Nat.card (augmentationMap V).toAddMonoidHom.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [AddMonoidHom.mem_ker]; exact LinearMap.mem_ker)
  rw [heq]
  omega

theorem range_kappa_le (hV : finrank (ZMod 2) V = 3) :
    LinearMap.range (kappa hV) ≤ LinearMap.ker (theta V) := by
  rintro _ ⟨f, rfl⟩
  rw [LinearMap.mem_ker]
  change ∑ p : Points V, f p • (p : V) = 0
  rw [sum_points (fun v => f v • v) (by rw [smul_zero])]
  exact sum_smul_self_eq_zero hV f

theorem natCard_ker_theta (hV : finrank (ZMod 2) V = 3) :
    Nat.card (LinearMap.ker (theta V)) = 8 := by
  let Θ := (augmentationMap V).prod (thetaFull V)
  have hsurj : Function.Surjective Θ := by
    rintro ⟨c, v⟩
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · obtain ⟨x, hx⟩ := theta_surjective hV v
      exact ⟨x, Prod.ext (mem_augmentation.mp x.2) hx⟩
    · have hpos : 0 < Fintype.card (Points V) := by rw [card_points hV]; norm_num
      obtain ⟨p⟩ := Fintype.card_pos_iff.mp hpos
      obtain ⟨x, hx⟩ := theta_surjective hV (v + p)
      refine ⟨(x : Points V → ZMod 2) + Pi.single p 1, Prod.ext ?_ ?_⟩
      · change augmentationMap V _ = 1
        rw [map_add]
        change ∑ q, (x : Points V → ZMod 2) q + ∑ q, (Pi.single p 1 : Points V → ZMod 2) q = 1
        rw [mem_augmentation.mp x.2, Finset.sum_pi_single']
        simp
      · change thetaFull V _ = v
        rw [map_add, ← theta_apply, hx]
        change v + (p : V) + ∑ q, (Pi.single p 1 : Points V → ZMod 2) q • (q : V) = v
        rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb])
          (fun h => absurd (Finset.mem_univ _) h), Pi.single_eq_same, one_smul, add_assoc,
          add_self_eq_zero', add_zero]
  have hker := AddSubgroup.card_ker_mul_card_range Θ.toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card (α := Points V), card_points hV, Nat.card_prod, Nat.card_zmod,
    Nat.card_eq_fintype_card (α := V), card_eq_eight hV] at hker
  have heq : Nat.card (LinearMap.ker (theta V)) = Nat.card Θ.toAddMonoidHom.ker :=
    Nat.card_congr
      { toFun := fun y => ⟨((y : augmentation V) : Points V → ZMod 2), by
          rw [AddMonoidHom.mem_ker]
          exact Prod.ext (mem_augmentation.mp (y : augmentation V).2) (LinearMap.mem_ker.mp y.2)⟩
        invFun := fun x => ⟨⟨x, congrArg Prod.fst (AddMonoidHom.mem_ker.mp x.2)⟩,
          LinearMap.mem_ker.mpr (congrArg Prod.snd (AddMonoidHom.mem_ker.mp x.2))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [heq]
  omega

omit [DecidableEq V] in
theorem natCard_dual (hV : finrank (ZMod 2) V = 3) :
    Nat.card (Module.Dual (ZMod 2) V) = 8 := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hV
  rw [Nat.card_congr b.dualBasis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem natCard_range_kappa (hV : finrank (ZMod 2) V = 3) :
    Nat.card (LinearMap.range (kappa hV)) = 8 := by
  have h1 : Nat.card (LinearMap.range (kappa hV)) = Nat.card (Module.Dual (ZMod 2) V) := by
    rw [← Nat.card_range_of_injective (kappa_injective hV)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [LinearMap.mem_range]; rfl)
  rw [h1, natCard_dual hV]

theorem ker_theta_eq (hV : finrank (ZMod 2) V = 3) :
    LinearMap.ker (theta V) = LinearMap.range (kappa hV) := by
  refine (SetLike.coe_injective (Set.eq_of_subset_of_ncard_le (range_kappa_le hV) ?_)).symm
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  change Nat.card (LinearMap.ker (theta V)) ≤ Nat.card (LinearMap.range (kappa hV))
  rw [natCard_ker_theta hV, natCard_range_kappa hV]

abbrev onePoints (V : Type*) [AddCommGroup V] : Points V → ZMod 2 := fun _ => 1

theorem isCompl_onePoints (hV : finrank (ZMod 2) V = 3) :
    IsCompl (Submodule.span (ZMod 2) {onePoints V}) (augmentation V) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxU
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have := mem_augmentation.mp hxU
    simp only [Pi.smul_apply, smul_eq_mul, mul_one] at this
    rw [Finset.sum_const, Finset.card_univ, card_points hV, nsmul_eq_mul] at this
    have hc : c = 0 := by
      have h7 : ((7 : ℕ) : ZMod 2) = 1 := by decide
      rwa [h7, one_mul] at this
    rw [hc, zero_smul]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hdecomp : x = (∑ p, x p) • onePoints V + (x + (∑ p, x p) • onePoints V) := by
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
      exact (by decide : ∀ a b : ZMod 2, a = b + (a + b)) _ _
    rw [hdecomp]
    refine Submodule.add_mem_sup (Submodule.mem_span_singleton.mpr ⟨_, rfl⟩) ?_
    rw [mem_augmentation]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_points hV, nsmul_eq_mul]
    have h7 : ((7 : ℕ) : ZMod 2) = 1 := by decide
    rw [h7, one_mul]
    exact (by decide : ∀ a : ZMod 2, a + a = 0) _

theorem seven_point_augmentation_natural_dual_filtration (hV : finrank (ZMod 2) V = 3) :
    (∀ (g : V ≃ₗ[ZMod 2] V) (f : Module.Dual (ZMod 2) V),
      ((kappa hV (dualAct g f) : augmentation V) : Points V → ZMod 2) =
        permAct g (kappa hV f)) ∧
    (∀ (g : V ≃ₗ[ZMod 2] V) (x : augmentation V), theta V (permActU g x) = g (theta V x)) ∧
    Function.Injective (kappa hV) ∧ Function.Surjective (theta V) ∧
    LinearMap.ker (theta V) = LinearMap.range (kappa hV) ∧
    IsCompl (Submodule.span (ZMod 2) {onePoints V}) (augmentation V) ∧
    ∀ g : V ≃ₗ[ZMod 2] V, permAct g (onePoints V) = onePoints V :=
  ⟨kappa_equivariant hV, theta_equivariant, kappa_injective hV, theta_surjective hV,
    ker_theta_eq hV, isCompl_onePoints hV, fun _ => rfl⟩

end CFSG.ProperTwoGeneratedCore.BinaryThreeSpace
