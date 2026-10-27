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

public noncomputable section

namespace CFSG.Wreathed.OddNormalQuotientInvolutions

universe u

variable {N : Type u} [Group N]

@[expose] def involutions (K : Type*) [Group K] : Set K := {t | orderOf t = 2}

@[expose] def involutionFiber (R : Subgroup N) [R.Normal] (v : N ⧸ R) : Set N :=
  {t | orderOf t = 2 ∧ QuotientGroup.mk' R t = v}

theorem odd_power_eq {K : Type*} [Group K] (t : K) (ht : t ^ 2 = 1)
    {j : ℕ} (hj : Odd j) : t ^ j = t := by
  obtain ⟨k, rfl⟩ := hj
  rw [pow_add, pow_mul, ht, one_pow, pow_one, one_mul]

theorem quotient_involution (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (t : N) (ht : orderOf t = 2) : orderOf (QuotientGroup.mk' R t) = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  apply orderOf_eq_prime
  · rw [← map_pow, ht2, map_one]
  · intro h
    have hmem : t ∈ R := (QuotientGroup.eq_one_iff t).mp h
    have hpow : t ^ Nat.card R = 1 := by
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨t, hmem⟩ : R)))
    have ht1 : t = 1 := (odd_power_eq t ht2 hR).symm.trans hpow
    have : orderOf t = 1 := orderOf_eq_one_iff.mpr ht1
    omega

theorem exists_involution_lift (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (v : N ⧸ R) (hv : orderOf v = 2) :
    ∃ t : N, orderOf t = 2 ∧ QuotientGroup.mk' R t = v := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective R v
  have hv2 : v ^ 2 = 1 := hv ▸ pow_orderOf_eq_one v
  have ha2 : a ^ 2 ∈ R := (QuotientGroup.eq_one_iff (a ^ 2)).mp (by
    change QuotientGroup.mk' R (a ^ 2) = 1
    rw [map_pow, ha, hv2])
  have hsquare : (a ^ Nat.card R) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a ^ 2, ha2⟩ : R)))
  have himage : QuotientGroup.mk' R (a ^ Nat.card R) = v := by
    rw [map_pow, ha, odd_power_eq v hv2 hR]
  refine ⟨a ^ Nat.card R, orderOf_eq_prime hsquare ?_, himage⟩
  intro hone
  have : v = 1 := by rw [← himage, hone, map_one]
  have : orderOf v = 1 := orderOf_eq_one_iff.mpr this
  omega

theorem exists_kernel_conjugator (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (t u : N) (ht : orderOf t = 2) (hu : orderOf u = 2)
    (himage : QuotientGroup.mk' R u = QuotientGroup.mk' R t) :
    ∃ r : R, (r : N) * t * (r : N)⁻¹ = u := by
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hit : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have hiu : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two hu
  let a : N := u * t
  have ha : a ∈ R := (QuotientGroup.eq_one_iff a).mp (by
    change QuotientGroup.mk' R (u * t) = 1
    rw [map_mul, himage, ← pow_two, ← map_pow, ht2, map_one])
  have hodd : Odd (orderOf a) := Odd.of_dvd_nat hR (R.orderOf_dvd_natCard ha)
  obtain ⟨k, hk⟩ := hodd
  let r : N := a ^ (k + 1)
  have hr : r ∈ R := R.pow_mem ha (k + 1)
  have hainv : t * a⁻¹ * t⁻¹ = a := by
    simp only [a, mul_inv_rev, hit, hiu, ← mul_assoc, ← pow_two, ht2, one_mul]
  have hconj : t * r⁻¹ * t⁻¹ = r := by
    change t * (a ^ (k + 1))⁻¹ * t⁻¹ = a ^ (k + 1)
    rw [← inv_pow, ← conj_pow, hainv]
  have htr : t * r⁻¹ = r * t := mul_inv_eq_iff_eq_mul.mp hconj
  refine ⟨⟨r, hr⟩, ?_⟩
  change r * t * r⁻¹ = u
  calc
    r * t * r⁻¹ = r * (r * t) := by rw [mul_assoc, htr]
    _ = a ^ ((k + 1) + (k + 1)) * t := by rw [← mul_assoc, ← pow_add]
    _ = a ^ (orderOf a + 1) * t := by congr 2; omega
    _ = a * t := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
    _ = u := by simp only [a, mul_assoc, ← pow_two, ht2, mul_one]

theorem quotient_involutions_isConj_iff (R : Subgroup N) [R.Normal]
    (hR : Odd (Nat.card R)) {t u : N} (ht : orderOf t = 2) (hu : orderOf u = 2) :
    IsConj (QuotientGroup.mk' R t) (QuotientGroup.mk' R u) ↔ IsConj t u := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := isConj_iff.mp h
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective R q
    have ht' : orderOf (g * t * g⁻¹) = 2 :=
      ((MulAut.conj g).orderOf_eq t).trans ht
    have himage : QuotientGroup.mk' R u = QuotientGroup.mk' R (g * t * g⁻¹) := by
      rw [map_mul, map_mul, map_inv, hg, hq]
    obtain ⟨r, hr⟩ := exists_kernel_conjugator R hR (g * t * g⁻¹) u ht' hu himage
    exact isConj_iff.mpr ⟨(r : N) * g, by simpa [mul_inv_rev, mul_assoc] using hr⟩
  · exact (QuotientGroup.mk' R).map_isConj

@[expose] def involutionClasses (K : Type*) [Group K] : Set (ConjClasses K) :=
  ConjClasses.mk '' involutions K

theorem involutionClasses_bijOn (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R)) :
    Set.BijOn (ConjClasses.map (QuotientGroup.mk' R))
      (involutionClasses N) (involutionClasses (N ⧸ R)) := by
  apply Set.BijOn.mk
  · rintro c ⟨t, ht, rfl⟩
    exact ⟨QuotientGroup.mk' R t, quotient_involution R hR t ht, rfl⟩
  · rintro c ⟨t, ht, rfl⟩ d ⟨u, hu, rfl⟩ h
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact (quotient_involutions_isConj_iff R hR ht hu).mp
      (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  · rintro c ⟨v, hv, rfl⟩
    obtain ⟨t, ht, himage⟩ := exists_involution_lift R hR v hv
    refine ⟨ConjClasses.mk t, ⟨t, ht, rfl⟩, ?_⟩
    change ConjClasses.mk (QuotientGroup.mk' R t) = ConjClasses.mk v
    rw [himage]

@[expose] def involutionClassEquiv (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R)) :
    involutionClasses N ≃ involutionClasses (N ⧸ R) :=
  (involutionClasses_bijOn R hR).equiv (ConjClasses.map (QuotientGroup.mk' R))

theorem involutionClassEquiv_coe (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (c : involutionClasses N) :
    (involutionClassEquiv R hR c : ConjClasses (N ⧸ R)) =
      ConjClasses.map (QuotientGroup.mk' R) c := rfl

@[expose] def onCentralizer (R : Subgroup N) [R.Normal] (t : N) :
    Subgroup.centralizer {t} →* N ⧸ R :=
  (QuotientGroup.mk' R).comp (Subgroup.centralizer {t}).subtype

@[expose] def kernelCentralizer (R : Subgroup N) (t : N) : Subgroup R :=
  (Subgroup.centralizer {t}).subgroupOf R

theorem onCentralizer_ker (R : Subgroup N) [R.Normal] (t : N) :
    (onCentralizer R t).ker = R.subgroupOf (Subgroup.centralizer {t}) := by
  ext x
  change QuotientGroup.mk' R (x : N) = 1 ↔ (x : N) ∈ R
  exact QuotientGroup.eq_one_iff _

@[expose] def centralizerKernelEquiv (R : Subgroup N) (t : N) :
    R.subgroupOf (Subgroup.centralizer {t}) ≃* kernelCentralizer R t where
  toFun x := ⟨⟨((x : Subgroup.centralizer {t}) : N), x.property⟩, x.val.property⟩
  invFun x := ⟨⟨((x : R) : N), x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem centralizer_lift (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (t : N) (ht : orderOf t = 2) (q : N ⧸ R)
    (hq : q ∈ Subgroup.centralizer {QuotientGroup.mk' R t}) :
    ∃ x : N, x ∈ Subgroup.centralizer {t} ∧ QuotientGroup.mk' R x = q := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective R q
  have ht' : orderOf (g * t * g⁻¹) = 2 := ((MulAut.conj g).orderOf_eq t).trans ht
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hq
  have himage : QuotientGroup.mk' R (g * t * g⁻¹) = QuotientGroup.mk' R t := by
    rw [map_mul, map_mul, map_inv, hg, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨r, hr⟩ := exists_kernel_conjugator R hR (g * t * g⁻¹) t ht' ht himage.symm
  refine ⟨(r : N) * g, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
  · apply mul_inv_eq_iff_eq_mul.mp
    simpa [mul_inv_rev, mul_assoc] using hr
  · have hrone : QuotientGroup.mk' R (r : N) = 1 := by
      change ((r : N) : N ⧸ R) = 1
      exact (QuotientGroup.eq_one_iff _).mpr r.property
    rw [map_mul, hrone, hg, one_mul]

theorem centralizer_map (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (t : N) (ht : orderOf t = 2) :
    (Subgroup.centralizer {t}).map (QuotientGroup.mk' R) =
      Subgroup.centralizer {QuotientGroup.mk' R t} := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg (QuotientGroup.mk' R) (Subgroup.mem_centralizer_singleton_iff.mp hx))
  · intro hq
    obtain ⟨x, hx, himage⟩ := centralizer_lift R hR t ht q hq
    exact ⟨x, hx, himage⟩

@[expose] def centralizerQuotient (R : Subgroup N) [R.Normal] (t : N) :
    Subgroup.centralizer {t} →* Subgroup.centralizer {QuotientGroup.mk' R t} :=
  (onCentralizer R t).codRestrict _ (fun x =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg (QuotientGroup.mk' R) (Subgroup.mem_centralizer_singleton_iff.mp x.property)))

theorem centralizerQuotient_coe (R : Subgroup N) [R.Normal] (t : N)
    (x : Subgroup.centralizer {t}) :
    (centralizerQuotient R t x : N ⧸ R) = QuotientGroup.mk' R (x : N) := rfl

theorem centralizerQuotient_surjective (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (t : N) (ht : orderOf t = 2) : Function.Surjective (centralizerQuotient R t) := by
  intro q
  obtain ⟨x, hx, himage⟩ := centralizer_lift R hR t ht q q.property
  exact ⟨⟨x, hx⟩, Subtype.ext himage⟩

theorem centralizerQuotient_ker (R : Subgroup N) [R.Normal] (t : N) :
    (centralizerQuotient R t).ker = R.subgroupOf (Subgroup.centralizer {t}) := by
  ext x
  change centralizerQuotient R t x = 1 ↔ (x : N) ∈ R
  rw [← Subtype.coe_inj]
  exact QuotientGroup.eq_one_iff _

theorem centralizer_card (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (t : N) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer {t}) = Nat.card (kernelCentralizer R t) *
      Nat.card (Subgroup.centralizer {QuotientGroup.mk' R t}) := by
  have h := Subgroup.card_ker_mul_card_of_surjective
    (centralizerQuotient_surjective R hR t ht)
  rw [centralizerQuotient_ker, Nat.card_congr (centralizerKernelEquiv R t).toEquiv] at h
  exact h.symm

@[expose, instance_reducible] def kernelAction (R : Subgroup N) : MulAction R N :=
  MulAction.compHom N (MulAut.conj.comp R.subtype)

theorem kernel_stabilizer (R : Subgroup N) (t : N) :
    let : MulAction R N := kernelAction R
    MulAction.stabilizer R t = kernelCentralizer R t := by
  let : MulAction R N := kernelAction R
  ext r
  change (r : N) * t * (r : N)⁻¹ = t ↔ (r : N) ∈ Subgroup.centralizer {t}
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem orbit_eq_involutionFiber (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (t : N) (ht : orderOf t = 2) :
    let : MulAction R N := kernelAction R
    MulAction.orbit R t = involutionFiber R (QuotientGroup.mk' R t) := by
  let : MulAction R N := kernelAction R
  ext u
  constructor
  · intro hu
    obtain ⟨r, hr⟩ := MulAction.mem_orbit_iff.mp hu
    change (r : N) * t * (r : N)⁻¹ = u at hr
    change orderOf u = 2 ∧ QuotientGroup.mk' R u = QuotientGroup.mk' R t
    rw [← hr]
    refine ⟨((MulAut.conj (r : N)).orderOf_eq t).trans ht, ?_⟩
    have hrone : QuotientGroup.mk' R (r : N) = 1 := by
      change ((r : N) : N ⧸ R) = 1
      exact (QuotientGroup.eq_one_iff _).mpr r.property
    rw [map_mul, map_mul, map_inv, hrone, one_mul, inv_one, mul_one]
  · intro hu
    obtain ⟨r, hr⟩ := exists_kernel_conjugator R hR t u ht hu.1 hu.2
    exact MulAction.mem_orbit_iff.mpr ⟨r, hr⟩

theorem involutionFiber_card (R : Subgroup N) [R.Normal]
    (hR : Odd (Nat.card R)) (t : N) (ht : orderOf t = 2) :
    Nat.card (involutionFiber R (QuotientGroup.mk' R t)) = (kernelCentralizer R t).index := by
  let : MulAction R N := kernelAction R
  rw [← orbit_eq_involutionFiber R hR t ht, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer, kernel_stabilizer]

theorem central_involutionFiber (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R))
    (t : N) (ht : orderOf t = 2) (hc : t ∈ Subgroup.center N) :
    involutionFiber R (QuotientGroup.mk' R t) = {t} := by
  ext u
  constructor
  · intro hu
    obtain ⟨r, hr⟩ := exists_kernel_conjugator R hR t u ht hu.1 hu.2
    have hcomm := (Subgroup.mem_center_iff.mp hc (r : N))
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one] at hr
    exact hr.symm
  · rintro rfl
    exact ⟨ht, rfl⟩

theorem conjClass_card (t : N) :
    Nat.card ((ConjClasses.mk t).carrier) = (Subgroup.centralizer {t}).index := by
  exact (Nat.card_coe_set_eq (conjugatesOf t)).trans
    (Subgroup.index_centralizer_eq_ncard t).symm

theorem conjClass_card_quotient [Finite N] (R : Subgroup N) [R.Normal]
    (hR : Odd (Nat.card R)) (t : N) (ht : orderOf t = 2) :
    Nat.card ((ConjClasses.mk t).carrier) = (kernelCentralizer R t).index *
      Nat.card ((ConjClasses.mk (QuotientGroup.mk' R t)).carrier) := by
  rw [conjClass_card, conjClass_card]
  have hN : Nat.card (Subgroup.centralizer {t}) *
      (Subgroup.centralizer {t}).index = Nat.card N := Subgroup.card_mul_index _
  have hH : Nat.card (Subgroup.centralizer {QuotientGroup.mk' R t}) *
      (Subgroup.centralizer {QuotientGroup.mk' R t}).index = Nat.card (N ⧸ R) :=
    Subgroup.card_mul_index _
  have hRcard : Nat.card (kernelCentralizer R t) * (kernelCentralizer R t).index =
      Nat.card R := Subgroup.card_mul_index _
  have hNH : Nat.card R * Nat.card (N ⧸ R) = Nat.card N := by
    simpa only [QuotientGroup.ker_mk'] using
      Subgroup.card_ker_mul_card_of_surjective (QuotientGroup.mk'_surjective R)
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Subgroup.centralizer {t}))
  calc
    Nat.card (Subgroup.centralizer {t}) * (Subgroup.centralizer {t}).index =
        Nat.card N := hN
    _ = Nat.card R * Nat.card (N ⧸ R) := hNH.symm
    _ = (Nat.card (kernelCentralizer R t) * (kernelCentralizer R t).index) *
        (Nat.card (Subgroup.centralizer {QuotientGroup.mk' R t}) *
          (Subgroup.centralizer {QuotientGroup.mk' R t}).index) := by rw [hRcard, hH]
    _ = Nat.card (Subgroup.centralizer {t}) *
        ((kernelCentralizer R t).index *
          (Subgroup.centralizer {QuotientGroup.mk' R t}).index) := by
      rw [centralizer_card R hR t ht]
      ac_rfl

theorem odd_normal_quotient_involution_classes_and_centralizers [Finite N]
    (R : Subgroup N) [R.Normal] (hR : Odd (Nat.card R)) :
    Set.BijOn (ConjClasses.map (QuotientGroup.mk' R))
      (involutionClasses N) (involutionClasses (N ⧸ R)) ∧
    (∀ v : N ⧸ R, orderOf v = 2 → ∃ t : N, orderOf t = 2 ∧ QuotientGroup.mk' R t = v) ∧
    (∀ v : N ⧸ R, ∀ t : N, orderOf t = 2 → QuotientGroup.mk' R t = v →
      (Subgroup.centralizer {t}).map (QuotientGroup.mk' R) = Subgroup.centralizer {v} ∧
      (onCentralizer R t).ker = R.subgroupOf (Subgroup.centralizer {t}) ∧
      Nat.card (Subgroup.centralizer {t}) =
        Nat.card (kernelCentralizer R t) * Nat.card (Subgroup.centralizer {v}) ∧
      Nat.card ((ConjClasses.mk t).carrier) = (kernelCentralizer R t).index *
        Nat.card ((ConjClasses.mk v).carrier) ∧
      Nat.card (involutionFiber R v) = (kernelCentralizer R t).index ∧
      (∀ u : N, orderOf u = 2 → QuotientGroup.mk' R u = v →
        ∃ r : R, (r : N) * t * (r : N)⁻¹ = u) ∧
      (t ∈ Subgroup.center N → involutionFiber R v = {t})) := by
  refine ⟨involutionClasses_bijOn R hR, exists_involution_lift R hR, ?_⟩
  intro v t ht himage
  subst v
  refine ⟨centralizer_map R hR t ht, onCentralizer_ker R t, centralizer_card R hR t ht,
    conjClass_card_quotient R hR t ht, involutionFiber_card R hR t ht, ?_, ?_⟩
  · exact fun u hu heq => exists_kernel_conjugator R hR t u ht hu heq
  · exact central_involutionFiber R hR t ht

end CFSG.Wreathed.OddNormalQuotientInvolutions
