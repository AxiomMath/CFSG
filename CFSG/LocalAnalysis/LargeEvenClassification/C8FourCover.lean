module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourLifts

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def c8FourCoverBit (q : ZMod 4) : ZMod 2 :=
  ((1 + 2 * (q.val : ZMod 8)).val / 4 : ℕ)

@[expose] def c8FourKappa (h k : C8FourCode) : ZMod 2 :=
  let c := c8FourCoefficients h
  let d := c8FourCoefficients k
  let r : ZMod 4 := 3 * d.1.2
  let z : ZMod 8 := 2 * (c.2.1.val : ZMod 8) * (5 * (r.val : ZMod 8)) +
    (c.2.2.val : ZMod 8) * (d.2.2.val : ZMod 8) - ((c8FourCoefficients (h * k)).2.2.val : ZMod 8)
  (z.val / 4 : ℕ)

@[expose] def c8FourKappaEntries (γ β η θ : ZMod 4) : ZMod 2 :=
  let z : ZMod 8 := 2 * (γ.val : ZMod 8) * (5 * ((3 * β).val : ZMod 8)) +
    (η.val : ZMod 8) * (θ.val : ZMod 8) - ((2 * γ * β + η * θ).val : ZMod 8)
  (z.val / 4 : ℕ)

theorem c8FourKappa_entries (h k : C8FourCode) :
    c8FourKappa h k = c8FourKappaEntries (c8FourCoefficients h).2.1 (c8FourCoefficients k).1.2
      (c8FourCoefficients h).2.2 (c8FourCoefficients k).2.2 := by
  rw [c8FourKappa, c8Four_coefficients_mul]
  rfl

set_option maxHeartbeats 8000000 in
theorem c8Four_cover_bit_identity (h k : C8FourCode) (q r : ZMod 4)
    (hq : 1 + 2 * q = (c8FourCoefficients h).2.2)
    (hr : 1 + 2 * r = (c8FourCoefficients k).2.2) :
    c8FourCoverBit (q + (c8FourCoefficients h).2.1 * (3 * (c8FourCoefficients k).1.2) +
      (c8FourCoefficients h).2.2 * r) = c8FourCoverBit q + c8FourCoverBit r + c8FourKappa h k := by
  have hfinite : ∀ γ β η θ q r : ZMod 4,
      1 + 2 * q = η → 1 + 2 * r = θ →
      c8FourCoverBit (q + γ * (3 * β) + η * r) = c8FourCoverBit q + c8FourCoverBit r +
        c8FourKappaEntries γ β η θ := by
    decide +kernel
  rw [c8FourKappa_entries]
  exact hfinite _ _ _ _ q r hq hr

section ActualCover

variable {S : Type*} [Group S]
variable (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
variable (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
variable (coordinates : Additive A ≃+ CyclicPair 2 4)
variable (t : S)
variable (ht : c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) t) = c8FourDelta)

include hselfCentralizing ht in
theorem c8Four_cover_difference_mem (s : S) : t⁻¹ * s * t * s⁻¹ ∈ A := by
  let e := c8FourAutomorphismEquiv hcommutative coordinates
  have hk : (MulAut.conjNormal (H := A)).ker = A := (conjNormal_ker_eq_centralizer A).trans hselfCentralizing
  apply hk.le
  apply e.injective
  change e (MulAut.conjNormal (H := A) (t⁻¹ * s * t * s⁻¹)) = e 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv,
    map_mul, map_mul, map_mul, map_inv, map_inv, ht, map_one]
  have hc := c8FourDelta_central (e (MulAut.conjNormal (H := A) s))
  rw [mul_assoc c8FourDelta⁻¹, hc.eq.symm]
  group

@[expose] noncomputable def c8FourCoverDifference (s : S) : A :=
  ⟨t⁻¹ * s * t * s⁻¹, c8Four_cover_difference_mem A hcommutative hselfCentralizing coordinates t ht s⟩

@[expose] noncomputable def c8FourCoverShort (s : S) : ZMod 4 :=
  (coordinates (Additive.ofMul (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s))).2

theorem c8FourCoverDifference_mul (s r : S) :
    c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht (s * r) =
      c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s *
        MulAut.conjNormal (H := A) s (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht r) := by
  apply Subtype.ext
  dsimp only [c8FourCoverDifference]
  rw [Subgroup.coe_mul, MulAut.conjNormal_apply]
  group

theorem c8FourCoverDifference_conjugate (s : S) :
    s * t * s⁻¹ = t * (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s : S) := by
  dsimp only [c8FourCoverDifference]
  group

include ht in
theorem c8Four_scalar_action_short (a : A) :
    (coordinates (Additive.ofMul (MulAut.conjNormal (H := A) t a))).2 =
      (coordinates (Additive.ofMul a)).2 := by
  rw [c8FourAutomorphismEquiv_apply hcommutative coordinates, ht]
  have h : ∀ x : CyclicPair 2 4, (c8FourApply c8FourDelta x).2 = x.2 := by decide +kernel
  exact h _

theorem c8FourCoverShort_normal (a : A) :
    c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht a = 0 := by
  have htInv : MulAut.conjNormal (H := A) t⁻¹ = MulAut.conjNormal (H := A) t := by
    let e := c8FourAutomorphismEquiv hcommutative coordinates
    apply e.injective
    rw [map_inv, map_inv, ht]
    have h : c8FourDelta⁻¹ = c8FourDelta := by decide +kernel
    exact h
  have hdiff : c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht a =
      MulAut.conjNormal (H := A) t a * a⁻¹ := by
    apply Subtype.ext
    rw [← htInv, Subgroup.coe_mul, MulAut.conjNormal_apply, inv_inv]
    rfl
  rw [c8FourCoverShort, hdiff]
  change (coordinates (Additive.ofMul (MulAut.conjNormal (H := A) t a) + -Additive.ofMul a)).2 = 0
  rw [map_add, map_neg]
  change (coordinates (Additive.ofMul (MulAut.conjNormal (H := A) t a))).2 +
    -(coordinates (Additive.ofMul a)).2 = 0
  rw [c8Four_scalar_action_short A hcommutative coordinates t ht, add_neg_cancel]

theorem c8FourCoverShort_normal_left (a : A) (s : S) :
    c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht ((a : S) * s) =
      c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht s := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := @mul_comm' _ _ hcommutative }
  have hconj : MulAut.conjNormal (H := A) (a : S) = 1 := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact (show Commute (a : S) (b : S) from congrArg Subtype.val (mul_comm a b)).mul_inv_cancel
  rw [c8FourCoverShort, c8FourCoverDifference_mul, hconj]
  change (coordinates (Additive.ofMul (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht a) +
    Additive.ofMul (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s))).2 = _
  rw [map_add]
  change c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht a +
    c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht s = _
  rw [c8FourCoverShort_normal, zero_add]

theorem c8FourCoverShort_fibers (s r : S)
    (hequal : MulAut.conjNormal (H := A) s = MulAut.conjNormal (H := A) r) :
    c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht s =
      c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht r := by
  have hmem : s * r⁻¹ ∈ A := by
    rw [← hselfCentralizing, ← conjNormal_ker_eq_centralizer A]
    change MulAut.conjNormal (H := A) (s * r⁻¹) = 1
    rw [map_mul, map_inv, hequal, mul_inv_cancel]
  let a : A := ⟨s * r⁻¹, hmem⟩
  have heq : s = (a : S) * r := by dsimp only [a]; group
  rw [heq]
  exact c8FourCoverShort_normal_left A hcommutative hselfCentralizing coordinates t ht a r

variable (hsquare : t ^ 2 = ((coordinates.symm (0, 1)).toMul : S))

include hsquare

theorem c8FourCoverDifference_square (s : S) :
    c8FourApply (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s)) (0, 1) =
      (0, 1) + c8FourApply c8FourDelta
        (coordinates (Additive.ofMul (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s))) +
        coordinates (Additive.ofMul (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s)) := by
  let a := c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s
  let y := (coordinates.symm (0, 1)).toMul
  have htInv : MulAut.conjNormal (H := A) t⁻¹ = MulAut.conjNormal (H := A) t := by
    apply (c8FourAutomorphismEquiv hcommutative coordinates).injective
    rw [map_inv, map_inv, ht]
    decide +kernel
  have hy : MulAut.conjNormal (H := A) s y = y * MulAut.conjNormal (H := A) t a * a := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, MulAut.conjNormal_apply, ← htInv, MulAut.conjNormal_apply, inv_inv]
    rw [← hsquare]
    calc
      s * t ^ 2 * s⁻¹ = (s * t * s⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = (t * a) ^ 2 := by rw [c8FourCoverDifference_conjugate A hcommutative hselfCentralizing coordinates t ht s]
      _ = t ^ 2 * (t⁻¹ * (a : S) * t) * a := by simp only [pow_two]; group
  have h := congrArg (fun a : A => coordinates (Additive.ofMul a)) hy
  change coordinates (Additive.ofMul (MulAut.conjNormal (H := A) s y)) =
    coordinates (Additive.ofMul y + Additive.ofMul (MulAut.conjNormal (H := A) t a) + Additive.ofMul a) at h
  rw [map_add, map_add, c8FourAutomorphismEquiv_apply hcommutative coordinates,
    c8FourAutomorphismEquiv_apply hcommutative coordinates, ht] at h
  dsimp only [y] at h
  change c8FourApply _ (coordinates (coordinates.symm (0, 1))) =
    coordinates (coordinates.symm (0, 1)) + c8FourApply c8FourDelta _ + _ at h
  rw [coordinates.apply_symm_apply] at h
  exact h

theorem c8FourCoverShort_eta (s : S) :
    1 + 2 * c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht s =
      (c8FourCoefficients (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s))).2.2 := by
  have h := congrArg Prod.snd (c8FourCoverDifference_square A hcommutative hselfCentralizing coordinates t ht hsquare s)
  have hfinite : ∀ g : C8FourCode, ∀ a : CyclicPair 2 4,
      (c8FourApply g (0, 1)).2 = ((0, 1) + c8FourApply c8FourDelta a + a).2 →
      1 + 2 * a.2 = (c8FourCoefficients g).2.2 := by decide +kernel
  exact hfinite _ _ h

theorem c8FourCoverDifference_long (s : S) :
    cyclicReduction 2 4 (coordinates (Additive.ofMul
      (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s))).1 =
      3 * (c8FourCoefficients (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s))).1.2 := by
  have h := congrArg Prod.fst (c8FourCoverDifference_square A hcommutative hselfCentralizing coordinates t ht hsquare s)
  have hfinite : ∀ g : C8FourCode, ∀ a : CyclicPair 2 4,
      (c8FourApply g (0, 1)).1 = ((0, 1) + c8FourApply c8FourDelta a + a).1 →
      cyclicReduction 2 4 a.1 = 3 * (c8FourCoefficients g).1.2 := by decide +kernel
  exact hfinite _ _ h

theorem c8FourCoverShort_mul (s r : S) :
    c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht (s * r) =
      c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht s +
      (c8FourCoefficients (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s))).2.1 *
        (3 * (c8FourCoefficients (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) r))).1.2) +
      (c8FourCoefficients (c8FourAutomorphismEquiv hcommutative coordinates (MulAut.conjNormal (H := A) s))).2.2 *
        c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht r := by
  rw [c8FourCoverShort, c8FourCoverDifference_mul]
  change (coordinates (Additive.ofMul (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht s) +
    Additive.ofMul (MulAut.conjNormal (H := A) s (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht r)))).2 = _
  rw [map_add, c8FourAutomorphismEquiv_apply hcommutative coordinates]
  change c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht s +
    ((c8FourCoefficients _).2.1 * cyclicReduction 2 4 (coordinates (Additive.ofMul
      (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht r))).1 +
      (c8FourCoefficients _).2.2 * c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht r) = _
  rw [c8FourCoverDifference_long A hcommutative hselfCentralizing coordinates t ht hsquare]
  exact (add_assoc _ _ _).symm

end ActualCover

@[expose] def c8FourCompatible (H : Subgroup C8FourCode) : Prop :=
  ∃ b : H → ZMod 2, b 1 = 0 ∧ (∀ δ : H, δ.val = c8FourDelta → b δ = 0) ∧
    ∀ h k : H, b (h * k) = b h + b k + c8FourKappa h.val k.val

theorem c8_four_central_cover_compatibility {S : Type*} [Group S] [Finite S]
    (A : Subgroup S) [A.Normal] (hcommutative : IsMulCommutative A)
    (hselfCentralizing : Subgroup.centralizer (A : Set S) = A)
    (hnoEight : ∀ E : Subgroup S, E.Normal → CFSG.Open.IsElemAbelian 2 E → Nat.card E ≠ 8)
    (coordinates : Additive A ≃+ CyclicPair 2 4)
    (hdelta : c8FourDelta ∈ ((c8FourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))).range) :
    c8FourCompatible (((c8FourAutomorphismEquiv hcommutative coordinates).toMonoidHom.comp
      (MulAut.conjNormal (H := A))).range) := by
  classical
  let e := c8FourAutomorphismEquiv hcommutative coordinates
  let action := e.toMonoidHom.comp (MulAut.conjNormal (H := A))
  let H := action.range
  obtain ⟨t, ht⟩ := hdelta
  obtain ⟨t, hsquare, ht⟩ := c8_four_adjusted_scalar_lift A hcommutative hselfCentralizing hnoEight coordinates t ht
  let short := c8FourCoverShort A hcommutative hselfCentralizing coordinates t ht
  let lift (h : H) : S := Classical.choose h.property
  have hlift (h : H) : action (lift h) = h.val := Classical.choose_spec h.property
  have hfiber (s r : S) (heq : action s = action r) : short s = short r :=
    c8FourCoverShort_fibers A hcommutative hselfCentralizing coordinates t ht s r (e.injective heq)
  have hone : short 1 = 0 := by
    change (coordinates (Additive.ofMul (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht 1))).2 = 0
    have hdiff : c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht 1 = 1 := by
      apply Subtype.ext
      dsimp only [c8FourCoverDifference]
      change t⁻¹ * 1 * t * 1⁻¹ = (1 : S)
      group
    rw [hdiff]
    change (coordinates 0).2 = 0
    rw [map_zero]
    rfl
  have htzero : short t = 0 := by
    change (coordinates (Additive.ofMul (c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht t))).2 = 0
    have hdiff : c8FourCoverDifference A hcommutative hselfCentralizing coordinates t ht t = 1 := by
      apply Subtype.ext
      dsimp only [c8FourCoverDifference]
      change t⁻¹ * t * t * t⁻¹ = (1 : S)
      group
    rw [hdiff]
    change (coordinates 0).2 = 0
    rw [map_zero]
    rfl
  let q (h : H) := short (lift h)
  let b (h : H) := c8FourCoverBit (q h)
  refine ⟨b, ?_, ?_, ?_⟩
  · have hq : q 1 = 0 := by
      have heq : action (lift 1) = action 1 := (hlift 1).trans (map_one action).symm
      exact (hfiber _ _ heq).trans hone
    change c8FourCoverBit (q 1) = 0
    rw [hq]
    decide +kernel
  · intro δ hδ
    have hq : q δ = 0 := by
      have heq : action (lift δ) = action t := (hlift δ).trans (hδ.trans ht.symm)
      exact (hfiber _ _ heq).trans htzero
    change c8FourCoverBit (q δ) = 0
    rw [hq]
    decide +kernel
  · intro h k
    have hqproduct : q (h * k) = short (lift h * lift k) := by
      apply hfiber
      rw [map_mul, hlift, hlift, hlift]
      rfl
    have hqmul : q (h * k) = q h + (c8FourCoefficients h.val).2.1 *
        (3 * (c8FourCoefficients k.val).1.2) + (c8FourCoefficients h.val).2.2 * q k := by
      rw [hqproduct]
      have hmul := c8FourCoverShort_mul A hcommutative hselfCentralizing coordinates t ht hsquare (lift h) (lift k)
      change short (lift h * lift k) = short (lift h) + (c8FourCoefficients (action (lift h))).2.1 *
        (3 * (c8FourCoefficients (action (lift k))).1.2) + (c8FourCoefficients (action (lift h))).2.2 * short (lift k) at hmul
      simpa only [hlift] using hmul
    have hqeta (h : H) : 1 + 2 * q h = (c8FourCoefficients h.val).2.2 := by
      have h' := c8FourCoverShort_eta A hcommutative hselfCentralizing coordinates t ht hsquare (lift h)
      change 1 + 2 * short (lift h) = (c8FourCoefficients (action (lift h))).2.2 at h'
      simpa only [hlift] using h'
    change c8FourCoverBit (q (h * k)) = c8FourCoverBit (q h) + c8FourCoverBit (q k) + c8FourKappa h.val k.val
    rw [hqmul]
    exact c8Four_cover_bit_identity h.val k.val (q h) (q k) (hqeta h) (hqeta k)

end CFSG.LargeEvenClassification.Helpers
