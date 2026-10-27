module

public import CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
public import CFSG.LieType.Ree.LargeReeRootInvolution

public noncomputable section

namespace CFSG.EvenSmallLie.FFourTwo

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
open scoped commutatorElement

structure Cover (K : Type) [Field K] (M : Type*) [Group M] where
  card : Nat.card K = 2
  π : M →* adjointGroup .F4 K
  surj : Function.Surjective π
  ker_le : π.ker ≤ center M
  z : M
  z_ne : z ≠ 1
  ker_iff : ∀ k, π k = 1 ↔ k = 1 ∨ k = z

namespace Cover

variable {K : Type} [Field K] {M : Type*} [Group M] (C : Cover K M)

@[expose] def lift (x : adjointGroup .F4 K) : M := Function.surjInv C.surj x

theorem π_lift (x : adjointGroup .F4 K) : C.π (C.lift x) = x := Function.surjInv_eq C.surj x

theorem π_z : C.π C.z = 1 := (C.ker_iff C.z).2 (Or.inr rfl)

theorem z_mem_center : C.z ∈ center M := C.ker_le C.π_z

theorem z_comm (m : M) : m * C.z = C.z * m := mem_center_iff.1 C.z_mem_center m

theorem z_mul_z : C.z * C.z = 1 := by
  rcases (C.ker_iff (C.z * C.z)).1 (by rw [map_mul, C.π_z, one_mul]) with h | h
  · exact h
  · exact absurd (mul_eq_left.1 h) C.z_ne

theorem eq_or_eq_mul {e e' : M} (h : C.π e = C.π e') : e' = e ∨ e' = e * C.z := by
  rcases (C.ker_iff (e⁻¹ * e')).1 (by rw [map_mul, map_inv, h, inv_mul_cancel]) with h' | h'
  · left; rw [← mul_inv_cancel_left e e', h', mul_one]
  · right; rw [← mul_inv_cancel_left e e', h']

theorem mul_self_of_root
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) {e : M}
    (he : C.π e = xr r) : e * e = 1 := by
  obtain ⟨y, hy, hy2⟩ := exists_lift_mul_self_xr C.card C.surj C.ker_le hr
  rcases C.eq_or_eq_mul (hy.trans he.symm) with h | h
  · rw [h, hy2]
  · rw [h]
    calc y * C.z * (y * C.z) = y * (C.z * y) * C.z := by group
      _ = y * y * (C.z * C.z) := by rw [← C.z_comm y]; group
      _ = 1 := by rw [hy2, C.z_mul_z, one_mul]

theorem commutator_eq {a a' b b' : M} (ha : C.π a = C.π a') (hb : C.π b = C.π b') :
    ⁅a, b⁆ = ⁅a', b'⁆ :=
  commutatorElement_lift_eq C.ker_le ha hb

theorem commutator_commute {a b y : M} (ha : C.π y * C.π a = C.π a * C.π y)
    (hb : C.π y * C.π b = C.π b * C.π y) : y * ⁅a, b⁆ = ⁅a, b⁆ * y := by
  have h1 : C.π (y * a * y⁻¹) = C.π a := by rw [map_mul, map_mul, map_inv, ha, mul_inv_cancel_right]
  have h2 : C.π (y * b * y⁻¹) = C.π b := by rw [map_mul, map_mul, map_inv, hb, mul_inv_cancel_right]
  have h := C.commutator_eq h1 h2
  have e : ⁅y * a * y⁻¹, y * b * y⁻¹⁆ = y * ⁅a, b⁆ * y⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem liftsCommute_shortOrth
    : LiftsCommute C.π (xr vS1) (xr vE2) := by
  intro e f he hf
  set a : Fin Tag.F4.rank → ℤ := ![1, 0, 0, 0]
  set b : Fin Tag.F4.rank → ℤ := ![0, 1, 1, 0]
  obtain ⟨-, -, -, -, h5, -⟩ := xr_commutatorElement_mixed (K := K) C.card (r := a) (s := b)
    (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  rw [eq_of_ofFn (show List.ofFn (a + b) = List.ofFn vE2 by decide +kernel),
    eq_of_ofFn (show List.ofFn (a + 2 • b) = List.ofFn vE23 by decide +kernel)] at h5
  set ea := C.lift (xr a)
  set eb := C.lift (xr b)
  set ec := C.lift (xr vE23)
  have hc2 : xr (K := K) vE23 * xr vE23 = 1 :=
      xr_mul_self C.card (isRoot_of_ofFn (by decide +kernel))
  have hf' : C.π (⁅ea, eb⁆ * ec) = C.π f := by
    rw [map_mul, map_commutatorElement, C.π_lift, C.π_lift, C.π_lift, h5, mul_assoc, hc2, mul_one,
      hf]
  have ca : xr (K := K) vS1 * xr a = xr a * xr vS1 := xr_commute C.card
    (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have cb : xr (K := K) vS1 * xr b = xr b * xr vS1 := xr_commute C.card
    (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hcomm : e * (⁅ea, eb⁆ * ec) = ⁅ea, eb⁆ * ec * e := by
    have h1 : e * ⁅ea, eb⁆ = ⁅ea, eb⁆ * e := C.commutator_commute
      (by rw [he, C.π_lift]; exact ca) (by rw [he, C.π_lift]; exact cb)
    have h2 : e * ec = ec * e := liftsCommute_xr C.card C.surj C.ker_le
      (rootPair_of_ofFn (by decide +kernel)) (Or.inr (Or.inr (Or.inl ⟨by decide +kernel,
        by decide +kernel, Or.inl (by decide +kernel)⟩))) e ec he (C.π_lift _)
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
  rcases C.eq_or_eq_mul hf' with h | h
  · rw [h]; exact hcomm
  · rw [h, ← mul_assoc, hcomm, mul_assoc, C.z_comm e]; group

theorem f4_pair_types : ∀ k k' : Fin 48,
    List.ofFn (Tag.F4.rootCertificate.root k) ≠ List.ofFn (Tag.F4.rootCertificate.root k') →
    List.ofFn (Tag.F4.rootCertificate.root k) ≠ List.ofFn (-Tag.F4.rootCertificate.root k') →
    let r := Tag.F4.rootCertificate.root k
    let s := Tag.F4.rootCertificate.root k'
    (f4Len r = 2 ∧ f4Len s = 2 ∧ (f4Ip r s = -1 ∨ f4Ip r s = 0 ∨ f4Ip r s = 1)) ∨
    (f4Len r = 1 ∧ f4Len s = 1 ∧ (f4Ip r s = -1 / 2 ∨ f4Ip r s = 0 ∨ f4Ip r s = 1 / 2)) ∨
    (f4Len r = 2 ∧ f4Len s = 1 ∧ (f4Ip r s = -1 ∨ f4Ip r s = 0 ∨ f4Ip r s = 1)) ∨
    (f4Len r = 1 ∧ f4Len s = 2 ∧ (f4Ip r s = -1 ∨ f4Ip r s = 0 ∨ f4Ip r s = 1)) := by
  decide +kernel

theorem liftsCommute
    {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s)
    (h1 : ¬(f4Len r = f4Len s ∧ 2 * f4Ip r s = -f4Len r))
    (h2 : ¬(f4Len r = 2 ∧ f4Len s = 1 ∧ f4Ip r s = -1))
    (h3 : ¬(f4Len r = 1 ∧ f4Len s = 2 ∧ f4Ip r s = -1)) : LiftsCommute C.π (xr r) (xr s) := by
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.mp h.1
  obtain ⟨k', rfl⟩ := isRoot_f4_iff.mp h.2.1
  have ht := f4_pair_types k k' (fun e => h.2.2.1 (List.ofFn_injective e))
    (fun e => h.2.2.2 (List.ofFn_injective e))
  have LC := fun {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s) hrs =>
    liftsCommute_xr (η := C.π) C.card C.surj C.ker_le h hrs
  rcases ht with ⟨ha, hb, hc | hc | hc⟩ | ⟨ha, hb, hc | hc | hc⟩ | ⟨ha, hb, hc | hc | hc⟩ |
      ⟨ha, hb, hc | hc | hc⟩
  · exact absurd ⟨by rw [ha, hb], by rw [hc, ha]; norm_num⟩ h1
  · exact LC h (Or.inr (Or.inl ⟨ha, hb, hc⟩))
  · exact LC h (Or.inl ⟨by rw [ha, hb], by rw [hc, ha]; norm_num⟩)
  · exact absurd ⟨by rw [ha, hb], by rw [hc, ha]; norm_num⟩ h1
  · exact liftsCommute_of_rep C.card C.surj (rootPair_of_ofFn (by decide +kernel))
      C.liftsCommute_shortOrth h (by rw [ha]; decide +kernel) (by rw [hb]; decide +kernel)
      (by rw [hc]; decide +kernel)
  · exact LC h (Or.inl ⟨by rw [ha, hb], by rw [hc, ha]; norm_num⟩)
  · exact absurd ⟨ha, hb, hc⟩ h2
  · exact LC h (Or.inr (Or.inr (Or.inr ⟨ha, hb, Or.inl hc⟩)))
  · exact LC h (Or.inr (Or.inr (Or.inr ⟨ha, hb, Or.inr hc⟩)))
  · exact absurd ⟨ha, hb, hc⟩ h3
  · exact LC h (Or.inr (Or.inr (Or.inl ⟨ha, hb, Or.inl hc⟩)))
  · exact LC h (Or.inr (Or.inr (Or.inl ⟨ha, hb, Or.inr hc⟩)))

abbrev Dec (r a b : Fin Tag.F4.rank → ℤ) : Prop :=
  IsRoot .F4 a ∧ IsRoot .F4 b ∧ a + b = r ∧ f4Len a = f4Len b ∧ 2 * f4Ip a b = -f4Len a

omit C in
theorem Dec.rootPair
    {r a b : Fin Tag.F4.rank → ℤ} (h : Dec r a b) : RootPair a b := by
  have hp := f4Len_pos h.1
  exact rootPair_of_ip h.1 h.2.1 (by linarith [h.2.2.2.2]) (by linarith [h.2.2.2.2])

omit C in
theorem xr_commutator_of_dec
    (hK : Nat.card K = 2) {r a b : Fin Tag.F4.rank → ℤ}
    (h : Dec r a b) : IsRoot .F4 r ∧ ⁅xr (K := K) a, xr (K := K) b⁆ = xr (K := K) r := by
  obtain ⟨h1, h2⟩ := xr_commutatorElement_obtuse (K := K) hK h.rootPair h.2.2.2.1 h.2.2.2.2
  rw [h.2.2.1] at h1 h2
  exact ⟨h1, h2⟩

@[expose] def cc
    (a b : Fin Tag.F4.rank → ℤ) : M := ⁅C.lift (xr a), C.lift (xr b)⁆

theorem cc_eq
    {a b : Fin Tag.F4.rank → ℤ} {e f : M} (he : C.π e = xr a) (hf : C.π f = xr b) :
    ⁅e, f⁆ = C.cc a b :=
  C.commutator_eq (he.trans (C.π_lift _).symm) (hf.trans (C.π_lift _).symm)

theorem π_cc
    {r a b : Fin Tag.F4.rank → ℤ} (h : Dec r a b) : C.π (C.cc a b) = xr r := by
  rw [cc, map_commutatorElement, C.π_lift, C.π_lift, (xr_commutator_of_dec C.card h).2]

theorem cc_swap
    {r a b : Fin Tag.F4.rank → ℤ} (h : Dec r a b) : C.cc b a = C.cc a b := by
  have h2 := C.mul_self_of_root (xr_commutator_of_dec C.card h).1 (C.π_cc h)
  rw [cc, cc, ← commutatorElement_inv, ← cc, inv_eq_of_mul_eq_one_right h2]

theorem cc_conj
    {g : adjointGroup .F4 K} {n : M} (hn : C.π n = g) {a b a' b' : Fin Tag.F4.rank → ℤ}
    (ha : g * xr a * g⁻¹ = xr a') (hb : g * xr b * g⁻¹ = xr b') :
    n * C.cc a b * n⁻¹ = C.cc a' b' := by
  rw [cc, conjugate_commutatorElement]
  exact C.cc_eq (by rw [map_mul, map_mul, map_inv, hn, C.π_lift, ha])
    (by rw [map_mul, map_mul, map_inv, hn, C.π_lift, hb])

omit C in
theorem two_eq_zero_of_card (hK : Nat.card K = 2) : (2 : K) = 0 := by
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two le_rfl (by rw [hK, pow_one])
  exact CharTwo.two_eq_zero

abbrev nX
    (i : Fin Tag.F4.rank) : adjointGroup .F4 K :=
  ⟨weylElt .F4 K i 1, weylElt_mem_adjointGroup i 1⟩

omit C in
theorem nX_conj
    (hK : Nat.card K = 2) (i : Fin Tag.F4.rank) {β : Fin Tag.F4.rank → ℤ}
    (hβ : IsRoot .F4 β) :
    nX (K := K) i * xr β * (nX i)⁻¹ = xr (reflect .F4 i β) :=
  Subtype.ext (by
    change weylElt .F4 K i 1 * pinnedX .F4 K β 1 * (weylElt .F4 K i 1)⁻¹ = _
    rw [CFSG.LieType.Ree.weylElt_conj_pinnedX_of_two_eq_zero (two_eq_zero_of_card hK) i hβ]
    rfl)

omit C in
theorem nX_eq
    (hK : Nat.card K = 2) (i : Fin Tag.F4.rank) :
    nX (K := K) i = xr (Pi.single i 1) * xr (-Pi.single i 1) * xr (Pi.single i 1) := by
  refine Subtype.ext ?_
  change weylElt .F4 K i 1 = pinnedX .F4 K _ 1 * pinnedX .F4 K _ 1 * pinnedX .F4 K _ 1
  rw [weylElt_eq_xUnit_mul, pinnedX_single, pinnedX_neg_single]
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two le_rfl (by rw [hK, pow_one])
  have : -(((1 : Kˣ)⁻¹ : Kˣ) : K) = 1 := by
    rw [inv_one, Units.val_one, CharTwo.neg_eq]
  rw [this]; rfl

theorem commute_lift_nX
    {i : Fin Tag.F4.rank} {r : Fin Tag.F4.rank → ℤ}
    (h1 : LiftsCommute C.π (xr (Pi.single i 1)) (xr r))
    (h2 : LiftsCommute C.π (xr (-Pi.single i 1)) (xr r)) {n e : M} (hn : C.π n = nX i)
    (he : C.π e = xr r) : n * e = e * n := by
  set a := C.lift (xr (K := K) (Pi.single i 1))
  set b := C.lift (xr (K := K) (-Pi.single i 1))
  have hab : C.π (a * b * a) = C.π n := by
    rw [map_mul, map_mul, C.π_lift, C.π_lift, hn, nX_eq C.card]
  have ha := h1 a e (C.π_lift _) he
  have hb := h2 b e (C.π_lift _) he
  have key : a * b * a * e = e * (a * b * a) := by
    rw [mul_assoc (a * b), ha, ← mul_assoc, mul_assoc a, hb, ← mul_assoc, ha]; group
  rcases C.eq_or_eq_mul hab with h | h
  · rw [h]; exact key
  · rw [h, mul_assoc (a * b * a), ← C.z_comm e, ← mul_assoc, key, mul_assoc]

theorem cc_reflect_of_fix
    {i : Fin Tag.F4.rank} {r₀ : Fin Tag.F4.rank → ℤ}
    (h1 : LiftsCommute C.π (xr (Pi.single i 1)) (xr r₀))
    (h2 : LiftsCommute C.π (xr (-Pi.single i 1)) (xr r₀)) {a b : Fin Tag.F4.rank → ℤ}
    (h : Dec r₀ a b) : C.cc (reflect .F4 i a) (reflect .F4 i b) = C.cc a b := by
  set n := C.lift (nX (K := K) i)
  have hc := C.cc_conj (C.π_lift (nX i)) (nX_conj C.card i h.1) (nX_conj C.card i h.2.1)
  rw [← hc, C.commute_lift_nX h1 h2 (C.π_lift _) (C.π_cc h), mul_inv_cancel_right]

omit C in
theorem dec_of_ofFn {r a b : Fin Tag.F4.rank → ℤ}
    (h : (∃ k : Fin 48, List.ofFn (Tag.F4.rootCertificate.root k) = List.ofFn a) ∧
      (∃ k : Fin 48, List.ofFn (Tag.F4.rootCertificate.root k) = List.ofFn b) ∧
      List.ofFn (a + b) = List.ofFn r ∧ f4Len a = f4Len b ∧ 2 * f4Ip a b = -f4Len a) :
    Dec r a b :=
  ⟨isRoot_of_ofFn h.1, isRoot_of_ofFn h.2.1, eq_of_ofFn h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

omit C in
theorem dec_long_cases : ∀ k k' : Fin 48,
    List.ofFn (Tag.F4.rootCertificate.root k + Tag.F4.rootCertificate.root k') =
      List.ofFn (![2, 3, 4, 2] : Fin Tag.F4.rank → ℤ) →
    f4Len (Tag.F4.rootCertificate.root k) = f4Len (Tag.F4.rootCertificate.root k') →
    2 * f4Ip (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k') =
      -f4Len (Tag.F4.rootCertificate.root k) →
    (List.ofFn (Tag.F4.rootCertificate.root k), List.ofFn (Tag.F4.rootCertificate.root k')) ∈
      [([1, 3, 4, 2], [1, 0, 0, 0]), ([1, 0, 0, 0], [1, 3, 4, 2]), ([1, 2, 4, 2], [1, 1, 0, 0]),
        ([1, 1, 0, 0], [1, 2, 4, 2]), ([1, 2, 2, 2], [1, 1, 2, 0]), ([1, 1, 2, 0], [1, 2, 2, 2]),
        ([1, 1, 2, 2], [1, 2, 2, 0]), ([1, 2, 2, 0], [1, 1, 2, 2])] := by
  decide +kernel

omit C in
theorem dec_short_cases : ∀ k k' : Fin 48,
    List.ofFn (Tag.F4.rootCertificate.root k + Tag.F4.rootCertificate.root k') =
      List.ofFn (![1, 2, 3, 2] : Fin Tag.F4.rank → ℤ) →
    f4Len (Tag.F4.rootCertificate.root k) = f4Len (Tag.F4.rootCertificate.root k') →
    2 * f4Ip (Tag.F4.rootCertificate.root k) (Tag.F4.rootCertificate.root k') =
      -f4Len (Tag.F4.rootCertificate.root k) →
    (List.ofFn (Tag.F4.rootCertificate.root k), List.ofFn (Tag.F4.rootCertificate.root k')) ∈
      [([1, 2, 3, 1], [0, 0, 0, 1]), ([0, 0, 0, 1], [1, 2, 3, 1]), ([1, 2, 2, 1], [0, 0, 1, 1]),
        ([0, 0, 1, 1], [1, 2, 2, 1]), ([1, 1, 2, 1], [0, 1, 1, 1]), ([0, 1, 1, 1], [1, 1, 2, 1]),
        ([1, 1, 1, 1], [0, 1, 2, 1]), ([0, 1, 2, 1], [1, 1, 1, 1])] := by
  decide +kernel

abbrev fi (i : ℕ) (h : i < 4 := by decide) : Fin Tag.F4.rank := ⟨i, h⟩

theorem liftsCommute_orth
    {r s : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) (hs : IsRoot .F4 s)
    (h0 : f4Ip r s = 0) : LiftsCommute C.π (xr r) (xr s) := by
  have hp := f4Len_pos hr
  refine C.liftsCommute (rootPair_of_ip hr hs (by rw [h0]; linarith) (by rw [h0]; linarith))
    (fun h' => by linarith [h'.2]) (fun h' => by linarith [h'.2.2]) (fun h' => by linarith [h'.2.2])

theorem cc_base_long
    {a b : Fin Tag.F4.rank → ℤ} (h : Dec ![2, 3, 4, 2] a b) :
    C.cc a b = C.cc ![1, 3, 4, 2] ![1, 0, 0, 0] := by
  have r0 : IsRoot .F4 (![2, 3, 4, 2] : Fin Tag.F4.rank → ℤ) := isRoot_of_ofFn (by decide +kernel)
  have hr : ∀ i : Fin Tag.F4.rank, i = fi 1 ∨ i = fi 2 →
      LiftsCommute C.π (xr (Pi.single i 1)) (xr ![2, 3, 4, 2]) ∧
        LiftsCommute C.π (xr (-Pi.single i 1)) (xr ![2, 3, 4, 2]) := by
    rintro i (rfl | rfl) <;> exact ⟨C.liftsCommute_orth (isRoot_single _ _) r0
      (by decide +kernel), C.liftsCommute_orth (IsRoot.neg (isRoot_single _ _)) r0
      (by decide +kernel)⟩
  have step : ∀ i : Fin Tag.F4.rank, i = fi 1 ∨ i = fi 2 → ∀ {a b a' b' : Fin Tag.F4.rank → ℤ},
      Dec ![2, 3, 4, 2] a b → List.ofFn (reflect .F4 i a) = List.ofFn a' →
        List.ofFn (reflect .F4 i b) = List.ofFn b' → C.cc a' b' = C.cc a b :=
    fun i hi _ _ _ _ hd ha hb => by
      rw [← eq_of_ofFn ha, ← eq_of_ofFn hb]
      exact C.cc_reflect_of_fix (hr i hi).1 (hr i hi).2 hd
  have d0 : Dec ![2, 3, 4, 2] ![1, 3, 4, 2] ![1, 0, 0, 0] := dec_of_ofFn (by decide +kernel)
  have d1 : Dec ![2, 3, 4, 2] ![1, 2, 4, 2] ![1, 1, 0, 0] := dec_of_ofFn (by decide +kernel)
  have d2 : Dec ![2, 3, 4, 2] ![1, 2, 2, 2] ![1, 1, 2, 0] := dec_of_ofFn (by decide +kernel)
  have d3 : Dec ![2, 3, 4, 2] ![1, 1, 2, 2] ![1, 2, 2, 0] := dec_of_ofFn (by decide +kernel)
  have e1 : C.cc ![1, 2, 4, 2] ![1, 1, 0, 0] = C.cc ![1, 3, 4, 2] ![1, 0, 0, 0] :=
      step (fi 1) (Or.inl rfl) d0
    (by decide +kernel) (by decide +kernel)
  have e2 : C.cc ![1, 2, 2, 2] ![1, 1, 2, 0] = C.cc ![1, 2, 4, 2] ![1, 1, 0, 0] :=
      step (fi 2) (Or.inr rfl) d1
    (by decide +kernel) (by decide +kernel)
  have e3 : C.cc ![1, 1, 2, 2] ![1, 2, 2, 0] = C.cc ![1, 2, 2, 2] ![1, 1, 2, 0] :=
      step (fi 1) (Or.inl rfl) d2
    (by decide +kernel) (by decide +kernel)
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.mp h.1
  obtain ⟨k', rfl⟩ := isRoot_f4_iff.mp h.2.1
  have hm := dec_long_cases k k' (congrArg List.ofFn h.2.2.1) h.2.2.2.1 h.2.2.2.2
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 3, 4, 2] : List ℤ) =
        List.ofFn (![1, 3, 4, 2] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 0, 0, 0] : List ℤ) =
        List.ofFn (![1, 0, 0, 0] : Fin Tag.F4.rank → ℤ)))]
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 0, 0, 0] : List ℤ) =
        List.ofFn (![1, 0, 0, 0] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 3, 4, 2] : List ℤ) =
        List.ofFn (![1, 3, 4, 2] : Fin Tag.F4.rank → ℤ)))]
    rw [C.cc_swap d0]
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 2, 4, 2] : List ℤ) =
        List.ofFn (![1, 2, 4, 2] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 1, 0, 0] : List ℤ) =
        List.ofFn (![1, 1, 0, 0] : Fin Tag.F4.rank → ℤ)))]
    exact e1
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 1, 0, 0] : List ℤ) =
        List.ofFn (![1, 1, 0, 0] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 2, 4, 2] : List ℤ) =
        List.ofFn (![1, 2, 4, 2] : Fin Tag.F4.rank → ℤ)))]
    rw [C.cc_swap d1]
    exact e1
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 2, 2, 2] : List ℤ) =
        List.ofFn (![1, 2, 2, 2] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 1, 2, 0] : List ℤ) =
        List.ofFn (![1, 1, 2, 0] : Fin Tag.F4.rank → ℤ)))]
    exact e2.trans e1
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 1, 2, 0] : List ℤ) =
        List.ofFn (![1, 1, 2, 0] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 2, 2, 2] : List ℤ) =
        List.ofFn (![1, 2, 2, 2] : Fin Tag.F4.rank → ℤ)))]
    rw [C.cc_swap d2]
    exact e2.trans e1
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 1, 2, 2] : List ℤ) =
        List.ofFn (![1, 1, 2, 2] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 2, 2, 0] : List ℤ) =
        List.ofFn (![1, 2, 2, 0] : Fin Tag.F4.rank → ℤ)))]
    exact e3.trans (e2.trans e1)
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 2, 2, 0] : List ℤ) =
        List.ofFn (![1, 2, 2, 0] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 1, 2, 2] : List ℤ) =
        List.ofFn (![1, 1, 2, 2] : Fin Tag.F4.rank → ℤ)))]
    rw [C.cc_swap d3]
    exact e3.trans (e2.trans e1)

theorem cc_base_short
    {a b : Fin Tag.F4.rank → ℤ} (h : Dec ![1, 2, 3, 2] a b) :
    C.cc a b = C.cc ![1, 2, 3, 1] ![0, 0, 0, 1] := by
  have r0 : IsRoot .F4 (![1, 2, 3, 2] : Fin Tag.F4.rank → ℤ) := isRoot_of_ofFn (by decide +kernel)
  have hr : ∀ i : Fin Tag.F4.rank, i = fi 1 ∨ i = fi 2 →
      LiftsCommute C.π (xr (Pi.single i 1)) (xr ![1, 2, 3, 2]) ∧
        LiftsCommute C.π (xr (-Pi.single i 1)) (xr ![1, 2, 3, 2]) := by
    rintro i (rfl | rfl) <;> exact ⟨C.liftsCommute_orth (isRoot_single _ _) r0
      (by decide +kernel), C.liftsCommute_orth (IsRoot.neg (isRoot_single _ _)) r0
      (by decide +kernel)⟩
  have step : ∀ i : Fin Tag.F4.rank, i = fi 1 ∨ i = fi 2 → ∀ {a b a' b' : Fin Tag.F4.rank → ℤ},
      Dec ![1, 2, 3, 2] a b → List.ofFn (reflect .F4 i a) = List.ofFn a' →
        List.ofFn (reflect .F4 i b) = List.ofFn b' → C.cc a' b' = C.cc a b :=
    fun i hi _ _ _ _ hd ha hb => by
      rw [← eq_of_ofFn ha, ← eq_of_ofFn hb]
      exact C.cc_reflect_of_fix (hr i hi).1 (hr i hi).2 hd
  have d0 : Dec ![1, 2, 3, 2] ![1, 2, 3, 1] ![0, 0, 0, 1] := dec_of_ofFn (by decide +kernel)
  have d1 : Dec ![1, 2, 3, 2] ![1, 2, 2, 1] ![0, 0, 1, 1] := dec_of_ofFn (by decide +kernel)
  have d2 : Dec ![1, 2, 3, 2] ![1, 1, 2, 1] ![0, 1, 1, 1] := dec_of_ofFn (by decide +kernel)
  have d3 : Dec ![1, 2, 3, 2] ![1, 1, 1, 1] ![0, 1, 2, 1] := dec_of_ofFn (by decide +kernel)
  have e1 : C.cc ![1, 2, 2, 1] ![0, 0, 1, 1] = C.cc ![1, 2, 3, 1] ![0, 0, 0, 1] :=
      step (fi 2) (Or.inr rfl) d0
    (by decide +kernel) (by decide +kernel)
  have e2 : C.cc ![1, 1, 2, 1] ![0, 1, 1, 1] = C.cc ![1, 2, 2, 1] ![0, 0, 1, 1] :=
      step (fi 1) (Or.inl rfl) d1
    (by decide +kernel) (by decide +kernel)
  have e3 : C.cc ![1, 1, 1, 1] ![0, 1, 2, 1] = C.cc ![1, 1, 2, 1] ![0, 1, 1, 1] :=
      step (fi 2) (Or.inr rfl) d2
    (by decide +kernel) (by decide +kernel)
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.mp h.1
  obtain ⟨k', rfl⟩ := isRoot_f4_iff.mp h.2.1
  have hm := dec_short_cases k k' (congrArg List.ofFn h.2.2.1) h.2.2.2.1 h.2.2.2.2
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ |
    ⟨ha, hb⟩
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 2, 3, 1] : List ℤ) =
        List.ofFn (![1, 2, 3, 1] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([0, 0, 0, 1] : List ℤ) =
        List.ofFn (![0, 0, 0, 1] : Fin Tag.F4.rank → ℤ)))]
  · rw [eq_of_ofFn (ha.trans (by rfl : ([0, 0, 0, 1] : List ℤ) =
        List.ofFn (![0, 0, 0, 1] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 2, 3, 1] : List ℤ) =
        List.ofFn (![1, 2, 3, 1] : Fin Tag.F4.rank → ℤ)))]
    rw [C.cc_swap d0]
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 2, 2, 1] : List ℤ) =
        List.ofFn (![1, 2, 2, 1] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([0, 0, 1, 1] : List ℤ) =
        List.ofFn (![0, 0, 1, 1] : Fin Tag.F4.rank → ℤ)))]
    exact e1
  · rw [eq_of_ofFn (ha.trans (by rfl : ([0, 0, 1, 1] : List ℤ) =
        List.ofFn (![0, 0, 1, 1] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 2, 2, 1] : List ℤ) =
        List.ofFn (![1, 2, 2, 1] : Fin Tag.F4.rank → ℤ)))]
    rw [C.cc_swap d1]
    exact e1
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 1, 2, 1] : List ℤ) =
        List.ofFn (![1, 1, 2, 1] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([0, 1, 1, 1] : List ℤ) =
        List.ofFn (![0, 1, 1, 1] : Fin Tag.F4.rank → ℤ)))]
    exact e2.trans e1
  · rw [eq_of_ofFn (ha.trans (by rfl : ([0, 1, 1, 1] : List ℤ) =
        List.ofFn (![0, 1, 1, 1] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 1, 2, 1] : List ℤ) =
        List.ofFn (![1, 1, 2, 1] : Fin Tag.F4.rank → ℤ)))]
    rw [C.cc_swap d2]
    exact e2.trans e1
  · rw [eq_of_ofFn (ha.trans (by rfl : ([1, 1, 1, 1] : List ℤ) =
        List.ofFn (![1, 1, 1, 1] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([0, 1, 2, 1] : List ℤ) =
        List.ofFn (![0, 1, 2, 1] : Fin Tag.F4.rank → ℤ)))]
    exact e3.trans (e2.trans e1)
  · rw [eq_of_ofFn (ha.trans (by rfl : ([0, 1, 2, 1] : List ℤ) =
        List.ofFn (![0, 1, 2, 1] : Fin Tag.F4.rank → ℤ))),
      eq_of_ofFn (hb.trans (by rfl : ([1, 1, 1, 1] : List ℤ) =
        List.ofFn (![1, 1, 1, 1] : Fin Tag.F4.rank → ℤ)))]
    rw [C.cc_swap d3]
    exact e3.trans (e2.trans e1)

omit C in
theorem reflect_add'
    (i : Fin Tag.F4.rank) (u v : Fin Tag.F4.rank → ℤ) :
    reflect .F4 i (u + v) = reflect .F4 i u + reflect .F4 i v := by
  rw [← simple_smul, ← simple_smul, ← simple_smul, smul_add]

omit C in
theorem f4Ip_reflect
    (i : Fin Tag.F4.rank) (u v : Fin Tag.F4.rank → ℤ) :
    f4Ip (reflect .F4 i u) (reflect .F4 i v) = f4Ip u v := by
  rw [← simple_smul, ← simple_smul]
  exact f4Euclid_smul_dotProduct _ u v

omit C in
theorem Dec.reflect'
    {r a b : Fin Tag.F4.rank → ℤ} (h : Dec r a b) (i : Fin Tag.F4.rank) :
    Dec (reflect .F4 i r) (reflect .F4 i a) (reflect .F4 i b) := by
  refine ⟨IsRoot.reflect i h.1, IsRoot.reflect i h.2.1, by rw [← reflect_add', h.2.2.1], ?_, ?_⟩
  · change f4Ip _ _ = f4Ip _ _
    rw [f4Ip_reflect, f4Ip_reflect]; exact h.2.2.2.1
  · change 2 * f4Ip _ _ = -f4Ip _ _
    rw [f4Ip_reflect, f4Ip_reflect]; exact h.2.2.2.2

omit C in
theorem Dec.of_reflect
    {r a b : Fin Tag.F4.rank → ℤ} {i : Fin Tag.F4.rank}
    (h : Dec (reflect .F4 i r) a b) : Dec r (reflect .F4 i a) (reflect .F4 i b) := by
  have := h.reflect' i
  rwa [reflect_reflect] at this

@[expose] def Indep
    (r : Fin Tag.F4.rank → ℤ) : Prop :=
  ∀ a b a' b', Dec r a b → Dec r a' b' → C.cc a b = C.cc a' b'

theorem indep_reflect
    {r : Fin Tag.F4.rank → ℤ} (hr : C.Indep r) (i : Fin Tag.F4.rank) :
    C.Indep (reflect .F4 i r) := by
  intro a b a' b' h h'
  have e := hr _ _ _ _ h.of_reflect h'.of_reflect
  have conj : ∀ {u v : Fin Tag.F4.rank → ℤ}, Dec (reflect .F4 i r) u v →
      C.lift (nX i) * C.cc (reflect .F4 i u) (reflect .F4 i v) * (C.lift (nX i))⁻¹ =
        C.cc u v := fun {u v} hd => by
    refine C.cc_conj (C.π_lift _) ?_ ?_
    · rw [nX_conj C.card i hd.of_reflect.1, reflect_reflect]
    · rw [nX_conj C.card i hd.of_reflect.2.1, reflect_reflect]
  rw [← conj h, ← conj h', e]

theorem indep_base_long
    : C.Indep ![2, 3, 4, 2] := fun _ _ _ _ h h' =>
  (C.cc_base_long h).trans (C.cc_base_long h').symm

theorem indep_base_short
    : C.Indep ![1, 2, 3, 2] := fun _ _ _ _ h h' =>
  (C.cc_base_short h).trans (C.cc_base_short h').symm

abbrev applyWord (w : List (Fin Tag.F4.rank)) (r : Fin Tag.F4.rank → ℤ) : Fin Tag.F4.rank → ℤ :=
  w.foldl (fun v i => reflect .F4 i v) r

theorem indep_word
    : ∀ (w : List (Fin Tag.F4.rank)) {r : Fin Tag.F4.rank → ℤ}, C.Indep r →
    C.Indep (applyWord w r)
  | [], _, h => h
  | i :: w, _, h => indep_word w (C.indep_reflect h i)

omit C in
theorem exists_dec_word :
    ∀ (w : List (Fin Tag.F4.rank)) {r : Fin Tag.F4.rank → ℤ},
    (∃ a b, Dec r a b) → ∃ a b, Dec (applyWord w r) a b
  | [], _, h => h
  | i :: w, _, ⟨_, _, h⟩ => exists_dec_word w ⟨_, _, h.reflect' i⟩

theorem word_simple :
    List.ofFn (applyWord [fi 0, fi 1, fi 2, fi 1, fi 3, fi 2, fi 1] ![2, 3, 4, 2]) =
        List.ofFn (Pi.single (fi 0) 1 : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (applyWord [fi 0, fi 1, fi 2, fi 1, fi 0, fi 3, fi 2] ![2, 3, 4, 2]) =
        List.ofFn (Pi.single (fi 1) 1 : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (applyWord [fi 3, fi 2, fi 1, fi 0, fi 2, fi 1, fi 3] ![1, 2, 3, 2]) =
        List.ofFn (Pi.single (fi 2) 1 : Fin Tag.F4.rank → ℤ) ∧
    List.ofFn (applyWord [fi 3, fi 2, fi 1, fi 0, fi 2, fi 1, fi 2] ![1, 2, 3, 2]) =
        List.ofFn (Pi.single (fi 3) 1 : Fin Tag.F4.rank → ℤ) := by
  decide +kernel

omit C in
theorem exists_dec :
    ∀ r, IsRoot .F4 r → ∃ a b, Dec r a b := by
  have hL : ∃ a b, Dec ![2, 3, 4, 2] a b := ⟨_, _, dec_of_ofFn (r := ![2, 3, 4, 2])
    (a := ![1, 3, 4, 2]) (b := ![1, 0, 0, 0]) (by decide +kernel)⟩
  have hS : ∃ a b, Dec ![1, 2, 3, 2] a b := ⟨_, _, dec_of_ofFn (r := ![1, 2, 3, 2])
    (a := ![1, 2, 3, 1]) (b := ![0, 0, 0, 1]) (by decide +kernel)⟩
  obtain ⟨w1, w2, w3, w4⟩ := word_simple
  intro r hr
  induction hr with
  | basis j =>
    match j with
    | ⟨0, _⟩ => rw [← eq_of_ofFn w1]; exact exists_dec_word _ hL
    | ⟨1, _⟩ => rw [← eq_of_ofFn w2]; exact exists_dec_word _ hL
    | ⟨2, _⟩ => rw [← eq_of_ofFn w3]; exact exists_dec_word _ hS
    | ⟨3, _⟩ => rw [← eq_of_ofFn w4]; exact exists_dec_word _ hS
  | reflect i _ ih => obtain ⟨a, b, h⟩ := ih; exact ⟨_, _, h.reflect' i⟩

theorem indep_all
    : ∀ r, IsRoot .F4 r → C.Indep r := by
  obtain ⟨w1, w2, w3, w4⟩ := word_simple
  intro r hr
  induction hr with
  | basis j =>
    match j with
    | ⟨0, _⟩ => rw [← eq_of_ofFn w1]; exact C.indep_word _ C.indep_base_long
    | ⟨1, _⟩ => rw [← eq_of_ofFn w2]; exact C.indep_word _ C.indep_base_long
    | ⟨2, _⟩ => rw [← eq_of_ofFn w3]; exact C.indep_word _ C.indep_base_short
    | ⟨3, _⟩ => rw [← eq_of_ofFn w4]; exact C.indep_word _ C.indep_base_short
  | reflect i _ ih => exact C.indep_reflect ih i

@[expose] def yhat
    (r : Fin Tag.F4.rank → ℤ) : M :=
  haveI := Classical.propDecidable (IsRoot .F4 r)
  if h : IsRoot .F4 r then C.cc (exists_dec r h).choose (exists_dec r h).choose_spec.choose else 1

theorem yhat_eq
    {r a b : Fin Tag.F4.rank → ℤ} (h : Dec r a b) : C.yhat r = C.cc a b := by
  have hr := (xr_commutator_of_dec C.card h).1
  rw [yhat]
  simp only [hr, ↓reduceDIte]
  exact C.indep_all r hr _ _ _ _ (exists_dec r hr).choose_spec.choose_spec h

theorem π_yhat
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) : C.π (C.yhat r) = xr r := by
  obtain ⟨a, b, h⟩ := exists_dec r hr
  rw [C.yhat_eq h, C.π_cc h]

theorem yhat_mul_self
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    C.yhat r * C.yhat r = 1 :=
  C.mul_self_of_root hr (C.π_yhat hr)

theorem yhat_inv
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) : (C.yhat r)⁻¹ = C.yhat r :=
  inv_eq_of_mul_eq_one_right (C.yhat_mul_self hr)

theorem commutator_yhat_of_dec
    {r a b : Fin Tag.F4.rank → ℤ} (h : Dec r a b) :
    ⁅C.yhat a, C.yhat b⁆ = C.yhat r := by
  rw [C.cc_eq (C.π_yhat h.1) (C.π_yhat h.2.1), C.yhat_eq h]

theorem commute_yhat
    {r s : Fin Tag.F4.rank → ℤ} (h : RootPair r s)
    (h1 : ¬(f4Len r = f4Len s ∧ 2 * f4Ip r s = -f4Len r))
    (h2 : ¬(f4Len r = 2 ∧ f4Len s = 1 ∧ f4Ip r s = -1))
    (h3 : ¬(f4Len r = 1 ∧ f4Len s = 2 ∧ f4Ip r s = -1)) :
    C.yhat r * C.yhat s = C.yhat s * C.yhat r :=
  C.liftsCommute h h1 h2 h3 _ _ (C.π_yhat h.1) (C.π_yhat h.2.1)

omit C in
theorem Dec.smul
    {r a b : Fin Tag.F4.rank → ℤ} (h : Dec r a b) (w : WeylGroup .F4) :
    Dec (w • r) (w • a) (w • b) := by
  refine ⟨CFSG.LieType.Chevalley.IsRoot.smul h.1 w, CFSG.LieType.Chevalley.IsRoot.smul h.2.1 w,
    by rw [← smul_add, h.2.2.1], ?_, ?_⟩
  · change f4Ip _ _ = f4Ip _ _
    rw [f4Ip, f4Ip, f4Euclid_smul_dotProduct, f4Euclid_smul_dotProduct]; exact h.2.2.2.1
  · change 2 * f4Ip _ _ = -f4Ip _ _
    rw [f4Ip, f4Ip, f4Euclid_smul_dotProduct, f4Euclid_smul_dotProduct]; exact h.2.2.2.2

theorem conj_yhat
    {g : adjointGroup .F4 K} {w : WeylGroup .F4}
    (hg : ∀ t, IsRoot .F4 t → g * xr t * g⁻¹ = xr (w • t)) {n : M} (hn : C.π n = g)
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) : n * C.yhat r * n⁻¹ = C.yhat (w • r) := by
  obtain ⟨a, b, h⟩ := exists_dec r hr
  rw [C.yhat_eq h, C.cc_conj hn (hg a h.1) (hg b h.2.1), C.yhat_eq (h.smul w)]

omit C in
theorem nX_conj_smul
    (hK : Nat.card K = 2) (i : Fin Tag.F4.rank) (t : Fin Tag.F4.rank → ℤ)
    (ht : IsRoot .F4 t) : nX (K := K) i * xr t * (nX i)⁻¹ = xr (simple .F4 i • t) := by
  rw [simple_smul]; exact nX_conj hK i ht

theorem conj_yhat_nX
    (i : Fin Tag.F4.rank) {n : M} (hn : C.π n = nX i)
    {r : Fin Tag.F4.rank → ℤ} (hr : IsRoot .F4 r) :
    n * C.yhat r * n⁻¹ = C.yhat (reflect .F4 i r) := by
  rw [C.conj_yhat (nX_conj_smul C.card i) hn hr, simple_smul]

abbrev Mixed (a b : Fin Tag.F4.rank → ℤ) : Prop :=
  IsRoot .F4 a ∧ IsRoot .F4 b ∧ f4Len a = 2 ∧ f4Len b = 1 ∧ f4Ip a b = -1

omit C in
theorem Mixed.rootPair {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) : RootPair a b :=
  rootPair_of_len_ne h.1 h.2.1 (by rw [h.2.2.1, h.2.2.2.1]; norm_num)

omit C in
theorem xr_commutator_of_mixed
    (hK : Nat.card K = 2) {a b : Fin Tag.F4.rank → ℤ}
    (h : Mixed a b) : IsRoot .F4 (a + b) ∧ IsRoot .F4 (a + 2 • b) ∧
      ⁅xr (K := K) a, xr (K := K) b⁆ = xr (K := K) (a + b) * xr (K := K) (a + 2 • b) := by
  obtain ⟨h1, h2, -, -, h5, -⟩ :=
    xr_commutatorElement_mixed (K := K) hK h.rootPair h.2.2.1 h.2.2.2.1 h.2.2.2.2
  exact ⟨h1, h2, h5⟩

@[expose] def twist
    (a b : Fin Tag.F4.rank → ℤ) : M :=
  (C.yhat (a + b) * C.yhat (a + 2 • b))⁻¹ * ⁅C.yhat a, C.yhat b⁆

theorem π_twist
    {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) : C.π (C.twist a b) = 1 := by
  obtain ⟨h1, h2, h3⟩ := xr_commutator_of_mixed C.card h
  rw [twist, map_mul, map_inv, map_mul, map_commutatorElement, C.π_yhat h.1, C.π_yhat h.2.1,
    C.π_yhat h1, C.π_yhat h2, h3, inv_mul_cancel]

theorem twist_mem_center
    {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) :
    C.twist a b ∈ center M := C.ker_le (C.π_twist h)

omit C in
theorem Mixed.smul
    {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) (w : WeylGroup .F4) :
    Mixed (w • a) (w • b) := by
  refine ⟨CFSG.LieType.Chevalley.IsRoot.smul h.1 w, CFSG.LieType.Chevalley.IsRoot.smul h.2.1 w,
    ?_, ?_, ?_⟩ <;> simp only [f4Len, f4Ip, f4Euclid_smul_dotProduct]
  exacts [h.2.2.1, h.2.2.2.1, h.2.2.2.2]

theorem twist_smul
    {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) {g : adjointGroup .F4 K}
    {w : WeylGroup .F4} (hg : ∀ t, IsRoot .F4 t → g * xr t * g⁻¹ = xr (w • t)) :
    C.twist (w • a) (w • b) = C.twist a b := by
  obtain ⟨h1, h2, -⟩ := xr_commutator_of_mixed C.card h
  set n := C.lift g
  have hn : C.π n = g := C.π_lift g
  have e : n * C.twist a b * n⁻¹ = C.twist (w • a) (w • b) := by
    rw [twist, twist, show n * ((C.yhat (a + b) * C.yhat (a + 2 • b))⁻¹ * ⁅C.yhat a, C.yhat b⁆) *
        n⁻¹ = ((n * C.yhat (a + b) * n⁻¹) * (n * C.yhat (a + 2 • b) * n⁻¹))⁻¹ *
          ⁅n * C.yhat a * n⁻¹, n * C.yhat b * n⁻¹⁆ by simp only [commutatorElement_def]; group,
      C.conj_yhat hg hn h1, C.conj_yhat hg hn h2, C.conj_yhat hg hn h.1, C.conj_yhat hg hn h.2.1,
      smul_add, smul_add, two_nsmul, two_nsmul, smul_add]
  rw [← e, mem_center_iff.1 (C.twist_mem_center h) n, mul_inv_cancel_right]

theorem twist_eq_twist
    {a b a' b' : Fin Tag.F4.rank → ℤ} (h : Mixed a b) (h' : Mixed a' b') :
    C.twist a' b' = C.twist a b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htrans, -⟩ := f4_field_two_root_pair_relations C.card
  have hrp := h.rootPair
  have hrp' := h'.rootPair
  obtain ⟨w, hwa, hwb, g, hg, hgt⟩ := htrans a b a' b' h.1 h.2.1 h'.1 h'.2.1 hrp.2.2.1 hrp.2.2.2
    hrp'.2.2.1 hrp'.2.2.2 (by change f4Len a = f4Len a'; rw [h.2.2.1, h'.2.2.1])
    (by change f4Len b = f4Len b'; rw [h.2.2.2.1, h'.2.2.2.1])
    (by change f4Ip a b = f4Ip a' b'; rw [h.2.2.2.2, h'.2.2.2.2])
  rw [← hwa, ← hwb]
  exact C.twist_smul (g := ⟨g, hg⟩) h fun t ht => Subtype.ext (hgt t ht)

omit C in
@[expose] def cl (α β : Fin Tag.F4.rank → ℤ) : List (Fin Tag.F4.rank → ℤ) :=
  if f4Len α = f4Len β ∧ 2 * f4Ip α β = -f4Len α then [α + β]
  else if f4Len α = 2 ∧ f4Len β = 1 ∧ f4Ip α β = -1 then [α + β, α + 2 • β]
  else if f4Len α = 1 ∧ f4Len β = 2 ∧ f4Ip α β = -1 then [β + α, β + 2 • α]
  else []

omit C in
theorem rootPair_of_pos {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hαp : 0 < height α)
    (hβ : IsRoot .F4 β) (hβp : 0 < height β) (hne : α ≠ β) : RootPair α β := by
  refine ⟨hα, hβ, hne, fun h => ?_⟩
  have : height α = -height β := by rw [h]; simp [height]
  omega

omit C in
theorem cl_spec
    (hK : Nat.card K = 2) {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α)
    (hαp : 0 < height α) (hβ : IsRoot .F4 β) (hβp : 0 < height β) (hne : α ≠ β) :
    ∀ γ ∈ cl α β, IsRoot .F4 γ ∧ height α < height γ ∧ height β < height γ := by
  intro γ hγ
  have h := rootPair_of_pos hα hαp hβ hβp hne
  by_cases c1 : f4Len α = f4Len β ∧ 2 * f4Ip α β = -f4Len α
  · simp only [cl, ite_eq_left c1, List.mem_singleton] at hγ
    subst hγ
    refine ⟨(xr_commutatorElement_obtuse (K := K) hK h c1.1 c1.2).1, ?_, ?_⟩ <;>
      rw [height_add] <;> omega
  · by_cases c2 : f4Len α = 2 ∧ f4Len β = 1 ∧ f4Ip α β = -1
    · simp only [cl, ite_eq_right c1, ite_eq_left c2, List.mem_cons, List.not_mem_nil,
        or_false] at hγ
      obtain ⟨h1, h2, -⟩ := xr_commutator_of_mixed (K := K) hK ⟨hα, hβ, c2⟩
      rcases hγ with rfl | rfl
      · exact ⟨h1, by rw [height_add]; omega, by rw [height_add]; omega⟩
      · exact ⟨h2, by rw [height_two_nsmul_add]; omega, by rw [height_two_nsmul_add]; omega⟩
    · by_cases c3 : f4Len α = 1 ∧ f4Len β = 2 ∧ f4Ip α β = -1
      · simp only [cl, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3, List.mem_cons,
          List.not_mem_nil, or_false] at hγ
        obtain ⟨h1, h2, -⟩ := xr_commutator_of_mixed (K := K) hK
          ⟨hβ, hα, c3.2.1, c3.1, by rw [f4Ip_comm]; exact c3.2.2⟩
        rcases hγ with rfl | rfl
        · exact ⟨h1, by rw [height_add]; omega, by rw [height_add]; omega⟩
        · exact ⟨h2, by rw [height_two_nsmul_add]; omega, by rw [height_two_nsmul_add]; omega⟩
      · simp only [cl, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, List.not_mem_nil] at hγ

omit C in
theorem mixed_sum_facts
    (hK : Nat.card K = 2) {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) :
    RootPair (a + b) (a + 2 • b) ∧ f4Len (a + b) = 1 ∧ f4Len (a + 2 • b) = 2 ∧
      f4Ip (a + b) (a + 2 • b) = 1 := by
  obtain ⟨h1, h2, -, -, -, -⟩ := xr_commutatorElement_mixed (K := K) hK h.rootPair h.2.2.1
    h.2.2.2.1 h.2.2.2.2
  have hAA : f4Ip a a = 2 := h.2.2.1
  have hBB : f4Ip b b = 1 := h.2.2.2.1
  have hab := h.2.2.2.2
  have hba : f4Ip b a = -1 := by rw [f4Ip_comm]; exact hab
  have l1 : f4Len (a + b) = 1 := by
    rw [f4Len_add]; change f4Ip a a + 2 * f4Ip a b + f4Ip b b = 1; rw [hAA, hab, hBB]; norm_num
  have l2 : f4Len (a + 2 • b) = 2 := by
    rw [f4Len_add, f4Ip_two_nsmul_right]
    change f4Ip a a + 2 * (2 * f4Ip a b) + f4Ip (2 • b) (2 • b) = 2
    rw [f4Ip_two_nsmul_left, f4Ip_two_nsmul_right, hAA, hab, hBB]; norm_num
  have i3 : f4Ip (a + b) (a + 2 • b) = 1 := by
    rw [f4Ip_add_left, f4Ip_add_right, f4Ip_add_right, f4Ip_two_nsmul_right,
      f4Ip_two_nsmul_right, hAA, hab, hba, hBB]; norm_num
  exact ⟨rootPair_of_len_ne h1 h2 (by rw [l1, l2]; norm_num), l1, l2, i3⟩

theorem mixed_sum_commute
    {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) :
    C.yhat (a + b) * C.yhat (a + 2 • b) = C.yhat (a + 2 • b) * C.yhat (a + b) := by
  obtain ⟨hr, l1, l2, i3⟩ := mixed_sum_facts (K := K) C.card h
  refine C.commute_yhat hr (fun h' => ?_) (fun h' => ?_) (fun h' => ?_)
  · rw [l1, l2] at h'; norm_num at h'
  · rw [l1] at h'; norm_num at h'
  · rw [i3] at h'; norm_num at h'

theorem commutator_yhat_mixed
    (a b : Fin Tag.F4.rank → ℤ) :
    ⁅C.yhat a, C.yhat b⁆ = C.yhat (a + b) * C.yhat (a + 2 • b) * C.twist a b := by
  rw [twist, mul_inv_cancel_left]

theorem commutator_yhat_mixed'
    {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) :
    ⁅C.yhat b, C.yhat a⁆ = C.yhat (a + b) * C.yhat (a + 2 • b) * C.twist a b := by
  obtain ⟨h1, h2, -⟩ := xr_commutator_of_mixed C.card h
  have hc := C.mixed_sum_commute h
  rw [← commutatorElement_inv, C.commutator_yhat_mixed a b, mul_inv_rev, mul_inv_rev,
    C.yhat_inv h1, C.yhat_inv h2, ← hc, ← mem_center_iff.1 (inv_mem (C.twist_mem_center h))]
  congr 1
  rcases (C.ker_iff _).1 (C.π_twist h) with e | e
  · rw [e, inv_one]
  · rw [e, inv_eq_of_mul_eq_one_right C.z_mul_z]

theorem commutator_yhat_pos
    (htw : ∀ a b, Mixed a b → C.twist a b = 1)
    {α β : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) (hαp : 0 < height α) (hβ : IsRoot .F4 β)
    (hβp : 0 < height β) (hne : α ≠ β) : ⁅C.yhat α, C.yhat β⁆ = ((cl α β).map C.yhat).prod := by
  have h := rootPair_of_pos hα hαp hβ hβp hne
  by_cases c1 : f4Len α = f4Len β ∧ 2 * f4Ip α β = -f4Len α
  · simp only [cl, ite_eq_left c1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one]
    exact C.commutator_yhat_of_dec ⟨hα, hβ, rfl, c1⟩
  · by_cases c2 : f4Len α = 2 ∧ f4Len β = 1 ∧ f4Ip α β = -1
    · simp only [cl, ite_eq_right c1, ite_eq_left c2, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      rw [C.commutator_yhat_mixed, htw α β ⟨hα, hβ, c2⟩, mul_one]
    · by_cases c3 : f4Len α = 1 ∧ f4Len β = 2 ∧ f4Ip α β = -1
      · simp only [cl, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        have hm : Mixed β α := ⟨hβ, hα, c3.2.1, c3.1, by rw [f4Ip_comm]; exact c3.2.2⟩
        rw [C.commutator_yhat_mixed' hm, htw β α hm, mul_one]
      · simp only [cl, ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, List.map_nil,
          List.prod_nil]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (C.commute_yhat h c1 c2 c3)

theorem twist_eq_z
    [Finite M] [Group.IsPerfect M] {a b : Fin Tag.F4.rank → ℤ} (h : Mixed a b) :
    C.twist a b = C.z := by
  by_contra hne
  have htw : ∀ a' b', Mixed a' b' → C.twist a' b' = 1 := fun a' b' h' => by
    rw [C.twist_eq_twist h h']
    rcases (C.ker_iff _).1 (C.π_twist h) with e | e
    · exact e
    · exact absurd e hne
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [C.card]; norm_num)
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two le_rfl (by rw [C.card, pow_one])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcount := card_closure_le_of_posRoots_list C.yhat (fun α hα _ => C.yhat_mul_self hα) cl
    (fun α β hα hαp hβ hβp hne => cl_spec C.card hα hαp hβ hβp hne)
    (fun α β hα hαp hβ hβp hne => C.commutator_yhat_pos htw hα hαp hβ hβp hne)
  set P₀ := closure {g | ∃ α, IsRoot .F4 α ∧ 0 < height α ∧ C.yhat α = g} with hP₀
  have hmap : P₀.map C.π =
      closure {g | ∃ α, IsRoot .F4 α ∧ 0 < height α ∧ xr (K := K) α = g} := by
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨α, hα, hαp, rfl⟩, rfl⟩
      exact ⟨α, hα, hαp, (C.π_yhat hα).symm⟩
    · rintro ⟨α, hα, hαp, rfl⟩
      exact ⟨C.yhat α, ⟨α, hα, hαp, rfl⟩, C.π_yhat hα⟩
  have := finite_modGL (τ := .F4) (K := K)
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 (posUnipotent_le_adjointGroup (K := K))
    (card_posUnipotent (τ := .F4) (K := K))
  set S := hUp.toSylow hUi with hS
  have hSle : (S : Subgroup (adjointGroup .F4 K)) ≤ P₀.map C.π := by
    rw [hmap]
    exact posUnipotent_le_closure_xr C.card
  have hcardS : Nat.card (S : Subgroup (adjointGroup .F4 K)) =
      2 ^ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α}.ncard := by
    rw [hS, IsPGroup.toSylow_coe, card_subgroupOf_of_le (posUnipotent_le_adjointGroup (K := K)),
      card_posUnipotent, C.card]
  have : Finite (P₀.map C.π) := Finite.of_surjective _ (C.π.subgroupMap_surjective P₀)
  have hbij : Function.Bijective (C.π.subgroupMap P₀) := by
    refine (C.π.subgroupMap_surjective P₀).bijective_of_nat_card_le ?_
    calc Nat.card P₀ ≤ 2 ^ {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α}.ncard := hcount
      _ = Nat.card (S : Subgroup (adjointGroup .F4 K)) := hcardS.symm
      _ ≤ Nat.card (P₀.map C.π) := Subgroup.card_le_of_le hSle
  have hinj : ∀ x ∈ P₀, C.π x = 1 → x = 1 := by
    intro x hx hx1
    have h' : C.π.subgroupMap P₀ ⟨x, hx⟩ = C.π.subgroupMap P₀ 1 :=
      Subtype.ext (by rw [map_one]; exact hx1)
    exact congrArg Subtype.val (hbij.1 h')
  have h2 : IsPGroup 2 C.π.ker := by
    rintro ⟨x, hx⟩
    refine ⟨1, Subtype.ext ?_⟩
    rcases (C.ker_iff x).1 hx with e | e
    · simp [e]
    · simp [e, pow_two, C.z_mul_z]
  have hbot := LinearCover.ker_eq_bot_of_sylow_le_map C.π C.surj C.ker_le h2 S P₀ hSle hinj
  have hz : C.z ∈ C.π.ker := C.π_z
  rw [hbot, mem_bot] at hz
  exact C.z_ne hz

theorem commutator_yhat_mixed_z
    [Finite M] [Group.IsPerfect M] {a b : Fin Tag.F4.rank → ℤ}
    (h : Mixed a b) : ⁅C.yhat a, C.yhat b⁆ = C.yhat (a + b) * C.yhat (a + 2 • b) * C.z ∧
      ⁅C.yhat b, C.yhat a⁆ = C.yhat (a + b) * C.yhat (a + 2 • b) * C.z := by
  rw [← C.twist_eq_z h]
  exact ⟨C.commutator_yhat_mixed a b, C.commutator_yhat_mixed' h⟩

theorem yhat_graph
    {β : M →* M} {φ : adjointGroup .F4 K →* adjointGroup .F4 K}
    (hβ : ∀ m, C.π (β m) = φ (C.π m)) {Ψ : (Fin Tag.F4.rank → ℤ) → Fin Tag.F4.rank → ℤ}
    (hφ : ∀ t, IsRoot .F4 t → φ (xr t) = xr (Ψ t)) {r a b : Fin Tag.F4.rank → ℤ} (h : Dec r a b)
    (h' : Dec (Ψ r) (Ψ a) (Ψ b)) : β (C.yhat r) = C.yhat (Ψ r) := by
  rw [C.yhat_eq h, cc, map_commutatorElement, C.yhat_eq h']
  exact C.cc_eq (by rw [hβ, C.π_lift, hφ a h.1]) (by rw [hβ, C.π_lift, hφ b h.2.1])

end Cover

end CFSG.EvenSmallLie.FFourTwo
