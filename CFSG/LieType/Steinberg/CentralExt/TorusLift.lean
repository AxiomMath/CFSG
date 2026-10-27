module

public import CFSG.LieType.Steinberg.CentralExt.AlternatingPairing
public import CFSG.LieType.Steinberg.PartBRankOne

public section

open scoped commutatorElement

namespace CFSG.LieType.Steinberg.CentralExt.TorusLift

abbrev centerCommGroup (E : Type*) [Group E] : CommGroup (Subgroup.center E) :=
  { (inferInstance : Group (Subgroup.center E)) with
    mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.1 b.2) a) }

attribute [local instance] centerCommGroup

variable {E K : Type*} [Group E] [Group K] {π : E →* K}

theorem commutatorElement_mul_central_left {z : E} (hz : z ∈ Subgroup.center E) (a b : E) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : z * b * z⁻¹ = b := by
    rw [← (Subgroup.mem_center_iff.1 hz) b, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

theorem commutatorElement_mul_central_right {z : E} (hz : z ∈ Subgroup.center E) (a b : E) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h : z * a⁻¹ * z⁻¹ = a⁻¹ := by
    rw [← (Subgroup.mem_center_iff.1 hz) a⁻¹, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

variable (hcen : π.ker ≤ Subgroup.center E)
include hcen

theorem commutatorElement_eq_of_map_eq {a a' b b' : E} (ha : π a = π a') (hb : π b = π b') :
    ⁅a, b⁆ = ⁅a', b'⁆ := by
  have hz : a⁻¹ * a' ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, ha, inv_mul_cancel]
  have hw : b⁻¹ * b' ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hb, inv_mul_cancel]
  calc ⁅a, b⁆ = ⁅a * (a⁻¹ * a'), b * (b⁻¹ * b')⁆ := by
        rw [commutatorElement_mul_central_left (hcen hz),
          commutatorElement_mul_central_right (hcen hw)]
    _ = ⁅a', b'⁆ := by rw [mul_inv_cancel_left, mul_inv_cancel_left]

theorem conj_eq_of_map_eq {g g' : E} (hg : π g = π g') (a : E) : g * a * g⁻¹ = g' * a * g'⁻¹ := by
  have hz : g⁻¹ * g' ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hg, inv_mul_cancel]
  have hc := (Subgroup.mem_center_iff.1 (hcen hz)) a
  calc g * a * g⁻¹ = g * (a * (g⁻¹ * g')) * (g⁻¹ * g')⁻¹ * g⁻¹ := by group
    _ = g * ((g⁻¹ * g') * a) * (g⁻¹ * g')⁻¹ * g⁻¹ := by rw [hc]
    _ = g' * a * g'⁻¹ := by group

omit hcen in
theorem commutatorElement_mul_left_of_central {a b c : E} (h : ⁅b, c⁆ ∈ Subgroup.center E) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have e : ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, (Subgroup.mem_center_iff.1 h) a, mul_assoc ⁅b, c⁆, mul_inv_cancel, mul_one]
  exact ((Subgroup.mem_center_iff.1 h) ⁅a, c⁆).symm

omit hcen in
theorem commutatorElement_mul_right_of_central {a b c : E} (h : ⁅a, c⁆ ∈ Subgroup.center E) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have e : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, (Subgroup.mem_center_iff.1 h) b]
  group

variable (hπ : Function.Surjective π)

@[expose] noncomputable def lift (g : K) : E := (hπ g).choose

omit hcen in
theorem map_lift (g : K) : π (lift hπ g) = g := (hπ g).choose_spec

section RootGroup

variable {k : Type*} [Field k] {x : k → K} (hx : ∀ s t, x (s + t) = x s * x t)
include hx

omit hcen hπ in
theorem commute_x (s t : k) : x s * x t = x t * x s := by rw [← hx, ← hx, add_comm]

omit hcen hπ in
theorem x_zero : x 0 = 1 := by
  have h := hx 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

omit hcen hπ in
theorem x_neg (s : k) : x (-s) = (x s)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hx, neg_add_cancel, x_zero hx]

omit hcen in
theorem commLift_mem_ker (s t : k) : ⁅lift hπ (x s), lift hπ (x t)⁆ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement, map_lift, map_lift,
    commutatorElement_eq_one_iff_mul_comm]
  exact commute_x hx s t

@[expose] noncomputable def commPairing : k →+ k →+ Additive (Subgroup.center E) :=
  AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun t => Additive.ofMul
      ⟨⁅lift hπ (x s), lift hπ (x t)⁆, hcen (commLift_mem_ker hπ hx s t)⟩) fun t t' => by
    rw [← ofMul_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [commutatorElement_eq_of_map_eq hcen rfl (show π (lift hπ (x (t + t'))) =
      π (lift hπ (x t) * lift hπ (x t')) by rw [map_mul, map_lift, map_lift, map_lift, hx])]
    exact commutatorElement_mul_right_of_central (hcen (commLift_mem_ker hπ hx s t')))
    fun s s' => by
  refine AddMonoidHom.ext fun t => ?_
  apply Additive.toMul.injective
  apply Subtype.ext
  change ⁅lift hπ (x (s + s')), lift hπ (x t)⁆ = ⁅lift hπ (x s), lift hπ (x t)⁆ *
    ⁅lift hπ (x s'), lift hπ (x t)⁆
  rw [commutatorElement_eq_of_map_eq hcen (show π (lift hπ (x (s + s'))) =
    π (lift hπ (x s) * lift hπ (x s')) by rw [map_mul, map_lift, map_lift, map_lift, hx]) rfl]
  exact commutatorElement_mul_left_of_central (hcen (commLift_mem_ker hπ hx s' t))

theorem commPairing_apply (s t : k) :
    ((Additive.toMul (commPairing hcen hπ hx s t) : Subgroup.center E) : E) =
      ⁅lift hπ (x s), lift hπ (x t)⁆ := rfl

theorem commPairing_self (s : k) : commPairing hcen hπ hx s s = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [commPairing_apply]
  simp

theorem commPairing_smul {g : K} {a : k} (hg : ∀ s, g * x s * g⁻¹ = x (a * s)) (s t : k) :
    commPairing hcen hπ hx (a * s) (a * t) = commPairing hcen hπ hx s t := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [commPairing_apply, commPairing_apply]
  set g' := lift hπ g
  rw [commutatorElement_eq_of_map_eq hcen
      (show π (lift hπ (x (a * s))) = π (g' * lift hπ (x s) * g'⁻¹) by
        rw [map_mul, map_mul, map_inv, map_lift, map_lift, map_lift, hg])
      (show π (lift hπ (x (a * t))) = π (g' * lift hπ (x t) * g'⁻¹) by
        rw [map_mul, map_mul, map_inv, map_lift, map_lift, map_lift, hg]),
    ← conjugate_commutatorElement]
  have hc := Subgroup.mem_center_iff.1 (hcen (commLift_mem_ker hπ hx s t)) g'
  rw [hc, mul_inv_cancel_right]

theorem commute_of_commPairing_eq_zero (h0 : commPairing hcen hπ hx = 0) {e e' : E} {s t : k}
    (he : π e = x s) (he' : π e' = x t) : e * e' = e' * e := by
  have h1 : ⁅e, e'⁆ = ⁅lift hπ (x s), lift hπ (x t)⁆ :=
    commutatorElement_eq_of_map_eq hcen (by rw [he, map_lift]) (by rw [he', map_lift])
  have h2 : ⁅lift hπ (x s), lift hπ (x t)⁆ = 1 := by
    have := congrArg (fun f => ((Additive.toMul (f s t) : Subgroup.center E) : E)) h0
    simpa [commPairing_apply] using this
  rw [← commutatorElement_eq_one_iff_mul_comm, h1, h2]

@[expose] noncomputable def canonLift (g : K) (a : k) (s : k) : E :=
  ⁅lift hπ g, lift hπ (x ((a - 1)⁻¹ * s))⁆

omit hcen in
theorem map_canonLift {g : K} {a : k} (hg : ∀ s, g * x s * g⁻¹ = x (a * s)) (ha : a ≠ 1) (s : k) :
    π (canonLift hπ (x := x) g a s) = x s := by
  rw [canonLift, map_commutatorElement, map_lift, map_lift, commutatorElement_def, hg,
    ← x_neg hx, ← hx]
  congr 1
  have : a - 1 ≠ 0 := sub_ne_zero.2 ha
  field_simp
  ring

theorem canonLift_add (h0 : commPairing hcen hπ hx = 0) {g : K} {a : k}
    (hg : ∀ s, g * x s * g⁻¹ = x (a * s)) (ha : a ≠ 1) (s t : k) :
    canonLift hπ (x := x) g a (s + t) =
      canonLift hπ (x := x) g a s * canonLift hπ (x := x) g a t := by
  simp only [canonLift]
  rw [commutatorElement_eq_of_map_eq hcen rfl (show π (lift hπ (x ((a - 1)⁻¹ * (s + t)))) =
      π (lift hπ (x ((a - 1)⁻¹ * s)) * lift hπ (x ((a - 1)⁻¹ * t))) by
    rw [map_mul, map_lift, map_lift, map_lift, ← hx, mul_add])]
  have e : ∀ a b c : E, ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := fun a b c => by
    simp only [commutatorElement_def]
    group
  rw [e]
  congr 1
  have hc := commute_of_commPairing_eq_zero hcen hπ hx h0 (map_lift hπ (x ((a - 1)⁻¹ * s)))
    (show π (⁅lift hπ g, lift hπ (x ((a - 1)⁻¹ * t))⁆) = x t from map_canonLift hπ hx hg ha t)
  rw [hc, mul_inv_cancel_right]

omit hx in
theorem conj_canonLift {g g' : K} {a a' : k} (hgg : g' * g * g'⁻¹ = g)
    (hg' : ∀ s, g' * x s * g'⁻¹ = x (a' * s)) {e : E} (he : π e = g') (s : k) :
    e * canonLift hπ (x := x) g a s * e⁻¹ = canonLift hπ (x := x) g a (a' * s) := by
  simp only [canonLift]
  rw [conjugate_commutatorElement]
  refine commutatorElement_eq_of_map_eq hcen ?_ ?_
  · rw [map_mul, map_mul, map_inv, map_lift, he, hgg]
  · rw [map_mul, map_mul, map_inv, map_lift, he, hg', map_lift]
    congr 1
    ring

omit hπ hx in
theorem lift_unique {ψ ψ' : k → E} (hψ : ∀ s t, ψ (s + t) = ψ s * ψ t)
    (hψ' : ∀ s t, ψ' (s + t) = ψ' s * ψ' t) (hπψ : ∀ s, π (ψ s) = x s) (hπψ' : ∀ s, π (ψ' s) = x s)
    {e : E} {a : k} (ha : a ≠ 1) (he : ∀ s, e * ψ s * e⁻¹ = ψ (a * s))
    (he' : ∀ s, e * ψ' s * e⁻¹ = ψ' (a * s)) : ψ = ψ' := by
  set ρ : k → E := fun s => (ψ s)⁻¹ * ψ' s with hρ
  have hker : ∀ s, ρ s ∈ π.ker := fun s => by
    rw [MonoidHom.mem_ker, hρ, map_mul, map_inv, hπψ, hπψ', inv_mul_cancel]
  have hcent : ∀ s g, g * ρ s = ρ s * g := fun s g => (Subgroup.mem_center_iff.1 (hcen (hker s))) g
  have hadd : ∀ s t, ρ (s + t) = ρ s * ρ t := fun s t => by
    simp only [hρ, hψ, hψ']
    calc (ψ s * ψ t)⁻¹ * (ψ' s * ψ' t) = (ψ t)⁻¹ * (ρ s) * ψ' t := by simp only [hρ]; group
      _ = ρ s * ((ψ t)⁻¹ * ψ' t) := by rw [hcent s (ψ t)⁻¹, mul_assoc]
  have hinv : ∀ s, ρ (a * s) = ρ s := fun s => by
    have : ρ (a * s) = e * ρ s * e⁻¹ := by
      simp only [hρ, ← he, ← he']
      group
    rw [this, hcent s e, mul_inv_cancel_right]
  have hzero : ∀ s, ρ ((a - 1) * s) = 1 := fun s => by
    have h1 := hadd ((a - 1) * s) s
    rw [show (a - 1) * s + s = a * s by ring, hinv] at h1
    exact (mul_eq_right.1 h1.symm)
  funext s
  have h2 := hzero ((a - 1)⁻¹ * s)
  rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 ha), one_mul] at h2
  have h3 : (ψ s)⁻¹ * ψ' s = 1 := h2
  exact (inv_mul_eq_one.1 h3)

end RootGroup

section RankOne

open RankOneRels

variable {k : Type*} [Field k] [Finite k] (R : RankOneRels K k)

omit hcen in
theorem w_conj_h {t u : k} (ht : t ≠ 0) (hu : u ≠ 0) :
    R.w t * R.h u * (R.w t)⁻¹ = R.h u⁻¹ := by
  have hC : ∀ s t : k, s ≠ 0 → t ≠ 0 → R.h (s * t) = R.h s * R.h t := fun s t hs ht =>
    R.h_mul hs ht
  rw [R.w_eq_h_mul t]
  have e : R.h t * R.w 1 * R.h u * (R.h t * R.w 1)⁻¹ =
      R.h t * (R.w 1 * R.h u) * (R.w 1)⁻¹ * (R.h t)⁻¹ := by group
  rw [e, R.w_one_mul_h hC hu]
  have e2 : R.h t * (R.h u⁻¹ * R.w 1) * (R.w 1)⁻¹ * (R.h t)⁻¹ =
      R.h t * R.h u⁻¹ * (R.h t)⁻¹ := by group
  rw [e2, (R.commute_h ht (inv_ne_zero hu)).eq, mul_inv_cancel_right]

omit hcen hπ in
theorem exists_prime_charP : ∃ p : ℕ, ∃ _ : Fact p.Prime, CharP k p := by
  obtain ⟨p, hp⟩ := CharP.exists k
  exact ⟨p, ⟨(CharP.char_is_prime_or_zero k p).resolve_right
    (CharP.char_ne_zero_of_finite k p)⟩, hp⟩

theorem commPairing_x_eq_zero (hk4 : Nat.card k ≠ 4) (hk9 : Nat.card k ≠ 9) :
    commPairing hcen hπ R.x_add = 0 := by
  obtain ⟨p, _, _⟩ := exists_prime_charP (k := k)
  refine Pairing.pairing_eq_zero_of_sq p hk4 hk9 (commPairing_self hcen hπ R.x_add)
    fun v hv s t => ?_
  exact commPairing_smul hcen hπ R.x_add (R.h_conj_x hv) s t

theorem commPairing_y_eq_zero (hk4 : Nat.card k ≠ 4) (hk9 : Nat.card k ≠ 9) :
    commPairing hcen hπ R.y_add = 0 := by
  obtain ⟨p, _, _⟩ := exists_prime_charP (k := k)
  refine Pairing.pairing_eq_zero_of_sq p hk4 hk9 (commPairing_self hcen hπ R.y_add)
    fun v hv s t => ?_
  have h := commPairing_smul hcen hπ R.y_add (R.h_conj_y (inv_ne_zero hv)) s t
  rwa [inv_pow, inv_inv] at h

variable (hk4 : Nat.card k ≠ 4) (hk9 : Nat.card k ≠ 9) {u : k} (hu0 : u ≠ 0) (hu1 : u ^ 2 ≠ 1)

@[expose] noncomputable def xLift : k → E := canonLift hπ (x := R.x) (R.h u) (u ^ 2)

@[expose] noncomputable def yLift : k → E := canonLift hπ (x := R.y) (R.h u) ((u ^ 2)⁻¹)

omit hcen [Finite k] in
include hu0 hu1 in
theorem map_xLift (a : k) : π (xLift hπ R (u := u) a) = R.x a :=
  map_canonLift hπ R.x_add (R.h_conj_x hu0) hu1 a

omit hcen [Finite k] in
include hu0 hu1 in
theorem map_yLift (a : k) : π (yLift hπ R (u := u) a) = R.y a :=
  map_canonLift hπ R.y_add (R.h_conj_y hu0) (inv_ne_one.2 hu1) a

include hk4 hk9 hu0 hu1 in
theorem xLift_add (a b : k) :
    xLift hπ R (u := u) (a + b) = xLift hπ R (u := u) a * xLift hπ R (u := u) b :=
  canonLift_add hcen hπ R.x_add (commPairing_x_eq_zero hcen hπ R hk4 hk9) (R.h_conj_x hu0) hu1 a b

include hk4 hk9 hu0 hu1 in
theorem yLift_add (a b : k) :
    yLift hπ R (u := u) (a + b) = yLift hπ R (u := u) a * yLift hπ R (u := u) b :=
  canonLift_add hcen hπ R.y_add (commPairing_y_eq_zero hcen hπ R hk4 hk9) (R.h_conj_y hu0)
    (inv_ne_one.2 hu1) a b

include hk4 hk9 hu0 hu1 in
theorem lift_conj_x {t : k} (ht : t ≠ 0) (a : k) :
    xLift hπ R (u := u) t * yLift hπ R (u := u) (-t⁻¹) * xLift hπ R (u := u) t *
        xLift hπ R (u := u) a *
        (xLift hπ R (u := u) t * yLift hπ R (u := u) (-t⁻¹) * xLift hπ R (u := u) t)⁻¹ =
      yLift hπ R (u := u) (-(t ^ 2)⁻¹ * a) := by
  set X := xLift hπ R (u := u)
  set Y := yLift hπ R (u := u)
  set W := X t * Y (-t⁻¹) * X t with hW
  have hπW : π W = R.w t := by
    rw [hW, map_mul, map_mul, map_xLift hπ R hu0 hu1, map_yLift hπ R hu0 hu1, R.w_def]
  have hXadd : ∀ a b, X (a + b) = X a * X b := xLift_add hcen hπ R hk4 hk9 hu0 hu1
  set ψ : k → E := fun b => W * X (-(t ^ 2) * b) * W⁻¹ with hψ
  have hψadd : ∀ b c, ψ (b + c) = ψ b * ψ c := fun b c => by
    simp only [hψ]
    rw [show -(t ^ 2) * (b + c) = -(t ^ 2) * b + -(t ^ 2) * c by ring, hXadd]
    group
  have hπψ : ∀ b, π (ψ b) = R.y b := fun b => by
    rw [hψ, map_mul, map_mul, map_inv, hπW, map_xLift hπ R hu0 hu1, R.w_conj_x ht]
    congr 1
    field_simp
  set h' := lift hπ (R.h u)
  have hh' : π h' = R.h u := map_lift hπ _
  set e := W * h' * W⁻¹ with he
  have hπe : π e = R.w t * R.h u * (R.w t)⁻¹ := by rw [he, map_mul, map_mul, map_inv, hπW, hh']
  have hcomm : R.h u * R.h u * (R.h u)⁻¹ = R.h u := by group
  have heψ : ∀ b, e * ψ b * e⁻¹ = ψ (u ^ 2 * b) := fun b => by
    have := conj_canonLift hcen hπ (x := R.x) (g := R.h u) (a := u ^ 2) hcomm (R.h_conj_x hu0) hh'
      (-(t ^ 2) * b)
    simp only [hψ, he]
    calc W * h' * W⁻¹ * (W * X (-(t ^ 2) * b) * W⁻¹) * (W * h' * W⁻¹)⁻¹ =
        W * (h' * X (-(t ^ 2) * b) * h'⁻¹) * W⁻¹ := by group
      _ = W * X (-(t ^ 2) * (u ^ 2 * b)) * W⁻¹ := by
        rw [show h' * X (-(t ^ 2) * b) * h'⁻¹ = X (u ^ 2 * (-(t ^ 2) * b)) from this]
        congr 3
        ring
  have hπe' : π e = R.h u⁻¹ := by rw [hπe, w_conj_h R ht hu0]
  have hgg : π e * R.h u * (π e)⁻¹ = R.h u := by
    rw [hπe', (R.commute_h (inv_ne_zero hu0) hu0).eq, mul_inv_cancel_right]
  have hgy : ∀ s, π e * R.y s * (π e)⁻¹ = R.y (u ^ 2 * s) := fun s => by
    rw [hπe', R.h_conj_y (inv_ne_zero hu0), inv_pow, inv_inv]
  have heY : ∀ b, e * Y b * e⁻¹ = Y (u ^ 2 * b) := fun b =>
    conj_canonLift hcen hπ (x := R.y) (g := R.h u) (a := (u ^ 2)⁻¹) hgg hgy rfl b
  have hY : ψ = Y := lift_unique hcen (x := R.y) hψadd (yLift_add hcen hπ R hk4 hk9 hu0 hu1)
    hπψ (map_yLift hπ R hu0 hu1) hu1 heψ heY
  have := congrFun hY (-(t ^ 2)⁻¹ * a)
  simp only [hψ] at this
  rw [← this]
  congr 2
  field_simp

@[expose] noncomputable def liftRels : RankOneRels E k where
  x := xLift hπ R (u := u)
  y := yLift hπ R (u := u)
  x_add := xLift_add hcen hπ R hk4 hk9 hu0 hu1
  y_add := yLift_add hcen hπ R hk4 hk9 hu0 hu1
  conj_x _ ht a := lift_conj_x hcen hπ R hk4 hk9 hu0 hu1 ht a

end RankOne

section Section

open RankOneRels

variable {k : Type*} [Field k] [Finite k] {R : RankOneRels K k} (R' : RankOneRels E k)
  (hx' : ∀ a, π (R'.x a) = R.x a) (hy' : ∀ a, π (R'.y a) = R.y a)
include hx' hy'

omit hcen [Finite k] in
theorem map_w_of_lift (t : k) : π (R'.w t) = R.w t := by
  rw [RankOneRels.w_def, RankOneRels.w_def, map_mul, map_mul, hx', hy']

omit hcen [Finite k] in
theorem map_h_of_lift (t : k) : π (R'.h t) = R.h t := by
  rw [RankOneRels.h_def, RankOneRels.h_def, map_mul, map_inv, map_w_of_lift R' hx' hy',
    map_w_of_lift R' hx' hy']

omit hcen [Finite k] in
theorem map_sub_of_lift : R'.sub.map π = R.sub := by
  rw [RankOneRels.sub, RankOneRels.sub, MonoidHom.map_closure, Set.image_union]
  congr 2
  · ext g
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, hx']
  · ext g
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, hy']

omit hcen in
theorem injOn_sub_of_lift (hi : ∀ a t, t ≠ 0 → R.x a * R.h t = 1 → a = 0 ∧ t = 1)
    (hii : ∀ a b t, t ≠ 0 → R.x a * R.w 1 * R.x b * R.h t ≠ 1) :
    Set.InjOn π R'.sub := by
  refine injOn_of_eq_one fun g hg h1 => ?_
  rcases R'.sub_subset_bruhat (fun s t hs ht => R'.h_mul hs ht) hg with
    ⟨a, t, ht, rfl⟩ | ⟨a, b, t, ht, rfl⟩
  · rw [map_mul, hx', map_h_of_lift R' hx' hy'] at h1
    obtain ⟨rfl, rfl⟩ := hi a t ht h1
    rw [R'.x_zero, R'.h_one, one_mul]
  · rw [map_mul, map_mul, map_mul, hx', map_w_of_lift R' hx' hy', hx',
      map_h_of_lift R' hx' hy'] at h1
    exact absurd h1 (hii a b t ht)

omit hcen in
theorem exists_section_of_lift (hi : ∀ a t, t ≠ 0 → R.x a * R.h t = 1 → a = 0 ∧ t = 1)
    (hii : ∀ a b t, t ≠ 0 → R.x a * R.w 1 * R.x b * R.h t ≠ 1) :
    ∃ φ : R.sub →* E, ∀ g, π (φ g) = g := by
  set L' := R'.sub
  have hmap : ∀ g : L', π g ∈ R.sub := fun g => by
    rw [← map_sub_of_lift R' hx' hy']
    exact ⟨g, g.2, rfl⟩
  let ψ : L' →* R.sub := (π.comp L'.subtype).codRestrict _ hmap
  have hψ : Function.Bijective ψ := by
    refine ⟨fun g g' h => Subtype.ext (injOn_sub_of_lift R' hx' hy' hi hii g.2 g'.2
      (congrArg Subtype.val h)), fun g => ?_⟩
    obtain ⟨g', hg', hgg'⟩ : (g : K) ∈ L'.map π := by
      rw [map_sub_of_lift R' hx' hy']
      exact g.2
    exact ⟨⟨g', hg'⟩, Subtype.ext hgg'⟩
  refine ⟨L'.subtype.comp (MulEquiv.ofBijective ψ hψ).symm.toMonoidHom, fun g => ?_⟩
  exact congrArg Subtype.val ((MulEquiv.ofBijective ψ hψ).apply_symm_apply g)

end Section

omit hcen in
theorem _root_.CFSG.LieType.Steinberg.RankOneRels.exists_section_of_central {k : Type*} [Field k]
    [Finite k]
    (R : RankOneRels K k) (hk4 : Nat.card k ≠ 4) (hk9 : Nat.card k ≠ 9) {u : k} (hu0 : u ≠ 0)
    (hu1 : u ^ 2 ≠ 1) (hi : ∀ a t, t ≠ 0 → R.x a * R.h t = 1 → a = 0 ∧ t = 1)
    (hii : ∀ a b t, t ≠ 0 → R.x a * R.w 1 * R.x b * R.h t ≠ 1)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) :
    ∃ φ : R.sub →* E, ∀ g, π (φ g) = g :=
  exists_section_of_lift (liftRels hcen hπ R hk4 hk9 hu0 hu1)
    (map_xLift hπ R hu0 hu1) (map_yLift hπ R hu0 hu1) hi hii


end CFSG.LieType.Steinberg.CentralExt.TorusLift
