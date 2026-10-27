module

public import CFSG.CGT.Stroth77.Section310Char
public import CFSG.CGT.Stroth77.Section33
public import CFSG.CGT.Stroth77.TorusNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnside

public section

namespace CFSG.CGT.Stroth77

section Omega

variable {G : Type} [Group G] [Finite G]

theorem mul_self_eq_one_of_mem_omegaIn_one {D : Subgroup G}
    (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {x : G} (hx : x ∈ omegaIn 1 D) : x * x = 1 := by
  obtain ⟨y, hy, rfl⟩ := hx
  rw [CFSG.omega] at hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    have h : ((z ^ (2 ^ 1) : D) : G) = 1 := congrArg Subtype.val (show z ^ (2 ^ 1) = 1 from hz)
    simpa [pow_two] using h
  | one => simp
  | mul a b _ _ ha hb =>
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul] at ha hb ⊢
    have hc : (b : G) * a = a * b := hD _ b.2 _ a.2
    calc (a : G) * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hc]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  | inv a _ ha =>
    simp only [Subgroup.coe_subtype, Subgroup.coe_inv] at ha ⊢
    rw [← mul_inv_rev, ha, inv_one]

theorem isElemAbelian_omegaIn_one {D : Subgroup G} (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) :
    CFSG.Open.IsElemAbelian 2 (omegaIn 1 D) := by
  refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
  · exact hD _ (omegaIn_le 1 D a.2) _ (omegaIn_le 1 D b.2)
  · rw [pow_two]
    exact mul_self_eq_one_of_mem_omegaIn_one hD hx

theorem omegaIn_one_mono {A D : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAD : A ≤ D) :
    omegaIn 1 A ≤ omegaIn 1 D := fun x hx =>
  mem_omegaIn_one_of_mul_self (hAD (omegaIn_le 1 A hx)) (mul_self_eq_one_of_mem_omegaIn_one hA hx)

end Omega

section TorusInvolutions

theorem zmod_two_pow_eq_zero_or_of_add_self {m : ℕ} (x : ZMod (2 ^ m)) (h : x + x = 0) :
    x = 0 ∨ x = 2 ^ (m - 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · left
    exact Subsingleton.elim (α := ZMod 1) x 0
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  haveI : NeZero (2 ^ (t + 1)) := ⟨by positivity⟩
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 2 ^ (t + 1) ∧ (n : ZMod (2 ^ (t + 1))) = x :=
    ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
  have h2 : ((2 * n : ℕ) : ZMod (2 ^ (t + 1))) = 0 := by
    push_cast
    rw [two_mul]
    exact h
  rw [ZMod.natCast_eq_zero_iff, pow_succ'] at h2
  obtain ⟨q, rfl⟩ : 2 ^ t ∣ n := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 h2
  have hq : q < 2 := by
    have h' : 2 ^ t * q < 2 ^ t * 2 := by rw [← pow_succ]; exact hn
    exact Nat.lt_of_mul_lt_mul_left h'
  interval_cases q
  · left
    simp
  · right
    simp

theorem card_add_self_eq_zero_le (k : Fin 3 → ℕ) :
    Nat.card {v : Torus k // v + v = 0} ≤ 8 := by
  classical
  let f : {v : Torus k // v + v = 0} → (Fin 3 → Bool) := fun v i => decide (v.1 i ≠ 0)
  have hf : Function.Injective f := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    apply Subtype.ext
    funext i
    change v i = w i
    have hi := congrFun h i
    simp only [f, decide_eq_decide] at hi
    have hvi := zmod_two_pow_eq_zero_or_of_add_self (v i) (congrFun hv i)
    have hwi := zmod_two_pow_eq_zero_or_of_add_self (w i) (congrFun hw i)
    rcases hvi with h0 | h1 <;> rcases hwi with h0' | h1'
    · rw [h0, h0']
    · by_cases hz : w i = 0
      · rw [h0, hz]
      · exact absurd (hi.mpr hz) (not_not.mpr h0)
    · by_cases hz : v i = 0
      · rw [hz, h0']
      · exact absurd (hi.mp hz) (not_not.mpr h0')
    · rw [h1, h1']
  calc Nat.card {v : Torus k // v + v = 0} ≤ Nat.card (Fin 3 → Bool) :=
        Nat.card_le_card_of_injective f hf
    _ = 8 := by simp [Nat.card_eq_fintype_card]

theorem card_add_self_eq_zero_eq_eight {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) :
    Nat.card {v : Torus k // v + v = 0} = 8 := by
  classical
  refine le_antisymm (card_add_self_eq_zero_le k) ?_
  let f : (Fin 3 → Bool) → {v : Torus k // v + v = 0} := fun ε =>
    ⟨fun i => if ε i then 2 ^ (k i - 1) else 0, by
      funext i
      by_cases h : ε i
      · simp only [Pi.add_apply, h, if_true, Pi.zero_apply]
        rw [← two_mul]
        exact two_mul_two_pow_pred (k i)
      · simp [h]⟩
  have hf : Function.Injective f := by
    intro ε ε' h
    funext i
    have hi := congrFun (congrArg Subtype.val h) i
    simp only [f] at hi
    have hne := two_pow_pred_ne_zero (hk i)
    cases hε : ε i <;> cases hε' : ε' i <;> simp only [hε, hε', Bool.false_eq_true, if_false,
      if_true] at hi <;> first | rfl | exact absurd hi.symm hne | exact absurd hi hne
  calc 8 = Nat.card (Fin 3 → Bool) := by simp [Nat.card_eq_fintype_card]
    _ ≤ Nat.card {v : Torus k // v + v = 0} := Nat.card_le_card_of_injective f hf

end TorusInvolutions

section TypedOmega

variable {G : Type} [Group G] [Finite G]

theorem comm_of_torus {D : Subgroup G} {k : Fin 3 → ℕ} (e : Additive D ≃+ Torus k) :
    ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy => by
  have h := e.injective (show e (Additive.ofMul (⟨x, hx⟩ * ⟨y, hy⟩ : D)) =
    e (Additive.ofMul (⟨y, hy⟩ * ⟨x, hx⟩ : D)) by
      rw [ofMul_mul, ofMul_mul, map_add, map_add, add_comm])
  exact congrArg Subtype.val (Additive.ofMul.injective h)

theorem card_omegaIn_one_eq {D : Subgroup G} {k : Fin 3 → ℕ} (e : Additive D ≃+ Torus k) :
    Nat.card (omegaIn 1 D) = Nat.card {v : Torus k // v + v = 0} := by
  have hD := comm_of_torus e
  refine Nat.card_congr
    { toFun := fun x => ⟨e (Additive.ofMul ⟨x.1, omegaIn_le 1 D x.2⟩), ?_⟩
      invFun := fun v => ⟨((Additive.toMul (e.symm v.1) : D) : G), ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  · rw [← map_add, ← ofMul_mul]
    have h1 : (⟨x.1, omegaIn_le 1 D x.2⟩ : D) * ⟨x.1, omegaIn_le 1 D x.2⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_mem_omegaIn_one hD x.2)
    rw [h1, ofMul_one, map_zero]
  · refine mem_omegaIn_one_of_mul_self (Additive.toMul (e.symm v.1) : D).2 ?_
    have h1 : (Additive.toMul (e.symm v.1) : D) * Additive.toMul (e.symm v.1) = 1 := by
      apply Additive.ofMul.injective
      rw [ofMul_mul, ofMul_toMul, ← map_add, v.2, map_zero, ofMul_one]
    exact congrArg Subtype.val h1

theorem card_omegaIn_one_eq_eight {D : Subgroup G} {k : Fin 3 → ℕ} (e : Additive D ≃+ Torus k)
    (hk : ∀ i, 1 ≤ k i) : Nat.card (omegaIn 1 D) = 8 :=
  (card_omegaIn_one_eq e).trans (card_add_self_eq_zero_eq_eight hk)

theorem card_omegaIn_one_le {D : Subgroup G} {k : Fin 3 → ℕ} (e : Additive D ≃+ Torus k) :
    Nat.card (omegaIn 1 D) ≤ 8 :=
  (card_omegaIn_one_eq e).trans_le (card_add_self_eq_zero_le k)

end TypedOmega

section Homocyclic

variable {G : Type} [Group G] [Finite G]

theorem pow_two_pow_eq_one_of_torus {D : Subgroup G} {k : Fin 3 → ℕ} {n : ℕ}
    (e : Additive D ≃+ Torus k) (hk : ∀ i, k i = n) {y : G} (hy : y ∈ D) : y ^ 2 ^ n = 1 := by
  have h : (2 ^ n) • e (Additive.ofMul (⟨y, hy⟩ : D)) = 0 := by
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
    have h0 : ((2 ^ n : ℕ) : ZMod (2 ^ k i)) = 0 := by rw [hk i]; exact ZMod.natCast_self _
    rw [h0, zero_mul]
  have h2 : (⟨y, hy⟩ : D) ^ 2 ^ n = 1 := by
    apply Additive.ofMul.injective
    apply e.injective
    rw [ofMul_pow, map_nsmul, h, ofMul_one, map_zero]
  simpa using congrArg Subtype.val h2

theorem exists_pow_eq_of_mul_self_of_torus {D : Subgroup G} {k : Fin 3 → ℕ} {n : ℕ}
    (e : Additive D ≃+ Torus k) (hk : ∀ i, k i = n) {x : G} (hx : x ∈ D) (hx2 : x * x = 1) :
    ∃ y ∈ D, y ^ 2 ^ (n - 1) = x := by
  classical
  set v := e (Additive.ofMul (⟨x, hx⟩ : D)) with hv
  have hv2 : v + v = 0 := by
    rw [hv, ← map_add, ← ofMul_mul,
      show (⟨x, hx⟩ : D) * ⟨x, hx⟩ = 1 from Subtype.ext hx2, ofMul_one, map_zero]
  let w : Torus k := fun i => if v i = 0 then 0 else 1
  have hw : (2 ^ (n - 1)) • w = v := by
    funext i
    by_cases h0 : v i = 0
    · simp [w, h0]
    · have h1 := (zmod_two_pow_eq_zero_or_of_add_self (v i) (congrFun hv2 i)).resolve_left h0
      simp only [Pi.smul_apply, w, if_neg h0, nsmul_eq_mul, mul_one]
      rw [h1, hk i]
      push_cast
      rfl
  refine ⟨((Additive.toMul (e.symm w) : D) : G), (Additive.toMul (e.symm w) : D).2, ?_⟩
  have h2 : (Additive.toMul (e.symm w) : D) ^ 2 ^ (n - 1) = ⟨x, hx⟩ := by
    apply Additive.ofMul.injective
    apply e.injective
    rw [ofMul_pow, map_nsmul, ofMul_toMul, AddEquiv.apply_symm_apply, hw]
  simpa using congrArg Subtype.val h2

theorem exists_mul_self_eq_of_torus {D : Subgroup G} {k : Fin 3 → ℕ} {n : ℕ}
    (e : Additive D ≃+ Torus k) (hk : ∀ i, k i = n) (hn : 2 ≤ n) {x : G} (hx : x ∈ D)
    (hx2 : x * x = 1) : ∃ y ∈ D, y * y = x := by
  obtain ⟨y, hy, rfl⟩ := exists_pow_eq_of_mul_self_of_torus e hk hx hx2
  refine ⟨y ^ 2 ^ (n - 2), pow_mem hy _, ?_⟩
  rw [← pow_two, ← pow_mul, ← pow_succ]
  congr 2
  omega

end Homocyclic

section CommHom

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}

@[expose] def commHom (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {b : G}
    (hb : b ∈ Subgroup.normalizer (D : Set G)) : D →* D :=
  MonoidHom.mk' (fun x => conjBy hb x * x⁻¹) (fun x y => by
    apply Subtype.ext
    have hX : b⁻¹ * (x : G) * b ∈ D := (Subgroup.mem_normalizer_iff''.mp hb x).mp x.2
    have hY : b⁻¹ * (y : G) * b ∈ D := (Subgroup.mem_normalizer_iff''.mp hb y).mp y.2
    have h1 : (b⁻¹ * (y : G) * b) * (x : G)⁻¹ = (x : G)⁻¹ * (b⁻¹ * (y : G) * b) :=
      hD _ hY _ (inv_mem x.2)
    have h2 : (y : G)⁻¹ * (x : G)⁻¹ = (x : G)⁻¹ * (y : G)⁻¹ := hD _ (inv_mem y.2) _ (inv_mem x.2)
    simp only [conjBy, Subgroup.coe_mul, Subgroup.coe_inv]
    calc b⁻¹ * ((x : G) * y) * b * ((x : G) * y)⁻¹
        = (b⁻¹ * x * b) * ((b⁻¹ * y * b) * ((y : G)⁻¹ * (x : G)⁻¹)) := by group
      _ = (b⁻¹ * x * b) * ((b⁻¹ * y * b) * (x : G)⁻¹ * (y : G)⁻¹) := by
          rw [h2, mul_assoc (b⁻¹ * (y : G) * b)]
      _ = (b⁻¹ * x * b) * ((x : G)⁻¹ * (b⁻¹ * y * b) * (y : G)⁻¹) := by rw [h1]
      _ = b⁻¹ * x * b * (x : G)⁻¹ * (b⁻¹ * y * b * (y : G)⁻¹) := by group)

variable (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {b : G}
  (hb : b ∈ Subgroup.normalizer (D : Set G))

theorem coe_commHom (x : D) : (commHom hD hb x : G) = b⁻¹ * x * b * (x : G)⁻¹ := rfl

theorem commHom_eq_one_iff (x : D) : commHom hD hb x = 1 ↔ (x : G) * b = b * x := by
  rw [← Subtype.val_inj, coe_commHom, Subgroup.coe_one, mul_inv_eq_one]
  constructor
  · intro h
    calc (x : G) * b = b * (b⁻¹ * x * b) := by group
      _ = b * x := by rw [h]
  · intro h
    rw [mul_assoc, h, inv_mul_cancel_left]

theorem card_inf_centralizer_mul_card_range :
    Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G) * Nat.card (commHom hD hb).range =
      Nat.card D := by
  have hmap : (commHom hD hb).ker.map D.subtype = D ⊓ Subgroup.centralizer {b} := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.coe_subtype, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (commHom_eq_one_iff hD hb y).mp hy⟩
    · rintro ⟨hxD, hx⟩
      exact ⟨⟨x, hxD⟩, (commHom_eq_one_iff hD hb ⟨x, hxD⟩).mpr hx, rfl⟩
  rw [← Subgroup.card_ker_mul_card_range (commHom hD hb), ← hmap,
    Subgroup.card_map_of_injective Subtype.val_injective]

include hD hb in
theorem mem_centralizer_omegaIn_of_card_le
    (hroot : ∀ x ∈ D, x * x = 1 → ∃ y ∈ D, y * y = x)
    (hcard : Nat.card D ≤ 2 * Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G)) :
    b ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  have hsplit := card_inf_centralizer_mul_card_range hD hb
  have hpos : 0 < Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G) := Nat.card_pos
  have hR2 : Nat.card (commHom hD hb).range ≤ 2 := by
    have h : Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G) *
        Nat.card (commHom hD hb).range ≤
        Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G) * 2 := by
      rw [hsplit, mul_comm]; exact hcard
    exact Nat.le_of_mul_le_mul_left h hpos
  have hsq : ∀ r ∈ (commHom hD hb).range, r * r = 1 := by
    intro r hr
    have hdvd := Subgroup.orderOf_dvd_natCard _ hr
    have hR1 : 0 < Nat.card (commHom hD hb).range := Nat.card_pos
    rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one]
    interval_cases h : Nat.card (commHom hD hb).range
    · exact hdvd.trans (one_dvd 2)
    · exact hdvd
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvD := omegaIn_le 1 D hv
  have hv2 := mul_self_eq_one_of_mem_omegaIn_one hD hv
  obtain ⟨y, hy, rfl⟩ := hroot v hvD hv2
  have h1 : commHom hD hb (⟨y, hy⟩ * ⟨y, hy⟩) = 1 := by
    rw [map_mul]
    exact hsq _ (⟨_, rfl⟩)
  exact (commHom_eq_one_iff hD hb _).mp h1

include hD hb in
theorem eight_mul_card_le_of_not_mem_centralizer {n : ℕ} (hn : 3 ≤ n)
    (hexp : ∀ y ∈ D, y ^ 2 ^ n = 1) (hroot : ∀ x ∈ D, x * x = 1 → ∃ y ∈ D, y ^ 2 ^ (n - 1) = x)
    (hbV : b ∉ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    8 * Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G) ≤ Nat.card D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv, hvb⟩ : ∃ v ∈ omegaIn 1 D, ¬ v * b = b * v := by
    by_contra hcon
    push Not at hcon
    exact hbV (Subgroup.mem_centralizer_iff.mpr hcon)
  have hvD := omegaIn_le 1 D hv
  obtain ⟨y, hy, hyv⟩ := hroot v hvD (mul_self_eq_one_of_mem_omegaIn_one hD hv)
  set r := commHom hD hb ⟨y, hy⟩ with hr
  have hnot : ¬ r ^ 2 ^ (n - 1) = 1 := by
    rw [hr, ← map_pow, commHom_eq_one_iff]
    simpa [hyv] using hvb
  have hfin : r ^ 2 ^ (n - 1 + 1) = 1 := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    exact Subtype.ext (by simpa using hexp _ r.2)
  have hord : orderOf r = 2 ^ n := by
    rw [orderOf_eq_prime_pow hnot hfin, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have hdvd : 2 ^ n ∣ Nat.card (commHom hD hb).range := by
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard _ (⟨_, rfl⟩)
  have h8 : 8 ≤ Nat.card (commHom hD hb).range := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      _ ≤ _ := Nat.le_of_dvd Nat.card_pos hdvd
  calc 8 * Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G)
      ≤ Nat.card (commHom hD hb).range * Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G) :=
        Nat.mul_le_mul_right _ h8
    _ = Nat.card D := by rw [mul_comm]; exact card_inf_centralizer_mul_card_range hD hb

end CommHom

section Fixed

variable {G : Type} [Group G] [Finite G]

theorem card_inf_centralizer_eq_card_fixed {D : Subgroup G} {k : Fin 3 → ℕ}
    (e : Additive D ≃+ Torus k) {b : G} (hb : b ∈ Subgroup.normalizer (D : Set G))
    {φ : Torus k →+ Torus k}
    (hconj : ∀ x : D, e (Additive.ofMul (conjBy hb x)) = φ (e (Additive.ofMul x))) :
    Nat.card (D ⊓ Subgroup.centralizer {b} : Subgroup G) = Nat.card {v : Torus k // φ v = v} := by
  have hfix : ∀ x : D, conjBy hb x = x ↔ (x : G) * b = b * x := fun x => by
    rw [← Subtype.val_inj]
    simp only [conjBy]
    constructor
    · intro h
      calc (x : G) * b = b * (b⁻¹ * x * b) := by group
        _ = b * x := by rw [h]
    · intro h
      rw [mul_assoc, h, inv_mul_cancel_left]
  have hfixφ : ∀ x : D, φ (e (Additive.ofMul x)) = e (Additive.ofMul x) ↔
      (x : G) * b = b * x := fun x => by
    rw [← hconj, ← hfix, EmbeddingLike.apply_eq_iff_eq, Additive.ofMul.injective.eq_iff]
  refine Nat.card_congr
    { toFun := fun x => ⟨e (Additive.ofMul ⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩), ?_⟩
      invFun := fun v => ⟨((Additive.toMul (e.symm v.1) : D) : G), ?_⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  · exact (hfixφ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2)
  · refine Subgroup.mem_inf.mpr ⟨(Additive.toMul (e.symm v.1) : D).2,
      Subgroup.mem_centralizer_singleton_iff.mpr ((hfixφ _).mp ?_)⟩
    simpa using v.2

theorem card_fixed_uv_t300_two :
    Nat.card {v : Torus (StrothTypeIndex.t300 2).k //
      (StrothTypeIndex.t300 2).action.φuv v = v} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_fixed_uv_t310_two :
    Nat.card {v : Torus (StrothTypeIndex.t310 2 le_rfl).k //
      (StrothTypeIndex.t310 2 le_rfl).action.φuv v = v} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

end Fixed

section Action

variable {G : Type} [Group G] [Finite G]

theorem card_mulAut_of_isElemAbelian {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V)
    (h8 : Nat.card V = 8) : Nat.card (MulAut V) = 168 := by
  obtain ⟨e⟩ := CFSG.ComponentClassification.GHarris.nonempty_mulAut_equiv_GL32 hV h8
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.ComponentClassification.GHarris.card_GL32_gh

theorem normalizerMonoidHom_eq_one_iff {V : Subgroup G}
    (x : Subgroup.normalizer (V : Set G)) :
    V.normalizerMonoidHom x = 1 ↔ (x : G) ∈ Subgroup.centralizer (V : Set G) := by
  rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]

theorem mul_mul_inv_mul_inv_eq_of_rels {uv t u : G} (huvu : uv * u = u * uv)
    (htu : t * u = u * uv * t) : t * u * t⁻¹ * u⁻¹ = uv := by
  rw [htu]
  calc u * uv * t * t⁻¹ * u⁻¹ = u * uv * u⁻¹ := by group
    _ = uv * u * u⁻¹ := by rw [huvu]
    _ = uv := by group

theorem normalizerMonoidHom_mul_ne {V : Subgroup G} {uv t u : G}
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (hu : u ∈ Subgroup.normalizer (V : Set G))
    (huvu : uv * u = u * uv) (htu : t * u = u * uv * t)
    (huvV : uv ∉ Subgroup.centralizer (V : Set G)) :
    V.normalizerMonoidHom ⟨t, ht⟩ * V.normalizerMonoidHom ⟨u, hu⟩ ≠
      V.normalizerMonoidHom ⟨u, hu⟩ * V.normalizerMonoidHom ⟨t, ht⟩ := by
  intro h
  apply huvV
  have h1 : V.normalizerMonoidHom (⟨t, ht⟩ * ⟨u, hu⟩ * ⟨t, ht⟩⁻¹ * ⟨u, hu⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  rw [normalizerMonoidHom_eq_one_iff] at h1
  simpa [mul_mul_inv_mul_inv_eq_of_rels huvu htu] using h1

theorem card_map_eq_eight_and_eq_sup {S V : Subgroup G} (hS : IsPGroup 2 S)
    (hV : CFSG.Open.IsElemAbelian 2 V) (h8 : Nat.card V = 8)
    (hSV : S ≤ Subgroup.normalizer (V : Set G)) {uv t u : G} (huvS : uv ∈ S) (htS : t ∈ S)
    (huS : u ∈ S) (huvu : uv * u = u * uv) (htu : t * u = u * uv * t)
    (huvV : uv ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ((S.subgroupOf (Subgroup.normalizer (V : Set G))).map V.normalizerMonoidHom) = 8 ∧
      S = S ⊓ Subgroup.centralizer (V : Set G) ⊔ Subgroup.closure {uv, t, u} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (V : Set G) with hN
  set W := Subgroup.closure ({uv, t, u} : Set G) with hW
  have hWS : W ≤ S := by
    rw [hW, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [huvS, htS, huS]
  set P := (S.subgroupOf N).map V.normalizerMonoidHom with hP
  set H := (W.subgroupOf N).map V.normalizerMonoidHom with hH
  have hHP : H ≤ P := Subgroup.map_mono (fun x hx => hWS hx)
  have hP2 : IsPGroup 2 P :=
    (hS.comap_of_injective N.subtype Subtype.val_injective).map _
  have hPdvd : Nat.card P ∣ 8 := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hP2
    have hdvd : 2 ^ j ∣ 168 := by
      rw [← hj, ← card_mulAut_of_isElemAbelian hV h8]
      exact Subgroup.card_subgroup_dvd_card P
    have hj3 : j ≤ 3 := by
      by_contra h4
      have : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    rw [hj]
    exact Nat.pow_dvd_pow 2 hj3
  have hnc := normalizerMonoidHom_mul_ne (hSV htS) (hSV huS) huvu htu huvV
  have hH8 : Nat.card H = 8 :=
    card_eq_eight_of_dvd ((Subgroup.card_dvd_of_le hHP).trans hPdvd)
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.subset_closure (by simp) : t ∈ W)))
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
        (Subgroup.subset_closure (by simp) : u ∈ W))) hnc
  have hHP' : H = P :=
    Subgroup.eq_of_le_of_card_ge hHP ((Nat.le_of_dvd (by norm_num) hPdvd).trans hH8.ge)
  refine ⟨hHP' ▸ hH8, le_antisymm ?_ (sup_le inf_le_left hWS)⟩
  intro s hs
  have hsP : V.normalizerMonoidHom ⟨s, hSV hs⟩ ∈ P :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hs)
  rw [← hHP'] at hsP
  obtain ⟨w, hw, hwθ⟩ := hsP
  have hk : V.normalizerMonoidHom (w⁻¹ * ⟨s, hSV hs⟩) = 1 := by
    rw [map_mul, map_inv, hwθ, inv_mul_cancel]
  rw [normalizerMonoidHom_eq_one_iff] at hk
  have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
  have hk' : (w : G)⁻¹ * s ∈ S ⊓ Subgroup.centralizer (V : Set G) :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hWS hwW)) hs, by simpa using hk⟩
  have : s = (w : G) * ((w : G)⁻¹ * s) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_right hwW) (Subgroup.mem_sup_left hk')

theorem card_eq_card_inf_mul_card_map {S K B : Subgroup G} {Q : Type*} [Group Q]
    (π : S →* Q) (hπ : ∀ s : S, π s = 1 ↔ (s : G) ∈ K) (hBS : B ≤ S) :
    Nat.card B = Nat.card (B ⊓ K : Subgroup G) * Nat.card ((B.subgroupOf S).map π) := by
  set f : B.subgroupOf S →* Q := π.comp (B.subgroupOf S).subtype
  have hrange : f.range = (B.subgroupOf S).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker.map (S.subtype.comp (B.subgroupOf S).subtype) = B ⊓ K := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, MonoidHom.coe_comp, Subgroup.coe_subtype,
      Function.comp_apply, Subgroup.mem_inf, f]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Subgroup.mem_subgroupOf.mp y.2, (hπ _).mp hy⟩
    · rintro ⟨hxB, hxK⟩
      exact ⟨⟨⟨x, hBS hxB⟩, Subgroup.mem_subgroupOf.mpr hxB⟩, (hπ _).mpr hxK, rfl⟩
  have hinj : Function.Injective (S.subtype.comp (B.subgroupOf S).subtype) :=
    Subtype.val_injective.comp Subtype.val_injective
  rw [← hrange, ← hker, Subgroup.card_map_of_injective hinj, Subgroup.card_ker_mul_card_range,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv]

theorem eq_of_isMulCommutative_of_card_eq {S D B : Subgroup G} {Q : Type*} [Group Q] [Finite Q]
    (π : S →* Q) (hπ : ∀ s : S, π s = 1 ↔ (s : G) ∈ D) (h8 : Nat.card π.range = 8)
    {t u z : S} (htu : π t * π u ≠ π u * π t) (hz : ∀ s : S, π z * π s = π s * π z)
    (hA : ∀ b : S, π b ≠ 1 →
      2 * Nat.card (D ⊓ Subgroup.centralizer {(b : G)} : Subgroup G) < Nat.card D)
    (hB : ∀ b : S, π b = π z →
      4 * Nat.card (D ⊓ Subgroup.centralizer {(b : G)} : Subgroup G) < Nat.card D)
    (hBS : B ≤ S) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hcard : Nat.card B = Nat.card D) :
    B = D := by
  set R := (B.subgroupOf S).map π with hR
  have hsplit := card_eq_card_inf_mul_card_map π hπ hBS
  rw [← hR] at hsplit
  have hRle : R ≤ π.range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hRdvd : Nat.card R ∣ 8 := h8 ▸ Subgroup.card_dvd_of_le hRle
  have hcent : ∀ b : S, (b : G) ∈ B → Nat.card (B ⊓ D : Subgroup G) ≤
      Nat.card (D ⊓ Subgroup.centralizer {(b : G)} : Subgroup G) := by
    intro b hb
    refine Subgroup.card_le_of_le fun x hx => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hBc _ (Subgroup.mem_inf.mp hx).1 _ hb
  have hRc : ∀ p ∈ R, ∀ q ∈ R, p * q = q * p := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  have htuR : ∀ {K : Subgroup Q}, K ≤ π.range → Nat.card π.range ≤ Nat.card K →
      (∀ p ∈ K, ∀ q ∈ K, p * q = q * p) → False := by
    intro K hK hcK hKc
    have hKeq : K = π.range := Subgroup.eq_of_le_of_card_ge hK hcK
    exact htu (hKc _ (hKeq ▸ ⟨t, rfl⟩) _ (hKeq ▸ ⟨u, rfl⟩))
  have hpos : 0 < Nat.card (B ⊓ D : Subgroup G) := Nat.card_pos
  have hdiv : Nat.card R = 1 ∨ Nat.card R = 2 ∨ Nat.card R = 4 ∨ Nat.card R = 8 := by
    have : Nat.card R ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hRdvd, by norm_num⟩
    have h8' : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [h8'] at this
    simpa using this
  rcases hdiv with h1 | h2 | h4 | h8R
  ·
    rw [h1, mul_one] at hsplit
    have hBD : B ⊓ D = B := Subgroup.eq_of_le_of_card_ge inf_le_left hsplit.le
    exact Subgroup.eq_of_le_of_card_ge (hBD ▸ inf_le_right) hcard.ge
  ·
    exfalso
    obtain ⟨q, hqR, hq1⟩ : ∃ q ∈ R, q ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).mpr hcon
      rw [this, Subgroup.card_bot] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨b, hb, rfl⟩ := hqR
    have := hA b hq1
    have := hcent b (Subgroup.mem_subgroupOf.mp hb)
    rw [h2] at hsplit
    omega
  ·
    exfalso
    have hzR : π z ∈ R := by
      by_contra hzR
      set K := Subgroup.closure ((R : Set Q) ∪ {π z}) with hK
      have hKc : ∀ p ∈ K, ∀ q ∈ K, p * q = q * p := by
        have hpw : ((R : Set Q) ∪ {π z}).Pairwise Commute := by
          intro p hp q hq _
          rcases hp with hp | hp <;> rcases hq with hq | hq
          · exact hRc p hp q hq
          · rw [Set.mem_singleton_iff.mp hq]
            obtain ⟨x, -, rfl⟩ := hp
            exact (hz x).symm
          · rw [Set.mem_singleton_iff.mp hp]
            obtain ⟨x, -, rfl⟩ := hq
            exact hz x
          · rw [Set.mem_singleton_iff.mp hp, Set.mem_singleton_iff.mp hq]
        intro p hp q hq
        exact congrArg Subtype.val
          ((Subgroup.isMulCommutative_closure hpw).is_comm.comm (⟨p, hp⟩ : K) ⟨q, hq⟩)
      have hKle : K ≤ π.range := by
        rw [hK, Subgroup.closure_le]
        rintro _ (hp | hp)
        · exact hRle hp
        · rw [Set.mem_singleton_iff.mp hp]
          exact ⟨z, rfl⟩
      have hRK : R < K := by
        refine lt_of_le_of_ne (fun p hp => Subgroup.subset_closure (Or.inl hp)) fun hRK => hzR ?_
        rw [hRK]
        exact Subgroup.subset_closure (Or.inr rfl)
      have hcardK : Nat.card R < Nat.card K := Subgroup.card_lt_of_lt hRK
      have hKdvd : Nat.card K ∣ 8 := h8 ▸ Subgroup.card_dvd_of_le hKle
      have hK8 : Nat.card K = 8 := by
        have : Nat.card K ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hKdvd, by norm_num⟩
        have h8' : Nat.divisors 8 = {1, 2, 4, 8} := by decide
        rw [h8'] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        omega
      exact htuR hKle (by omega) hKc
    obtain ⟨b, hb, hbz⟩ := hzR
    have := hB b hbz
    have := hcent b (Subgroup.mem_subgroupOf.mp hb)
    rw [h4] at hsplit
    omega
  ·
    exact (htuR hRle (by omega) hRc).elim

end Action

section Kernel

variable {G : Type} [Group G] [Finite G]

theorem mem_conjugate_iff_conj_mem {H : Subgroup G} {g z : G} :
    z ∈ CFSG.conjugate H g ↔ g * z * g⁻¹ ∈ H := by
  rw [CFSG.conjugate, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem mem_centralizer_of_odd {D : Subgroup G} (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hD2 : IsPGroup 2 D) {y : G} (hyN : y ∈ Subgroup.normalizer (D : Set G))
    (hyV : y ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hodd : Odd (orderOf y)) : y ∈ Subgroup.centralizer (D : Set G) := by
  have hconj : ∀ d ∈ D, y * d * y⁻¹ ∈ D := fun d hd => (Subgroup.mem_normalizer_iff.mp hyN d).mp hd
  have key : ∀ i : ℕ, ∀ d ∈ D, d ^ 2 ^ i = 1 → y * d * y⁻¹ = d := by
    intro i
    induction i with
    | zero =>
      intro d _ hd
      rw [pow_zero, pow_one] at hd
      rw [hd]
      group
    | succ i ih =>
      intro d hd hdi
      have hsq : y * (d * d) * y⁻¹ = d * d :=
        ih _ (mul_mem hd hd) (by rw [← pow_two, ← pow_mul, ← pow_succ']; exact hdi)
      set w := y * d * y⁻¹ * d⁻¹ with hw
      have hwD : w ∈ D := mul_mem (hconj d hd) (inv_mem hd)
      have hydD := hconj d hd
      have hw2 : w * w = 1 := by
        have hc : d⁻¹ * (y * d * y⁻¹) = (y * d * y⁻¹) * d⁻¹ := hD _ (inv_mem hd) _ hydD
        calc w * w = (y * d * y⁻¹) * (d⁻¹ * (y * d * y⁻¹)) * d⁻¹ := by rw [hw]; group
          _ = (y * d * y⁻¹) * ((y * d * y⁻¹) * d⁻¹) * d⁻¹ := by rw [hc]
          _ = y * (d * d) * y⁻¹ * (d * d)⁻¹ := by group
          _ = 1 := by rw [hsq, mul_inv_cancel]
      have hwy : y * w * y⁻¹ = w :=
        ((Subgroup.mem_centralizer_iff.mp hyV) w (mem_omegaIn_one_of_mul_self hwD hw2)).symm ▸
          (by group)
      have hpow : ∀ j : ℕ, y ^ j * d * (y ^ j)⁻¹ = w ^ j * d := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          calc y ^ (j + 1) * d * (y ^ (j + 1))⁻¹ = y * (y ^ j * d * (y ^ j)⁻¹) * y⁻¹ := by
                rw [pow_succ']; group
            _ = y * (w ^ j * d) * y⁻¹ := by rw [ihj]
            _ = (y * w * y⁻¹) ^ j * (y * d * y⁻¹) := by
                rw [conj_pow]
                group
            _ = w ^ (j + 1) * d := by
                rw [hwy, hw, pow_succ]
                group
      have hr := hpow (orderOf y)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hr
      obtain ⟨r, hr'⟩ := hodd
      have hw1 : w = 1 := by
        have : w ^ orderOf y = 1 := mul_right_cancel (hr.symm.trans (one_mul d).symm)
        rw [hr', pow_succ, pow_mul, show w ^ 2 = 1 by rw [pow_two, hw2], one_pow,
          one_mul] at this
        exact this
      calc y * d * y⁻¹ = w * d := by rw [hw]; group
        _ = d := by rw [hw1, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  obtain ⟨i, hi⟩ := hD2 ⟨d, hd⟩
  have hdi : d ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
  have := key i d hd hdi
  calc d * y = y * d * y⁻¹ * y := by rw [this]
    _ = y * d := by group

theorem mem_centralizer_of_mem_centralizer_omegaIn (S : Sylow 2 G) {D : Subgroup G}
    (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    (hR : (S : Subgroup G) ⊓ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D)
    (hwc : ∀ g : G, CFSG.conjugate D g ≤ S → CFSG.conjugate D g = D)
    {x : G} (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (hxV : x ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    x ∈ Subgroup.centralizer (D : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDS : D ≤ S := hR ▸ inf_le_left
  have hD2 : IsPGroup 2 D := S.isPGroup'.to_le hDS
  have h2part : ∀ y ∈ Subgroup.normalizer (D : Set G),
      y ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      ∀ a : ℕ, y ^ 2 ^ a = 1 → y ∈ D := by
    intro y hyN hyV a hya
    have hZ2 : IsPGroup 2 (Subgroup.zpowers y) := fun g => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨a, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hya, one_zpow]
    have hQ : IsPGroup 2 (D ⊔ Subgroup.zpowers y : Subgroup G) :=
      hD2.to_sup_of_normal_left' hZ2 ((Subgroup.zpowers_le).mpr hyN)
    obtain ⟨S₁, hS₁⟩ := hQ.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S₁
    have hmem : ∀ z ∈ (S₁ : Subgroup G), g⁻¹ * z * g ∈ (S : Subgroup G) := by
      intro z hz
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz
      simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hz
    have hgD : CFSG.conjugate D g = D := by
      apply hwc
      rintro _ ⟨d, hd, rfl⟩
      simpa [MulAut.conj_apply] using hmem d (hS₁ (Subgroup.mem_sup_left hd))
    have hgN : g⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro d
      rw [inv_inv]
      constructor
      · intro hd
        have : g⁻¹ * d * g ∈ CFSG.conjugate D g :=
          mem_conjugate_iff_conj_mem.mpr (by simpa [mul_assoc] using hd)
        rwa [hgD] at this
      · intro hd
        rw [← hgD, mem_conjugate_iff_conj_mem] at hd
        simpa [mul_assoc] using hd
    have hyS : g⁻¹ * y * g ∈ (S : Subgroup G) :=
      hmem y (hS₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
    have hyV' : g⁻¹ * y * g ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : g * v * g⁻¹ ∈ omegaIn 1 D := by
        have := conj_mem_omegaIn_one (g := g⁻¹) hgN hv
        simpa using this
      have hc := (Subgroup.mem_centralizer_iff.mp hyV) _ hv'
      calc v * (g⁻¹ * y * g) = g⁻¹ * ((g * v * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * v * g⁻¹)) * g := by rw [hc]
        _ = g⁻¹ * y * g * v := by group
    have hyD : g⁻¹ * y * g ∈ D := by
      rw [← hR]
      exact Subgroup.mem_inf.mpr ⟨hyS, hyV'⟩
    exact (Subgroup.mem_normalizer_iff.mp hgN y).mpr (by simpa using hyD)
  have ho : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, r, hr, hxr⟩ := Nat.exists_eq_two_pow_mul_odd ho
  have hx2 : x ^ r ∈ D := by
    refine h2part _ (pow_mem hxN r) (pow_mem hxV r) a ?_
    rw [← pow_mul, mul_comm, ← hxr, pow_orderOf_eq_one]
  have hxodd : x ^ 2 ^ a ∈ Subgroup.centralizer (D : Set G) := by
    refine mem_centralizer_of_odd hD hD2 (pow_mem hxN _) (pow_mem hxV _) ?_
    rw [orderOf_pow_of_dvd (by positivity) (hxr ▸ dvd_mul_right _ _), hxr,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hr
  have hcop : Nat.Coprime r (2 ^ a) := Nat.Coprime.pow_right a hr.coprime_two_right
  have hbez := Nat.gcd_eq_gcd_ab r (2 ^ a)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  have hxeq : x = (x ^ r) ^ (Nat.gcdA r (2 ^ a)) * (x ^ 2 ^ a) ^ (Nat.gcdB r (2 ^ a)) := by
    conv_lhs => rw [← zpow_one x, hbez]
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [hxeq]
  have hDC : D ≤ Subgroup.centralizer (D : Set G) := fun d hd => Subgroup.mem_centralizer_iff.mpr
    fun d' hd' => hD _ hd' _ hd
  exact mul_mem (zpow_mem (hDC hx2) _) (zpow_mem hxodd _)

theorem seven_dvd_index_of_transitive {N V : Subgroup G} (hVN : V ≤ N)
    (hNV : ∀ n ∈ N, ∀ v ∈ V, n * v * n⁻¹ ∈ V) (h8 : Nat.card V = 8)
    (htr : ∀ x ∈ V, ∀ y ∈ V, x ≠ 1 → y ≠ 1 → ∃ n ∈ N, n * x * n⁻¹ = y) :
    7 ∣ ((Subgroup.centralizer (V : Set G)).subgroupOf N).index := by
  obtain ⟨x₀, hx₀, hx₀1⟩ : ∃ x ∈ V, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hcon
    rw [this, Subgroup.card_bot] at h8
    exact absurd h8 (by norm_num)
  set x : N := ⟨x₀, hVN hx₀⟩ with hx
  have hle : (Subgroup.centralizer (V : Set G)).subgroupOf N ≤ Subgroup.centralizer {x} := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hn)) x₀ hx₀
    simpa [hx] using this.symm
  have hconj : conjugatesOf x = Subtype.val ⁻¹' ((V : Set G) \ {1}) := by
    ext y
    simp only [conjugatesOf, Set.mem_setOf_eq, isConj_iff, Set.mem_preimage, Set.mem_diff,
      SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [hx] using hNV c c.2 x₀ hx₀
      · intro h1
        apply hx₀1
        have : (c : G) * x₀ * (c : G)⁻¹ = 1 := by simpa [hx] using h1
        calc x₀ = (c : G)⁻¹ * ((c : G) * x₀ * (c : G)⁻¹) * c := by group
          _ = 1 := by rw [this]; group
    · rintro ⟨hyV, hy1⟩
      obtain ⟨n, hn, hny⟩ := htr x₀ hx₀ y hyV hx₀1 hy1
      exact ⟨⟨n, hn⟩, Subtype.ext (by simpa [hx] using hny)⟩
  have h7 : (Subgroup.centralizer {x}).index = 7 := by
    rw [Subgroup.index_centralizer_eq_ncard, hconj,
      Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
        (fun v hv => ⟨⟨v, hVN hv.1⟩, rfl⟩),
      Set.ncard_sdiff_singleton_of_mem (show (1 : G) ∈ (V : Set G) from V.one_mem)]
    rw [← Nat.card_coe_set_eq]
    change Nat.card V - 1 = 7
    rw [h8]
  rw [← h7]
  exact Subgroup.index_dvd_of_le hle

end Kernel

section Core

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_normalizer_omegaIn (D : Subgroup G) :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    simpa using conj_mem_omegaIn_one (g := g⁻¹) (inv_mem hg) hv
  · intro hv
    simpa [mul_assoc] using conj_mem_omegaIn_one hg hv

theorem card_fixed_uv_of_k_eq_two {τ : StrothTypeIndex} (hτ : τ.k 0 = τ.k 1) (h2 : τ.k 1 = 2) :
    Nat.card {v : Torus τ.k // τ.action.φuv v = v} = 8 := by
  cases τ with
  | t300 n' =>
    obtain rfl : n' = 2 := h2
    exact card_fixed_uv_t300_two
  | t310 m hm =>
    obtain rfl : m = 2 := h2
    exact card_fixed_uv_t310_two
  | t320 m hm =>
    exact absurd (show m = 2 from h2) (by omega)
  | t330 m hm =>
    exact absurd (show m = 2 from h2) (by omega)
  | t321 => exact absurd h2 (by decide)
  | t331 => exact absurd h2 (by decide)
  | _ =>
    exfalso
    simp [StrothTypeIndex.k, Type100.k, Type101.k, Type110.k, Type111.k, Type120.k, Type121.k,
      Type130.k, Type131.k, Type200.k, Type201.k, Type210.k, Type211.k, Type220.k, Type221.k,
      Type230.k, Type231.k] at hτ

theorem exists_gl32_of_stroth41 {D : Subgroup G} {uv t u : G} {τ : StrothTypeIndex}
    (hτ : τ.k 0 = τ.k 1) (hn : 2 ≤ τ.k 1) (e : Additive D ≃+ Torus τ.k)
    (huv : uv ∈ Subgroup.normalizer (D : Set G))
    (huv_conj : ∀ x : D, e (Additive.ofMul (conjBy huv x)) = τ.action.φuv (e (Additive.ofMul x)))
    (huvt : uv * t = t * uv) (huvu : uv * u = u * uv) (htu : t * u = u * uv * t)
    (S : Sylow 2 G) (huvS : uv ∈ (S : Subgroup G)) (htS : t ∈ (S : Subgroup G))
    (huS : u ∈ (S : Subgroup G))
    (huvV : uv ∉ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hR : (S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D)
    (hall : ∀ x ∈ omegaIn 1 D, ∀ y ∈ omegaIn 1 D, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    (S : Subgroup G) = D ⊔ Subgroup.closure {uv, t, u} ∧
      ∃ φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
          (Subgroup.normalizer (D : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n := τ.k 1 with hndef
  have hk : ∀ i, τ.k i = n := by
    have h21 : τ.k 2 = τ.k 1 := by cases τ <;> rfl
    intro i
    fin_cases i
    exacts [hτ, rfl, h21]
  set V := omegaIn 1 D with hVdef
  have hD := comm_of_torus e
  have hV8 : Nat.card V = 8 := card_omegaIn_one_eq_eight e (fun i => by rw [hk]; omega)
  have hVab : CFSG.Open.IsElemAbelian 2 V := isElemAbelian_omegaIn_one hD
  have hNDV := normalizer_le_normalizer_omegaIn D
  have hSV : (S : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := hSN.trans hNDV
  have hRS : (S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G) = D := by
    rwa [inf_eq_left.mpr hSN] at hR
  have hDS : D ≤ S := hRS ▸ inf_le_left
  obtain ⟨h8, hSsup⟩ :=
    card_map_eq_eight_and_eq_sup S.isPGroup' hVab hV8 hSV huvS htS huS huvu htu huvV
  have hS : (S : Subgroup G) = D ⊔ Subgroup.closure {uv, t, u} := by
    rw [hRS] at hSsup
    exact hSsup
  refine ⟨hS, ?_⟩
  set π : (S : Subgroup G) →* MulAut V := V.normalizerMonoidHom.comp (Subgroup.inclusion hSV)
    with hπdef
  have hπ : ∀ s : (S : Subgroup G), π s = 1 ↔ (s : G) ∈ D := fun s => by
    rw [hπdef, MonoidHom.comp_apply, normalizerMonoidHom_eq_one_iff, ← hRS]
    exact ⟨fun h => Subgroup.mem_inf.mpr ⟨s.2, h⟩, fun h => (Subgroup.mem_inf.mp h).2⟩
  have hπ8 : Nat.card π.range = 8 := by
    rw [hπdef, MonoidHom.range_comp, Subgroup.inclusion_range]
    exact h8
  have htu' : π ⟨t, htS⟩ * π ⟨u, huS⟩ ≠ π ⟨u, huS⟩ * π ⟨t, htS⟩ :=
    normalizerMonoidHom_mul_ne (hSV htS) (hSV huS) huvu htu huvV
  have hz : ∀ s : (S : Subgroup G), π ⟨uv, huvS⟩ * π s = π s * π ⟨uv, huvS⟩ := by
    set c := π ⟨uv, huvS⟩ with hc
    let X : Subgroup G := ((Subgroup.centralizer {c}).comap π).map (S : Subgroup G).subtype
    have hmemX : ∀ (x : G) (hx : x ∈ (S : Subgroup G)), c * π ⟨x, hx⟩ = π ⟨x, hx⟩ * c →
        x ∈ X := fun x hx h =>
      ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_singleton_iff.mpr h.symm), rfl⟩
    have hDX : D ≤ X := fun d hd =>
      hmemX d (hDS hd) (by rw [(hπ ⟨d, hDS hd⟩).mpr hd, mul_one, one_mul])
    have hWX : Subgroup.closure {uv, t, u} ≤ X := by
      rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hmemX _ huvS rfl
      · refine hmemX _ htS ?_
        rw [hc, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext huvt
      · refine hmemX _ huS ?_
        rw [hc, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext huvu
    rintro ⟨x, hxS⟩
    have hsX : x ∈ X := by
      have h : x ∈ D ⊔ Subgroup.closure {uv, t, u} := hS ▸ hxS
      exact sup_le hDX hWX h
    obtain ⟨s', hs', hss'⟩ := hsX
    obtain rfl : s' = ⟨x, hxS⟩ := Subtype.ext hss'
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp hs')).symm
  have hexp : ∀ y ∈ D, y ^ 2 ^ n = 1 := fun y hy => pow_two_pow_eq_one_of_torus e hk hy
  have hroot' : ∀ x ∈ D, x * x = 1 → ∃ y ∈ D, y ^ 2 ^ (n - 1) = x :=
    fun x hx hx2 => exists_pow_eq_of_mul_self_of_torus e hk hx hx2
  have hroot : ∀ x ∈ D, x * x = 1 → ∃ y ∈ D, y * y = x :=
    fun x hx hx2 => exists_mul_self_eq_of_torus e hk hn hx hx2
  have hF1 : 8 * Nat.card (D ⊓ Subgroup.centralizer {uv} : Subgroup G) ≤ Nat.card D := by
    rcases (show 3 ≤ n ∨ n = 2 by omega) with h3 | h2
    · exact eight_mul_card_le_of_not_mem_centralizer hD huv h3 hexp hroot' huvV
    · rw [card_inf_centralizer_eq_card_fixed e huv huv_conj, card_fixed_uv_of_k_eq_two hτ h2]
      have hcardD : Nat.card D = 64 := by
        rw [show Nat.card D = Nat.card (Torus τ.k) from
          (Nat.card_congr Additive.ofMul).trans (Nat.card_congr e.toEquiv), natCard_torus,
          hk 0, hk 1, hk 2, h2]
        norm_num
      rw [hcardD]
  have hA : ∀ b : (S : Subgroup G), π b ≠ 1 →
      2 * Nat.card (D ⊓ Subgroup.centralizer {(b : G)} : Subgroup G) < Nat.card D := by
    intro b hb
    by_contra hle
    push Not at hle
    apply hb
    exact (normalizerMonoidHom_eq_one_iff _).mpr
      (mem_centralizer_omegaIn_of_card_le hD (hSN b.2) hroot hle)
  have hB : ∀ b : (S : Subgroup G), π b = π ⟨uv, huvS⟩ →
      4 * Nat.card (D ⊓ Subgroup.centralizer {(b : G)} : Subgroup G) < Nat.card D := by
    intro b hb
    have hd : uv⁻¹ * (b : G) ∈ D := by
      have h1 : π (⟨uv, huvS⟩⁻¹ * b) = 1 := by rw [map_mul, map_inv, hb, inv_mul_cancel]
      simpa using (hπ _).mp h1
    have hcent : D ⊓ Subgroup.centralizer {(b : G)} = D ⊓ Subgroup.centralizer {uv} := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      refine and_congr_right fun hx => ?_
      have hbe : (b : G) = uv * (uv⁻¹ * b) := by group
      have hxd : x * (uv⁻¹ * b) = (uv⁻¹ * b) * x := hD _ hx _ hd
      constructor
      · intro h
        apply mul_right_cancel (b := uv⁻¹ * (b : G))
        calc x * uv * (uv⁻¹ * b) = x * b := by group
          _ = b * x := h
          _ = uv * ((uv⁻¹ * b) * x) := by group
          _ = uv * x * (uv⁻¹ * b) := by rw [← hxd]; group
      · intro h
        calc x * (b : G) = x * uv * (uv⁻¹ * b) := by group
          _ = uv * x * (uv⁻¹ * b) := by rw [h]
          _ = uv * (x * (uv⁻¹ * b)) := by group
          _ = uv * ((uv⁻¹ * b) * x) := by rw [hxd]
          _ = b * x := by group
    rw [hcent]
    have hpos : 0 < Nat.card (D ⊓ Subgroup.centralizer {uv} : Subgroup G) := Nat.card_pos
    omega
  have hwc : ∀ g : G, CFSG.conjugate D g ≤ S → CFSG.conjugate D g = D := by
    intro g hg
    refine eq_of_isMulCommutative_of_card_eq π hπ hπ8 htu' hz hA hB hg ?_ ?_
    · intro x hx y hy
      rw [mem_conjugate_iff_conj_mem] at hx hy
      have h := hD _ hx _ hy
      have h' : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
          _ = (g * y * g⁻¹) * (g * x * g⁻¹) := h
          _ = g * (y * x) * g⁻¹ := by group
      simpa using h'
    · exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have htr : ∀ x ∈ V, ∀ y ∈ V, x ≠ 1 → y ≠ 1 →
      ∃ m ∈ Subgroup.normalizer (D : Set G), m * x * m⁻¹ = y := by
    intro x hx y hy hx1 hy1
    have hox : orderOf x = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact mul_self_eq_one_of_mem_omegaIn_one hD hx) hx1
    have hoy : orderOf y = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact mul_self_eq_one_of_mem_omegaIn_one hD hy) hy1
    obtain ⟨c, hc⟩ := isConj_iff.mp (hall x hx y hy hox hoy)
    obtain ⟨m, hm, hmx⟩ := CFSG.GF2Type.Aschbacher1976Full.HS.burnside_fusion S D hDS hD hwc
      (omegaIn_le 1 D hx) (hc ▸ omegaIn_le 1 D hy)
    exact ⟨m, hm, hmx.trans hc⟩
  obtain ⟨eGL⟩ := CFSG.ComponentClassification.GHarris.nonempty_mulAut_equiv_GL32 hVab hV8
  set ψ : Subgroup.normalizer (D : Set G) →* MulAut V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion hNDV) with hψdef
  have hkerV : (eGL.toMonoidHom.comp ψ).ker =
      (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (D : Set G)) := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, hψdef, MonoidHom.comp_apply, normalizerMonoidHom_eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl
  refine ⟨eGL.toMonoidHom.comp ψ, ?_, ?_⟩
  ·
    have h7 : 7 ∣ Nat.card (eGL.toMonoidHom.comp ψ).range := by
      rw [← Subgroup.index_ker, hkerV]
      refine seven_dvd_index_of_transitive ((omegaIn_le 1 D).trans Subgroup.le_normalizer)
        (fun m hm v hv => (Subgroup.mem_normalizer_iff.mp (hNDV hm) v).mp hv) hV8 htr
    have h8' : 8 ∣ Nat.card (eGL.toMonoidHom.comp ψ).range := by
      have hmapS : ((S : Subgroup G).subgroupOf (Subgroup.normalizer (D : Set G))).map ψ =
          ((S : Subgroup G).subgroupOf (Subgroup.normalizer (V : Set G))).map
            V.normalizerMonoidHom := by
        rw [hψdef, ← Subgroup.map_map]
        congr 1
        ext y
        simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact hx
        · intro hy
          exact ⟨⟨y, hSN hy⟩, hy, rfl⟩
      have hcard : Nat.card (((S : Subgroup G).subgroupOf
          (Subgroup.normalizer (D : Set G))).map (eGL.toMonoidHom.comp ψ)) = 8 := by
        rw [← Subgroup.map_map, Subgroup.card_map_of_injective eGL.injective, hmapS]
        exact h8
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (Subgroup.map_le_range _ _)
    have h56 : 56 ∣ Nat.card (eGL.toMonoidHom.comp ψ).range :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h7 h8'
    have htop := CFSG.ComponentClassification.GHarris.eq_top_of_dvd_card_GL32 h56
    intro M
    have hM : M ∈ (eGL.toMonoidHom.comp ψ).range := htop ▸ Subgroup.mem_top M
    exact hM
  ·
    rw [hkerV]
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact mem_centralizer_of_mem_centralizer_omegaIn S hD hRS hwc x.2 hx
    · intro hx
      exact Subgroup.centralizer_le (omegaIn_le 1 D) hx

end Core

end CFSG.CGT.Stroth77
