module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

namespace W192

open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def bAct (v : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 := (v.2, v.2 - v.1)

@[expose] def aAct (v : ZMod 4 × ZMod 4) : ZMod 4 × ZMod 4 := (v.2, v.1)

@[expose] def bPow : ℕ → ZMod 4 × ZMod 4 → ZMod 4 × ZMod 4
  | 0, v => v
  | k + 1, v => bAct (bPow k v)

@[expose] def dAct : DihedralGroup 6 → ZMod 4 × ZMod 4 → ZMod 4 × ZMod 4
  | .r i, v => bPow i.val v
  | .sr i, v => aAct (bPow i.val v)

theorem dAct_one (v : ZMod 4 × ZMod 4) : dAct 1 v = v := rfl

theorem dAct_mul : ∀ (d e : DihedralGroup 6) (v : ZMod 4 × ZMod 4),
    dAct (d * e) v = dAct d (dAct e v) := by
  decide

theorem dAct_inv_left : ∀ (d : DihedralGroup 6) (v : ZMod 4 × ZMod 4), dAct d⁻¹ (dAct d v) = v := by
  decide

theorem dAct_inv_right : ∀ (d : DihedralGroup 6) (v : ZMod 4 × ZMod 4), dAct d (dAct d⁻¹ v) = v := by
  decide

theorem dAct_add : ∀ (d : DihedralGroup 6) (v w : ZMod 4 × ZMod 4),
    dAct d (v + w) = dAct d v + dAct d w := by
  decide

@[expose] def actAut (d : DihedralGroup 6) : MulAut (Multiplicative (ZMod 4 × ZMod 4)) where
  toFun v := Multiplicative.ofAdd (dAct d (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd (dAct d⁻¹ (Multiplicative.toAdd v))
  left_inv v := dAct_inv_left d v
  right_inv v := dAct_inv_right d v
  map_mul' v w := dAct_add d v w

@[expose] def act : DihedralGroup 6 →* MulAut (Multiplicative (ZMod 4 × ZMod 4)) where
  toFun := actAut
  map_one' := MulEquiv.ext fun v => dAct_one v
  map_mul' d e := MulEquiv.ext fun v => dAct_mul d e v

end W192

open W192 in
abbrev G192 : Type := Multiplicative (ZMod 4 × ZMod 4) ⋊[act] DihedralGroup 6

instance : Fintype G192 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

namespace W192

open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def w192W : Subgroup G192 := (SemidirectProduct.inl : Multiplicative (ZMod 4 × ZMod 4) →* G192).range

theorem mem_w192W {x : G192} : x ∈ w192W ↔ x.right = 1 := by
  constructor
  · rintro ⟨n, rfl⟩
    rfl
  · intro h
    exact ⟨x.left, SemidirectProduct.ext rfl h.symm⟩

@[expose] noncomputable def w192WEquiv : ↥w192W ≃* Multiplicative (ZMod 4 × ZMod 4) :=
  (MonoidHom.ofInjective SemidirectProduct.inl_injective).symm

instance : w192W.Normal := by
  rw [w192W, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem w192_card : Nat.card G192 = 192 := by
  rw [SemidirectProduct.card, DihedralGroup.nat_card, Nat.card_eq_fintype_card]
  rfl

set_option synthInstance.maxSize 1000 in
theorem w192_center_dec : ∀ x : G192, (∀ y : G192, x * y = y * x) → x = 1 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem w192_four_three_dec :
    ∀ k d : G192, k ^ 4 = 1 → k ^ 2 ≠ 1 → d ^ 3 = 1 → d ≠ 1 → k * d ≠ d * k := by
  decide +kernel

@[expose] def q8Reps : Finset (G192 × G192) :=
  {((⟨Multiplicative.ofAdd ((0 : ZMod 4), (1 : ZMod 4)), DihedralGroup.r 0⟩ : G192),
      (⟨Multiplicative.ofAdd ((2 : ZMod 4), (0 : ZMod 4)), DihedralGroup.sr 5⟩ : G192)),
    ((⟨Multiplicative.ofAdd ((0 : ZMod 4), (1 : ZMod 4)), DihedralGroup.sr 2⟩ : G192),
      (⟨Multiplicative.ofAdd ((2 : ZMod 4), (0 : ZMod 4)), DihedralGroup.sr 2⟩ : G192)),
    ((⟨Multiplicative.ofAdd ((0 : ZMod 4), (1 : ZMod 4)), DihedralGroup.sr 2⟩ : G192),
      (⟨Multiplicative.ofAdd ((2 : ZMod 4), (1 : ZMod 4)), DihedralGroup.r 0⟩ : G192)),
    ((⟨Multiplicative.ofAdd ((0 : ZMod 4), (2 : ZMod 4)), DihedralGroup.sr 1⟩ : G192),
      (⟨Multiplicative.ofAdd ((1 : ZMod 4), (0 : ZMod 4)), DihedralGroup.r 0⟩ : G192)),
    ((⟨Multiplicative.ofAdd ((0 : ZMod 4), (2 : ZMod 4)), DihedralGroup.sr 1⟩ : G192),
      (⟨Multiplicative.ofAdd ((1 : ZMod 4), (2 : ZMod 4)), DihedralGroup.sr 1⟩ : G192)),
    ((⟨Multiplicative.ofAdd ((1 : ZMod 4), (2 : ZMod 4)), DihedralGroup.r 0⟩ : G192),
      (⟨Multiplicative.ofAdd ((0 : ZMod 4), (2 : ZMod 4)), DihedralGroup.sr 4⟩ : G192))}

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000 in
theorem w192_q8_reps_dec : ∀ a b : G192, a ^ 2 ≠ 1 → a ^ 4 = 1 → b * b = a * a →
    b * a * b⁻¹ = a⁻¹ → ∃ g : G192, (g * a * g⁻¹, g * b * g⁻¹) ∈ q8Reps := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000 in
theorem w192_q8_rep_cent_dec : ∀ p ∈ q8Reps, ∀ y : G192, y * y = 1 →
    ∃ x : G192, ∃ k ∈ ({p.1, p.2, p.1 * p.2} : Finset G192), y * (x * k * x⁻¹) = x * k * x⁻¹ * y := by
  decide +kernel

theorem w192_q8_dec : ∀ a b y : G192, a ^ 2 ≠ 1 → a ^ 4 = 1 → b * b = a * a → b * a * b⁻¹ = a⁻¹ →
    y * y = 1 → ∃ x : G192, ∃ k ∈ ({a, b, a * b} : Finset G192),
      y * (x * k * x⁻¹) = x * k * x⁻¹ * y := by
  intro a b y h1 h2 h3 h4 hy
  obtain ⟨g, hg⟩ := w192_q8_reps_dec a b h1 h2 h3 h4
  have hy' : (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
    calc (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      _ = 1 := by rw [hy]; group
  obtain ⟨x, k, hk, hc⟩ := w192_q8_rep_cent_dec _ hg _ hy'
  refine ⟨g⁻¹ * x * g, g⁻¹ * k * g, ?_, ?_⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
    rcases hk with rfl | rfl | rfl
    · left
      group
    · right
      left
      group
    · right
      right
      group
  · calc y * (g⁻¹ * x * g * (g⁻¹ * k * g) * (g⁻¹ * x * g)⁻¹)
        = g⁻¹ * ((g * y * g⁻¹) * (x * k * x⁻¹)) * g := by group
      _ = g⁻¹ * ((x * k * x⁻¹) * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * x * g * (g⁻¹ * k * g) * (g⁻¹ * x * g)⁻¹ * y := by group

set_option synthInstance.maxSize 1000 in
theorem w192_q8_sq_dec : ∀ a b : G192, a ^ 2 ≠ 1 → a ^ 4 = 1 → b * b = a * a → b * a * b⁻¹ = a⁻¹ →
    (a * a).right = 1 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem w192_W_conj_dec : ∀ a b : G192, a.right = 1 → b.right = 1 → a * a = 1 → b * b = 1 → a ≠ 1 →
    b ≠ 1 → ∃ x : G192, x * a * x⁻¹ = b := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem w192_odd_dec : ∀ x : G192, x ^ 3 = 1 →
    x.right ∈ ({DihedralGroup.r 0, DihedralGroup.r 2, DihedralGroup.r 4} : Finset (DihedralGroup 6)) := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem w192_two_dec : ∀ x : G192,
    x.right ∈ ({DihedralGroup.r 0, DihedralGroup.r 2, DihedralGroup.r 4} : Finset (DihedralGroup 6)) →
    x ^ 64 = 1 → x.right = 1 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem w192_W_prod_dec : ∀ w : G192, w.right = 1 → ∃ y : G192, y ^ 3 = 1 ∧ (y⁻¹ * w) ^ 3 = 1 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem z4_fix_dec : ∀ p q : ZMod 4 × ZMod 4,
    (∀ v : ZMod 4 × ZMod 4, (v.1 • p + v.2 • q).1 • p + (v.1 • p + v.2 • q).2 • q = v) →
    4 ≤ (Finset.univ.filter fun v : ZMod 4 × ZMod 4 => v.1 • p + v.2 • q = v).card := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem gl24_d12_dec : ∀ A' B' : Matrix (Fin 2) (Fin 2) (ZMod 4), A' * A' = 1 → B' ^ 6 = 1 →
    A' * B' * A' * B' = 1 → B' ^ 2 ≠ 1 → B' ^ 3 ≠ 1 →
    ∃ P : Matrix (Fin 2) (Fin 2) (ZMod 4), (P.det = 1 ∨ P.det = 3) ∧
      ∃ i ∈ ({1, 5} : Finset ℕ), ∃ j ∈ Finset.range 6,
        P * B' = !![0, 1; -1, 1] ^ i * P ∧ P * A' = (!![0, 1; 1, 0] * !![0, 1; -1, 1] ^ j) * P := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem gl24_three_fpf_dec : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 4), M ^ 3 = 1 → M ≠ 1 →
    ∀ v : Fin 2 → ZMod 4, M.mulVec v = v → v = 0 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem w192_W_pow_four : ∀ w : G192, w.right = 1 → w ^ 4 = 1 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
private theorem r2_closed : ∀ d e : DihedralGroup 6,
    d ∈ ({DihedralGroup.r 0, DihedralGroup.r 2, DihedralGroup.r 4} : Finset (DihedralGroup 6)) →
    e ∈ ({DihedralGroup.r 0, DihedralGroup.r 2, DihedralGroup.r 4} : Finset (DihedralGroup 6)) →
    d * e⁻¹ ∈ ({DihedralGroup.r 0, DihedralGroup.r 2, DihedralGroup.r 4} : Finset (DihedralGroup 6)) := by
  decide

private def o2Sub : Subgroup G192 :=
  Subgroup.ofDiv {x : G192 | x.right ∈ ({DihedralGroup.r 0, DihedralGroup.r 2, DihedralGroup.r 4} :
      Finset (DihedralGroup 6))} ⟨1, by decide⟩ fun x hx y hy => by
    show (x * y⁻¹).right ∈ ({DihedralGroup.r 0, DihedralGroup.r 2, DihedralGroup.r 4} :
      Finset (DihedralGroup 6))
    rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    exact r2_closed _ _ hx hy

private theorem pow_three_of_odd {x : G192} (h : Odd (orderOf x)) : x ^ 3 = 1 := by
  have h1 : orderOf x ∣ 2 ^ 6 * 3 := by
    have := orderOf_dvd_natCard x
    rwa [w192_card] at this
  exact orderOf_dvd_iff_pow_eq_one.mp (((Odd.coprime_two_right h).pow_right 6).dvd_of_dvd_mul_left h1)

private theorem pow_sixtyfour_of_two {x : G192} {k : ℕ} (h : x ^ 2 ^ k = 1) : x ^ 64 = 1 := by
  have h1 : orderOf x ∣ 2 ^ 6 * 3 := by
    have := orderOf_dvd_natCard x
    rwa [w192_card] at this
  have h2 : Nat.Coprime (orderOf x) 3 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h)
      (Nat.Coprime.pow_left k (by norm_num))
  exact orderOf_dvd_iff_pow_eq_one.mp (h2.dvd_of_dvd_mul_right h1)

private theorem q8_rel {P : Subgroup G192} (e : ↥P ≃* QuaternionGroup 2) :
    let φ : QuaternionGroup 2 →* G192 := P.subtype.comp e.symm.toMonoidHom
    φ (QuaternionGroup.a 1) ^ 2 ≠ 1 ∧ φ (QuaternionGroup.a 1) ^ 4 = 1 ∧
      φ (QuaternionGroup.xa 0) * φ (QuaternionGroup.xa 0) =
        φ (QuaternionGroup.a 1) * φ (QuaternionGroup.a 1) ∧
      φ (QuaternionGroup.xa 0) * φ (QuaternionGroup.a 1) * (φ (QuaternionGroup.xa 0))⁻¹ =
        (φ (QuaternionGroup.a 1))⁻¹ := by
  intro φ
  have hφ : Function.Injective φ := P.subtype_injective.comp e.symm.injective
  refine ⟨fun h => ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ← map_one φ] at h
    exact absurd (hφ h) (by decide)
  · rw [← map_pow, show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one]
  · rw [← map_mul, ← map_mul,
      show (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.a 1 * QuaternionGroup.a 1 by decide]
  · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv,
      show (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.a 1 * (QuaternionGroup.xa 0)⁻¹ =
        (QuaternionGroup.a 1)⁻¹ by decide]

theorem w192_center_eq_bot : Subgroup.center G192 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact w192_center_dec x fun y => (Subgroup.mem_center_iff.mp hx y).symm

theorem w192_not_commute_four_three (k d : G192) (hk : orderOf k = 4) (hd : orderOf d = 3) :
    k * d ≠ d * k := by
  refine w192_four_three_dec k d (orderOf_dvd_iff_pow_eq_one.mp (by rw [hk])) (fun h => ?_)
    (orderOf_dvd_iff_pow_eq_one.mp (by rw [hd])) (fun h => ?_)
  · have := orderOf_dvd_of_pow_eq_one h
    rw [hk] at this
    norm_num at this
  · rw [h, orderOf_one] at hd
    norm_num at hd

theorem w192_involution_cent_order_four {P : Subgroup G192} (hP : Nonempty (↥P ≃* QuaternionGroup 2))
    {y : G192} (hy : y * y = 1) :
    ∃ x k : G192, k ∈ P ∧ orderOf k = 4 ∧ y * (x * k * x⁻¹) = x * k * x⁻¹ * y := by
  obtain ⟨e⟩ := hP
  set φ : QuaternionGroup 2 →* G192 := P.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := P.subtype_injective.comp e.symm.injective
  have hφP : ∀ q, φ q ∈ P := fun q => (e.symm q).2
  obtain ⟨h1, h2, h3, h4⟩ := q8_rel e
  obtain ⟨x, k, hk, hc⟩ := w192_q8_dec _ _ y h1 h2 h3 h4 hy
  refine ⟨x, k, ?_, ?_, hc⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact hφP _
    · exact hφP _
    · exact P.mul_mem (hφP _) (hφP _)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · rw [orderOf_injective φ hφ, QuaternionGroup.orderOf_a_one]
    · rw [orderOf_injective φ hφ, QuaternionGroup.orderOf_xa]
    · rw [← map_mul, orderOf_injective φ hφ, QuaternionGroup.a_mul_xa, QuaternionGroup.orderOf_xa]

theorem w192_q8_inv_mem {P : Subgroup G192} (hP : Nonempty (↥P ≃* QuaternionGroup 2)) {y : G192}
    (hyP : y ∈ P) (hy2 : y * y = 1) : y ∈ w192W := by
  obtain ⟨e⟩ := hP
  set φ : QuaternionGroup 2 →* G192 := P.subtype.comp e.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := P.subtype_injective.comp e.symm.injective
  obtain ⟨h1, h2, h3, h4⟩ := q8_rel e
  have hsq := w192_q8_sq_dec _ _ h1 h2 h3 h4
  have hy : y = φ (e ⟨y, hyP⟩) := by simp [hφdef]
  have hq2 : e ⟨y, hyP⟩ * e ⟨y, hyP⟩ = 1 := by
    apply hφ
    rw [map_mul, ← hy, hy2, map_one]
  have key : ∀ q : QuaternionGroup 2, q * q = 1 → q = 1 ∨ q = QuaternionGroup.a 1 * QuaternionGroup.a 1 := by
    decide
  rcases key _ hq2 with h | h
  · rw [hy, h, map_one]
    exact w192W.one_mem
  · rw [hy, h, map_mul]
    exact mem_w192W.mpr hsq

theorem w192_W_inv_conj {a b : G192} (ha : a ∈ w192W) (hb : b ∈ w192W) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : ∃ x : G192, x * a * x⁻¹ = b :=
  w192_W_conj_dec a b (mem_w192W.mp ha) (mem_w192W.mp hb) ha2 hb2 ha1 hb1

theorem w192_oUpperTwoPrime_oUpperTwo :
    oUpperTwoPrime (oUpperTwo (⊤ : Subgroup G192)) = w192W := by
  have hO2 : oUpperTwo (⊤ : Subgroup G192) ≤ o2Sub := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨-, hx⟩
    exact w192_odd_dec x (pow_three_of_odd hx)
  refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun w hw => ?_
  · rintro x ⟨hx, k, hk⟩
    exact mem_w192W.mpr (w192_two_dec x (hO2 hx) (pow_sixtyfour_of_two hk))
  · have hw1 := mem_w192W.mp hw
    obtain ⟨y, hy3, hyw⟩ := w192_W_prod_dec w hw1
    have hodd : ∀ c : G192, c ^ 3 = 1 → c ∈ oUpperTwo (⊤ : Subgroup G192) := by
      intro c hc
      refine Subgroup.subset_closure ⟨Subgroup.mem_top c, ?_⟩
      exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hc)
    have hwO : w ∈ oUpperTwo (⊤ : Subgroup G192) := by
      have := (oUpperTwo (⊤ : Subgroup G192)).mul_mem (hodd y hy3) (hodd _ hyw)
      rwa [mul_inv_cancel_left] at this
    exact Subgroup.subset_closure ⟨hwO, 2, w192_W_pow_four w hw1⟩

@[expose] def g1 : G192 := ⟨Multiplicative.ofAdd ((0 : ZMod 4), (0 : ZMod 4)), DihedralGroup.r 1⟩

@[expose] def g2 : G192 := ⟨Multiplicative.ofAdd ((0 : ZMod 4), (1 : ZMod 4)), DihedralGroup.sr 5⟩

@[expose] def h1 : G192 := ⟨Multiplicative.ofAdd ((1 : ZMod 4), (2 : ZMod 4)), DihedralGroup.r 1⟩

@[expose] def h2 : G192 := ⟨Multiplicative.ofAdd ((2 : ZMod 4), (2 : ZMod 4)), DihedralGroup.sr 0⟩

@[expose] def wh1 (a b : G192) : G192 := a * b * a⁻¹ * a⁻¹ * b * a⁻¹ * a⁻¹

@[expose] def wh2 (a b : G192) : G192 := a * b * a * a * b * a * b * a

theorem h1_eq : h1 = wh1 g1 g2 := by decide

theorem h2_eq : h2 = wh2 g1 g2 := by decide

set_option synthInstance.maxSize 1000 in
theorem w192_nf_dec : ∀ x : G192, ∃ m n : Fin 4, ∃ i : Fin 6, ∃ j : Fin 2,
    x = (g1 * g2 * g1 * g2) ^ (m : ℕ) * (g1 * g2 * g1⁻¹ * g2 * g1⁻¹ * g1⁻¹) ^ (n : ℕ) *
      g1 ^ (i : ℕ) * (g1 * g2 * g1 * g2 * g1⁻¹ * g2) ^ (j : ℕ) := by
  decide +kernel

theorem w192_closure : Subgroup.closure ({g1, g2} : Set G192) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨m, n, i, j, rfl⟩ := w192_nf_dec x
  have ha : g1 ∈ Subgroup.closure ({g1, g2} : Set G192) := Subgroup.subset_closure (by simp)
  have hb : g2 ∈ Subgroup.closure ({g1, g2} : Set G192) := Subgroup.subset_closure (by simp)
  have hA := Subgroup.inv_mem _ ha
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _)
    (Subgroup.pow_mem _ ?_ _)) (Subgroup.pow_mem _ ha _)) (Subgroup.pow_mem _ ?_ _)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) ha) hb
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ ha hb) hA) hb) hA) hA
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ ha hb) ha) hb) hA) hb

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1000 in
theorem w192_aut_dec : ∀ a b : G192, a ^ 6 = 1 → a ^ 2 ≠ 1 → a ^ 3 ≠ 1 → b * b = 1 → b ≠ 1 →
    (a * b) ^ 8 = 1 → (a * b) ^ 4 ≠ 1 → (a * b * a⁻¹ * b⁻¹) ^ 3 = 1 → a * b * a⁻¹ * b⁻¹ ≠ 1 →
    (a * a * b) ^ 8 = 1 → (a * a * b) ^ 4 ≠ 1 → (a * b * a) ^ 8 = 1 → (a * b * a) ^ 4 ≠ 1 →
    ∃ c : G192, (c * g1 * c⁻¹ = a ∧ c * g2 * c⁻¹ = b) ∨ (c * h1 * c⁻¹ = a ∧ c * h2 * c⁻¹ = b) := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
theorem w192_sq_dec : ∃ e : G192, e * g1 * e⁻¹ = wh1 h1 h2 ∧ e * g2 * e⁻¹ = wh2 h1 h2 := by
  decide +kernel

set_option synthInstance.maxSize 1000 in
private theorem w192_cond_g : g1 ^ 6 = 1 ∧ g1 ^ 2 ≠ 1 ∧ g1 ^ 3 ≠ 1 ∧ g2 * g2 = 1 ∧ g2 ≠ 1 ∧
    (g1 * g2) ^ 8 = 1 ∧ (g1 * g2) ^ 4 ≠ 1 ∧ (g1 * g2 * g1⁻¹ * g2⁻¹) ^ 3 = 1 ∧
    g1 * g2 * g1⁻¹ * g2⁻¹ ≠ 1 ∧ (g1 * g1 * g2) ^ 8 = 1 ∧ (g1 * g1 * g2) ^ 4 ≠ 1 ∧
    (g1 * g2 * g1) ^ 8 = 1 ∧ (g1 * g2 * g1) ^ 4 ≠ 1 := by
  decide +kernel

private theorem w192_aut_images (χ : MulAut G192) :
    ∃ c : G192, (c * g1 * c⁻¹ = χ g1 ∧ c * g2 * c⁻¹ = χ g2) ∨
      (c * h1 * c⁻¹ = χ g1 ∧ c * h2 * c⁻¹ = χ g2) := by
  have e1 : ∀ (x : G192) (n : ℕ), (χ x) ^ n = 1 ↔ x ^ n = 1 := fun x n => by
    rw [← map_pow, map_eq_one_iff _ χ.injective]
  have e2 : ∀ x : G192, χ x = 1 ↔ x = 1 := fun x => map_eq_one_iff _ χ.injective
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩ := w192_cond_g
  refine w192_aut_dec (χ g1) (χ g2) ((e1 _ _).mpr c1) (fun h => c2 ((e1 _ _).mp h))
    (fun h => c3 ((e1 _ _).mp h)) (by rw [← map_mul, e2]; exact c4) (fun h => c5 ((e2 _).mp h))
    (by rw [← map_mul, e1]; exact c6) (fun h => c7 (by rw [← map_mul, e1] at h; exact h))
    (by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, e1]; exact c8)
    (fun h => c9 (by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, e2] at h; exact h))
    (by rw [← map_mul, ← map_mul, e1]; exact c10)
    (fun h => c11 (by rw [← map_mul, ← map_mul, e1] at h; exact h))
    (by rw [← map_mul, ← map_mul, e1]; exact c12)
    (fun h => c13 (by rw [← map_mul, ← map_mul, e1] at h; exact h))

theorem w192_mul_mem_inner {φ ψ : MulAut G192} (hφ : φ ∉ inner G192) (hψ : ψ ∉ inner G192) :
    φ * ψ ∈ inner G192 := by
  have hext : ∀ χ χ' : MulAut G192, χ g1 = χ' g1 → χ g2 = χ' g2 → χ = χ' := by
    intro χ χ' e1 e2
    apply MulEquiv.toMonoidHom_injective
    refine MonoidHom.eq_of_eqOn_dense w192_closure ?_
    rintro x (rfl | rfl)
    · exact e1
    · exact e2
  have key : ∀ χ : MulAut G192, χ ∉ inner G192 →
      ∃ c : G192, c * h1 * c⁻¹ = χ g1 ∧ c * h2 * c⁻¹ = χ g2 := by
    intro χ hχ
    obtain ⟨c, ⟨hc1, hc2⟩ | h⟩ := w192_aut_images χ
    · exact absurd ⟨c, hext _ _ (by rw [MulAut.conj_apply]; exact hc1)
        (by rw [MulAut.conj_apply]; exact hc2)⟩ hχ
    · exact ⟨c, h⟩
  obtain ⟨c, hc1, hc2⟩ := key φ hφ
  obtain ⟨d, hd1, hd2⟩ := key ψ hψ
  obtain ⟨e, he1, he2⟩ := w192_sq_dec
  have hφh1 : φ h1 = c * (e * g1 * e⁻¹) * c⁻¹ := by
    rw [he1]
    conv_lhs => rw [h1_eq]
    simp only [wh1, map_mul, map_inv]
    rw [← hc1, ← hc2]
    group
  have hφh2 : φ h2 = c * (e * g2 * e⁻¹) * c⁻¹ := by
    rw [he2]
    conv_lhs => rw [h2_eq]
    simp only [wh2, map_mul, map_inv]
    rw [← hc1, ← hc2]
    group
  refine ⟨φ d * c * e, hext _ _ ?_ ?_⟩
  · rw [MulAut.conj_apply, MulAut.mul_apply, ← hd1, map_mul, map_mul, map_inv, hφh1]
    group
  · rw [MulAut.conj_apply, MulAut.mul_apply, ← hd2, map_mul, map_mul, map_inv, hφh2]
    group

end W192

theorem z4sq_card_fix_ge_four {T : Type} [Group T] [Finite T] {R : Subgroup T}
    (e : ↥R ≃* Multiplicative (ZMod 4 × ZMod 4)) {u : T} (hu2 : u * u = 1)
    (huR : u ∈ Subgroup.normalizer (R : Set T)) :
    4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({u} : Set T)) := by
  classical
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hσR : ∀ r ∈ R, u * r * u⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.mp huR r).mp hr
  let σ : ↥R →* ↥R :=
    { toFun := fun r => ⟨u * r * u⁻¹, hσR r r.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hσ : ∀ r : ↥R, ((σ r : ↥R) : T) = u * r * u⁻¹ := fun _ => rfl
  have hσσ : ∀ r : ↥R, σ (σ r) = r := fun r => Subtype.ext (by
    rw [hσ, hσ, hu]
    calc u * (u * (r : T) * u) * u = (u * u) * (r : T) * (u * u) := by group
      _ = r := by rw [hu2]; group)
  let f : (ZMod 4 × ZMod 4) →+ (ZMod 4 × ZMod 4) :=
    { toFun := fun v => Multiplicative.toAdd (e (σ (e.symm (Multiplicative.ofAdd v))))
      map_zero' := by simp
      map_add' := fun v w => by simp [ofAdd_add, toAdd_mul] }
  have hf : ∀ v, f v = Multiplicative.toAdd (e (σ (e.symm (Multiplicative.ofAdd v)))) := fun _ => rfl
  have hfv : ∀ v : ZMod 4 × ZMod 4, f v = v.1 • f (1, 0) + v.2 • f (0, 1) := by
    intro v
    have hv : v = v.1 • ((1 : ZMod 4), (0 : ZMod 4)) + v.2 • ((0 : ZMod 4), (1 : ZMod 4)) := by
      ext <;> simp
    conv_lhs => rw [hv]
    rw [map_add, ZMod.map_smul, ZMod.map_smul]
  have hff : ∀ v, f (f v) = v := by
    intro v
    rw [hf, hf, ofAdd_toAdd, MulEquiv.symm_apply_apply, hσσ, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  have hF : ∀ v : ZMod 4 × ZMod 4, v.1 • f (1, 0) + v.2 • f (0, 1) = f v := fun v => (hfv v).symm
  have h4 := W192.z4_fix_dec (f (1, 0)) (f (0, 1)) (fun v => by rw [hF, hF, hff])
  have hfix : ∀ r : ↥R, σ r = r ↔ (r : T) ∈ Subgroup.centralizer ({u} : Set T) := by
    intro r
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : u * (r : T) * u⁻¹ = r := by rw [← hσ, h]
      calc (r : T) * u = u * (r : T) * u⁻¹ * u := by rw [h1]
        _ = u * r := by group
    · intro h
      apply Subtype.ext
      rw [hσ, ← h]
      group
  let E : ↥(R ⊓ Subgroup.centralizer ({u} : Set T)) ≃ {v : ZMod 4 × ZMod 4 // f v = v} :=
    { toFun := fun r => ⟨Multiplicative.toAdd (e ⟨r, r.2.1⟩), by
        rw [hf, ofAdd_toAdd, MulEquiv.symm_apply_apply, (hfix ⟨r, r.2.1⟩).mpr r.2.2]⟩
      invFun := fun v => ⟨(e.symm (Multiplicative.ofAdd v.1) : T), (e.symm _).2,
        (hfix (e.symm (Multiplicative.ofAdd v.1))).mp (by
          apply e.injective
          apply Multiplicative.toAdd.injective
          rw [← hf, MulEquiv.apply_symm_apply, toAdd_ofAdd]
          exact v.2)⟩
      left_inv := fun r => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [hF] using h4

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
