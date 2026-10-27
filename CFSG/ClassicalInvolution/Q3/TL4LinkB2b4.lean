module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b

open CFSG.ClassicalInvolution.Asc77

abbrev QuatGrp (r : ℕ) : Type := QuaternionGroup (2 ^ (r - 2))

structure QuatAutFacts (r : ℕ) : Prop where
  three_le : 3 ≤ r
  exists_plus : ∃ A : Subgroup (MulAut (QuatGrp r)), A.index = 2 ∧
    (∀ g : QuatGrp r, MulAut.conj g ∈ A) ∧ (∀ φ : MulAut (QuatGrp r), φ * φ ∈ A) ∧
    ∀ φ : MulAut (QuatGrp r), φ * φ = 1 →
      (φ ∉ A ↔ ∀ w : QuatGrp r, φ w = w → w * w = 1)
  stab_power : ∀ (φ : MulAut (QuatGrp r)) (x : QuatGrp r), orderOf x = 2 ^ (r - 1) → φ x = x →
    φ ^ 2 ^ (r - 2) = 1 ∨ φ ^ 2 ^ (r - 2) = MulAut.conj (x ^ 2 ^ (r - 3))

section QuatFacts

open QuaternionGroup

variable {n : ℕ}

private theorem quat_inv_a (i : ZMod (2 * n)) : (a i : QuaternionGroup n)⁻¹ = a (-i) := rfl

private theorem quat_inv_xa (i : ZMod (2 * n)) :
    (xa i : QuaternionGroup n)⁻¹ = xa ((n : ZMod (2 * n)) + i) := rfl

private theorem quat_n_add_n : (n : ZMod (2 * n)) + n = 0 := by
  rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]

private theorem quat_n_ne_zero [NeZero n] : (n : ZMod (2 * n)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (NeZero.pos n) h
  have := NeZero.pos n
  omega

private theorem quat_add_self_eq_zero_iff [NeZero n] (i : ZMod (2 * n)) :
    i + i = 0 ↔ i = 0 ∨ i = n := by
  constructor
  · intro h
    have hv := ZMod.val_lt i
    rw [← ZMod.natCast_zmod_val i, ← Nat.cast_add, ZMod.natCast_eq_zero_iff] at h
    obtain ⟨k, hk⟩ := h
    have hk2 : k < 2 := by
      by_contra hk2
      have : 2 * n * 2 ≤ 2 * n * k := Nat.mul_le_mul_left _ (not_lt.mp hk2)
      omega
    interval_cases k
    · left
      rw [← ZMod.natCast_zmod_val i]
      have : i.val = 0 := by omega
      rw [this, Nat.cast_zero]
    · right
      rw [← ZMod.natCast_zmod_val i]
      have : i.val = n := by omega
      rw [this]
  · rintro (rfl | rfl)
    · exact add_zero 0
    · exact quat_n_add_n

private theorem quat_one_ne_add_self (i : ZMod (2 * n)) : (1 : ZMod (2 * n)) ≠ i + i := by
  intro h
  have h2 := congrArg (ZMod.castHom (dvd_mul_right 2 n) (ZMod 2)) h
  rw [map_one, map_add] at h2
  generalize (ZMod.castHom (dvd_mul_right 2 n) (ZMod 2)) i = c at h2
  revert c
  decide

private theorem quat_mul_self_eq_one_iff [NeZero n] (w : QuaternionGroup n) :
    w * w = 1 ↔ w = a 0 ∨ w = a n := by
  rcases w with i | i
  · rw [a_mul_a, one_def, a.injEq, quat_add_self_eq_zero_iff, a.injEq, a.injEq]
  · rw [xa_mul_xa, one_def, a.injEq, add_sub_cancel_right]
    simp only [reduceCtorEq, or_self, iff_false]
    exact quat_n_ne_zero

private theorem quat_a_n_mul_comm (p : QuaternionGroup n) : a n * p = p * a n := by
  rcases p with j | j
  · rw [a_mul_a, a_mul_a, add_comm]
  · rw [a_mul_xa, xa_mul_a]
    congr 1
    linear_combination (-1 : ZMod (2 * n)) * quat_n_add_n

private theorem quat_a_n_ne_one [NeZero n] : (a n : QuaternionGroup n) ≠ 1 := by
  rw [one_def, Ne, a.injEq]
  exact quat_n_ne_zero

private theorem quat_aut_a_n [NeZero n] (φ : MulAut (QuaternionGroup n)) : φ (a n) = a n := by
  have h : φ (a n) * φ (a n) = 1 := by
    rw [← map_mul, a_mul_a, quat_n_add_n, a_zero, map_one]
  rcases (quat_mul_self_eq_one_iff _).mp h with h0 | h0
  · exfalso
    apply quat_a_n_ne_one (n := n)
    apply φ.injective
    rw [h0, a_zero, map_one]
  · exact h0

private def quatNegFun : QuaternionGroup n → QuaternionGroup n
  | a i => a (-i)
  | xa i => xa (1 - i)

private theorem quatNegFun_quatNegFun (w : QuaternionGroup n) :
    quatNegFun (quatNegFun w) = w := by
  rcases w with i | i <;> simp [quatNegFun]

private def quatNegAut : MulAut (QuaternionGroup n) where
  toFun := quatNegFun
  invFun := quatNegFun
  left_inv := quatNegFun_quatNegFun
  right_inv := quatNegFun_quatNegFun
  map_mul' := by
    rintro (i | i) (j | j) <;> simp only [quatNegFun, a_mul_a, a_mul_xa, xa_mul_a, xa_mul_xa]
    · congr 1; ring
    · congr 1; ring
    · congr 1; ring
    · congr 1; linear_combination (-1 : ZMod (2 * n)) * quat_n_add_n

private theorem quatNegAut_apply (w : QuaternionGroup n) : quatNegAut w = quatNegFun w := rfl

private theorem quatNegAut_mul_self :
    (quatNegAut : MulAut (QuaternionGroup n)) * quatNegAut = 1 := by
  ext w
  rw [MulAut.mul_apply, quatNegAut_apply, quatNegAut_apply, quatNegFun_quatNegFun,
    MulAut.one_apply]

private theorem quatNegAut_fix (w : QuaternionGroup n) (hw : quatNegAut w = w) : w * w = 1 := by
  rw [quatNegAut_apply] at hw
  rcases w with i | i
  · simp only [quatNegFun, a.injEq] at hw
    rw [a_mul_a, one_def, a.injEq]
    linear_combination -hw
  · simp only [quatNegFun, xa.injEq] at hw
    exact absurd (by linear_combination hw) (quat_one_ne_add_self i)

end QuatFacts

section AutSign

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private abbrev autSign : MulAut G →* ℤˣ := Equiv.Perm.sign.comp (MulAut.toPerm G)

private theorem autSign_conj (g : G) : autSign (MulAut.conj g) = 1 := by
  have h1 : MulAut.toPerm G (MulAut.conj g) = Equiv.mulRight g⁻¹ * Equiv.mulLeft g := by
    ext x
    rfl
  have h2 : Equiv.mulRight g⁻¹ =
      ((Equiv.inv G).symm.trans (Equiv.mulLeft g)).trans (Equiv.inv G) := by
    ext x
    simp
  rw [MonoidHom.comp_apply, h1, map_mul, h2, Equiv.Perm.sign_symm_trans_trans,
    Int.units_mul_self]

end AutSign

section AutSignQuat

open QuaternionGroup

variable {k : ℕ}

private theorem autSign_eq_neg_one_iff (φ : MulAut (QuaternionGroup (2 ^ k))) (hφ : φ * φ = 1) :
    autSign φ = -1 ↔ ∀ w, φ w = w → w * w = 1 := by
  have hσ : (MulAut.toPerm _ φ) ^ 2 = 1 := by rw [sq, ← map_mul, hφ, map_one]
  set S := MonoidHom.eqLocus (φ : _ →* _) (MonoidHom.id (QuaternionGroup (2 ^ k))) with hS
  have hmemS : ∀ w, w ∈ S ↔ φ w = w := fun w => Iff.rfl
  have hfix : Fintype.card (Function.fixedPoints ⇑(MulAut.toPerm _ φ)) = Nat.card S := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  have hsign : autSign φ = (-1) ^ ((4 * 2 ^ k - Nat.card S) / 2) := by
    rw [MonoidHom.comp_apply, Equiv.Perm.sign_of_pow_two_eq_one hσ, QuaternionGroup.card, hfix]
  have hcardQ : Nat.card (QuaternionGroup (2 ^ k)) = 4 * 2 ^ k := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hdvd : Nat.card S ∣ 4 * 2 ^ k := hcardQ ▸ Subgroup.card_subgroup_dvd_card S
  have hzS : (a (2 ^ k : ℕ) : QuaternionGroup (2 ^ k)) ∈ S := (hmemS _).mpr (quat_aut_a_n φ)
  have hS1 : Nat.card S ≠ 1 := by
    rw [Ne, Subgroup.card_eq_one]
    intro h
    rw [h] at hzS
    exact quat_a_n_ne_one ((Subgroup.mem_bot).mp hzS)
  by_cases hall : ∀ w, φ w = w → w * w = 1
  · have hle : S ≤ Subgroup.zpowers (a (2 ^ k : ℕ)) := by
      intro w hw
      rcases (quat_mul_self_eq_one_iff w).mp (hall w hw) with rfl | rfl
      · rw [a_zero]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have hord : orderOf (a (2 ^ k : ℕ) : QuaternionGroup (2 ^ k)) = 2 := by
      apply orderOf_eq_prime
      · rw [sq, a_mul_a, quat_n_add_n, a_zero]
      · exact quat_a_n_ne_one
    have h2 : Nat.card S ∣ 2 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hord] at this
    have hS2 : Nat.card S = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact absurd h hS1
      · exact h
    rw [hsign, hS2]
    refine iff_of_true ?_ hall
    apply Odd.neg_one_pow
    refine ⟨2 ^ k - 1, ?_⟩
    have := Nat.one_le_two_pow (n := k)
    omega
  · refine iff_of_false ?_ hall
    have hex : ∃ w, φ w = w ∧ w * w ≠ 1 := by
      by_contra h
      exact hall fun w hw => by_contra fun hw' => h ⟨w, hw, hw'⟩
    obtain ⟨w, hw, hww⟩ := hex
    have hwS : w ∈ S := (hmemS w).mpr hw
    have hord : orderOf w ∣ 2 ^ (k + 2) := by
      have := orderOf_dvd_natCard w
      rw [hcardQ, show (4 : ℕ) * 2 ^ k = 2 ^ (k + 2) by ring] at this
      exact this
    obtain ⟨u, hu, hwu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hu2 : 2 ≤ u := by
      by_contra hu2
      apply hww
      rw [← sq, ← orderOf_dvd_iff_pow_eq_one, hwu]
      exact (pow_dvd_pow 2 (by omega : u ≤ 1)).trans (pow_one 2).dvd
    have h4 : 4 ∣ Nat.card S := by
      have h1 : orderOf w ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hwS
      rw [hwu] at h1
      exact (pow_dvd_pow 2 hu2).trans h1
    have hle : Nat.card S ≤ 4 * 2 ^ k := Nat.le_of_dvd (by positivity) hdvd
    rw [hsign]
    obtain ⟨f, hf⟩ := h4
    rw [hf] at hle ⊢
    rw [Even.neg_one_pow ⟨2 ^ k - f, by omega⟩]
    decide

private theorem exists_plus_quat :
    ∃ A : Subgroup (MulAut (QuaternionGroup (2 ^ k))), A.index = 2 ∧
      (∀ g : QuaternionGroup (2 ^ k), MulAut.conj g ∈ A) ∧
      (∀ φ : MulAut (QuaternionGroup (2 ^ k)), φ * φ ∈ A) ∧
      ∀ φ : MulAut (QuaternionGroup (2 ^ k)), φ * φ = 1 →
        (φ ∉ A ↔ ∀ w : QuaternionGroup (2 ^ k), φ w = w → w * w = 1) := by
  have hneg : autSign (quatNegAut : MulAut (QuaternionGroup (2 ^ k))) = -1 :=
    (autSign_eq_neg_one_iff quatNegAut quatNegAut_mul_self).mpr quatNegAut_fix
  refine ⟨autSign.ker, ?_, fun g => autSign_conj g, fun φ => ?_, fun φ hφ => ?_⟩
  · rw [Subgroup.index_eq_two_iff]
    refine ⟨quatNegAut, fun b => ?_⟩
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, map_mul, hneg]
    rcases Int.units_eq_one_or (autSign b) with h | h <;> rw [h] <;> decide
  · rw [MonoidHom.mem_ker, map_mul, Int.units_mul_self]
  · rw [MonoidHom.mem_ker, ← Ne, Int.units_ne_iff_eq_neg, autSign_eq_neg_one_iff φ hφ]

end AutSignQuat

section StabPower

private theorem stab_power_aux {G : Type*} [Group G] {x y : G} {M K L : ℕ} (hK : K = 2 * M)
    (hL : L = 4 * M)
    (hcov : ∀ g : G, g ∈ Subgroup.zpowers x ∨ g * y⁻¹ ∈ Subgroup.zpowers x)
    (hyx : y * x * y⁻¹ = x⁻¹) (hx : x ^ L = 1) (hy : y ∉ Subgroup.zpowers x)
    (φ : MulAut G) (hφ : φ x = x) :
    φ ^ K = 1 ∨ φ ^ K = MulAut.conj (x ^ M) := by
  subst hK hL
  have hfixH : ∀ h ∈ Subgroup.zpowers x, φ h = h := by
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [map_zpow, hφ]
  have hpowfix : ∀ m : ℕ, ∀ h ∈ Subgroup.zpowers x, (φ ^ m) h = h := by
    intro m
    induction m with
    | zero => intro h _; rfl
    | succ m ih =>
      intro h hh
      rw [pow_succ', MulAut.mul_apply, ih h hh, hfixH h hh]
  have hφy : φ y * y⁻¹ ∈ Subgroup.zpowers x := by
    rcases hcov (φ y) with h | h
    · exfalso
      apply hy
      have h2 := φ.injective (hfixH _ h)
      rw [h2] at h
      exact h
    · exact h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hφy
  have hφy' : φ y = x ^ j * y := by
    rw [hj, inv_mul_cancel_right]
  have hpowy : ∀ m : ℕ, (φ ^ m) y = x ^ (j * m) * y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, hfixH _ (Subgroup.zpow_mem_zpowers x _), hφy',
        ← mul_assoc, ← zpow_add]
      congr 2
      push_cast
      ring
  have hyxk : ∀ k : ℤ, y * x ^ k = x ^ (-k) * y := by
    intro k
    have : y * x ^ k * y⁻¹ = x ^ (-k) := by
      rw [← conj_zpow, hyx, inv_zpow']
    rw [← this, inv_mul_cancel_right]
  have key : ∀ p q : ℤ, x ^ p * (x ^ q * y) = x ^ (p + q) * y := fun p q => by
    rw [← mul_assoc, ← zpow_add]
  have hx4 : x ^ (4 * (M : ℤ)) = 1 := by
    rw [← hx]
    exact_mod_cast rfl
  have hdecomp : ∀ g : G, g ∉ Subgroup.zpowers x → ∃ k : ℤ, g = x ^ k * y := by
    intro g hg
    rcases hcov g with h | h
    · exact absurd h hg
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
      exact ⟨k, by rw [hk, inv_mul_cancel_right]⟩
  rcases Int.even_or_odd j with ⟨l, hl⟩ | ⟨l, hl⟩
  · left
    ext g
    rw [MulAut.one_apply]
    by_cases hg : g ∈ Subgroup.zpowers x
    · exact hpowfix _ g hg
    · obtain ⟨k, rfl⟩ := hdecomp g hg
      rw [map_mul, hpowfix _ _ (Subgroup.zpow_mem_zpowers x k), hpowy, hl]
      congr 1
      have : x ^ ((l + l) * ((2 * M : ℕ) : ℤ)) = (x ^ (4 * (M : ℤ))) ^ l := by
        rw [← zpow_mul]
        congr 1
        push_cast
        ring
      rw [this, hx4, one_zpow, one_mul]
  · right
    ext g
    rw [MulAut.conj_apply]
    by_cases hg : g ∈ Subgroup.zpowers x
    · rw [hpowfix _ g hg]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [← zpow_natCast, ← zpow_neg, ← zpow_add, ← zpow_add]
      congr 1
      ring
    · obtain ⟨k, rfl⟩ := hdecomp g hg
      rw [map_mul, hpowfix _ _ (Subgroup.zpow_mem_zpowers x k), hpowy, hl]
      have h1 : x ^ ((2 * l + 1) * ((2 * M : ℕ) : ℤ)) = x ^ (2 * (M : ℤ)) := by
        have : (2 * l + 1) * ((2 * M : ℕ) : ℤ) = 4 * (M : ℤ) * l + 2 * M := by push_cast; ring
        rw [this, zpow_add, zpow_mul, hx4, one_zpow, one_mul]
      have h2 : y * (x ^ M)⁻¹ = x ^ (M : ℤ) * y := by
        rw [← zpow_natCast, ← zpow_neg, hyxk, neg_neg]
      rw [h1, key, mul_assoc, mul_assoc, h2, key k (M : ℤ), ← zpow_natCast, key]
      congr 2
      ring

open QuaternionGroup in
private theorem stab_power_quat {r : ℕ} (hr : 3 ≤ r) (φ : MulAut (QuatGrp r)) (x : QuatGrp r)
    (hxo : orderOf x = 2 ^ (r - 1)) (hφ : φ x = x) :
    φ ^ 2 ^ (r - 2) = 1 ∨ φ ^ 2 ^ (r - 2) = MulAut.conj (x ^ 2 ^ (r - 3)) := by
  have h21 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have h32 : 2 ^ (r - 2) = 2 * 2 ^ (r - 3) := by
    rw [← pow_succ']
    congr 1
    omega
  obtain ⟨y, hyx⟩ : ∃ y : QuatGrp r, y * x * y⁻¹ = x⁻¹ := by
    rcases x with i | i
    · refine ⟨xa 0, ?_⟩
      rw [quat_inv_xa, xa_mul_a, xa_mul_xa, quat_inv_a]
      congr 1
      linear_combination quat_n_add_n
    · have h4 : (4 : ℕ) = 2 ^ (r - 1) := by rw [← hxo, orderOf_xa]
      have hn : 2 ^ (r - 2) = 2 := by omega
      refine ⟨a 1, ?_⟩
      rw [a_mul_xa, quat_inv_a, xa_mul_a, quat_inv_xa]
      congr 1
      have hc : ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) = 2 := by
        rw [congrArg (Nat.cast : ℕ → ZMod (2 * 2 ^ (r - 2))) hn, Nat.cast_ofNat]
      linear_combination (-1 : ZMod (2 * 2 ^ (r - 2))) * quat_n_add_n + hc
  have hx2 : x ≠ x⁻¹ := by
    intro h
    have h1 : x ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [h]
      exact mul_inv_cancel x
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) h1
    rw [hxo] at h2
    have h3 : 2 ^ 2 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hy : y ∉ Subgroup.zpowers x := by
    intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    apply hx2
    rw [← hyx, (Commute.zpow_self x k).eq, mul_inv_cancel_right]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have h := Subgroup.index_mul_card (Subgroup.zpowers x)
    rw [Nat.card_zpowers, hxo, Nat.card_eq_fintype_card, QuaternionGroup.card, h21] at h
    have hpos : 0 < 2 ^ (r - 2) := by positivity
    have h' : (Subgroup.zpowers x).index * 2 = 4 :=
      Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_assoc]; exact h)
    omega
  have hcov : ∀ g : QuatGrp r, g ∈ Subgroup.zpowers x ∨ g * y⁻¹ ∈ Subgroup.zpowers x := by
    intro g
    by_cases hg : g ∈ Subgroup.zpowers x
    · exact Or.inl hg
    · right
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact iff_of_false hg (fun h => hy (by simpa using (Subgroup.zpowers x).inv_mem h))
  exact stab_power_aux (L := 2 ^ (r - 1)) h32 (by rw [h21, h32]; ring) hcov hyx
    (by rw [← hxo]; exact pow_orderOf_eq_one x) hy φ hφ

end StabPower

theorem QuatAutFacts.of_three_le {r : ℕ} (hr : 3 ≤ r) : QuatAutFacts r :=
  ⟨hr, exists_plus_quat, fun φ x hxo hφ => stab_power_quat hr φ x hxo hφ⟩

theorem quatAutFacts_three : QuatAutFacts 3 :=
  QuatAutFacts.of_three_le le_rfl

@[expose] def Outer {G : Type} [Group G] (R : Subgroup G) (c : G) : Prop :=
  ∀ w ∈ R, w * c = c * w → w * w = 1

section Elements

variable {r : ℕ} {G : Type} [Group G]

private def indAut {R : Subgroup G} (e : ↥R ≃* QuatGrp r) :
    ↥(Subgroup.normalizer (R : Set G)) →* MulAut (QuatGrp r) :=
  (MulAut.congr e).toMonoidHom.comp R.normalizerMonoidHom

private theorem indAut_apply {R : Subgroup G} (e : ↥R ≃* QuatGrp r)
    (v : ↥(Subgroup.normalizer (R : Set G))) (q : QuatGrp r) :
    ((e.symm (indAut e v q) : ↥R) : G) = (v : G) * (e.symm q : G) * (v : G)⁻¹ := by
  simp only [indAut, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

private theorem indAut_fix_iff {R : Subgroup G} (e : ↥R ≃* QuatGrp r)
    (v : ↥(Subgroup.normalizer (R : Set G))) (q : QuatGrp r) :
    indAut e v q = q ↔ (e.symm q : G) * v = v * (e.symm q : G) := by
  constructor
  · intro h
    have h' := indAut_apply e v q
    rw [h] at h'
    calc (e.symm q : G) * v = (v : G) * (e.symm q : G) * (v : G)⁻¹ * v := by rw [← h']
      _ = v * (e.symm q : G) := by rw [inv_mul_cancel_right]
  · intro h
    apply e.symm.injective
    apply Subtype.ext
    rw [indAut_apply, ← h, mul_inv_cancel_right]

private theorem mul_self_eq_one_of_symm {R : Subgroup G} (e : ↥R ≃* QuatGrp r) (q : QuatGrp r)
    (h : (e.symm q : G) * (e.symm q : G) = 1) : q * q = 1 := by
  have h2 : e.symm q * e.symm q = 1 := Subtype.ext h
  have h3 := congrArg e h2
  rwa [map_mul, MulEquiv.apply_symm_apply, map_one] at h3

theorem QuatAutFacts.stab_power_elem (hQ : QuatAutFacts r) {R : Subgroup G}
    (e : ↥R ≃* QuatGrp r) {v x : G} (hv : v ∈ Subgroup.normalizer (R : Set G)) (hx : x ∈ R)
    (hxo : orderOf x = 2 ^ (r - 1)) (hvx : v * x = x * v) :
    (∀ w ∈ R, v ^ 2 ^ (r - 2) * w = w * v ^ 2 ^ (r - 2)) ∨
      ∀ w ∈ R, v ^ 2 ^ (r - 2) * w * (v ^ 2 ^ (r - 2))⁻¹ =
        x ^ 2 ^ (r - 3) * w * (x ^ 2 ^ (r - 3))⁻¹ := by
  let V : ↥(Subgroup.normalizer (R : Set G)) := ⟨v, hv⟩
  have hXo : orderOf (e ⟨x, hx⟩) = 2 ^ (r - 1) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxo]
  have hXfix : indAut e V (e ⟨x, hx⟩) = e ⟨x, hx⟩ := by
    rw [indAut_fix_iff, MulEquiv.symm_apply_apply]
    exact hvx.symm
  have hpow : ∀ w (hw : w ∈ R), ((e.symm ((indAut e V ^ 2 ^ (r - 2)) (e ⟨w, hw⟩)) : ↥R) : G) =
      v ^ 2 ^ (r - 2) * w * (v ^ 2 ^ (r - 2))⁻¹ := by
    intro w hw
    rw [← map_pow, indAut_apply, MulEquiv.symm_apply_apply]
    rfl
  rcases hQ.stab_power (indAut e V) (e ⟨x, hx⟩) hXo hXfix with h | h
  · left
    intro w hw
    have h1 : w = v ^ 2 ^ (r - 2) * w * (v ^ 2 ^ (r - 2))⁻¹ := by
      have := hpow w hw
      rwa [h, MulAut.one_apply, MulEquiv.symm_apply_apply] at this
    calc v ^ 2 ^ (r - 2) * w
        = v ^ 2 ^ (r - 2) * w * (v ^ 2 ^ (r - 2))⁻¹ * v ^ 2 ^ (r - 2) :=
          (inv_mul_cancel_right _ _).symm
      _ = w * v ^ 2 ^ (r - 2) := by rw [← h1]
  · right
    intro w hw
    rw [← hpow w hw, h, MulAut.conj_apply]
    simp only [map_mul, map_pow, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul,
      Subgroup.coe_pow, Subgroup.coe_inv]

theorem QuatAutFacts.exists_fixed_of_sq (hQ : QuatAutFacts r) {R : Subgroup G}
    (e : ↥R ≃* QuatGrp r) {d : G} (hd : d ∈ Subgroup.normalizer (R : Set G))
    (hd4 : (d * d) * (d * d) = 1) :
    ∃ w ∈ R, w * (d * d) = (d * d) * w ∧ w * w ≠ 1 := by
  obtain ⟨A, -, -, hsq, hinv⟩ := hQ.exists_plus
  let D : ↥(Subgroup.normalizer (R : Set G)) := ⟨d, hd⟩
  have hφA : indAut e (D * D) ∈ A := by
    rw [map_mul]
    exact hsq _
  have hφ2 : indAut e (D * D) * indAut e (D * D) = 1 := by
    rw [← map_mul, show D * D * (D * D) = 1 from Subtype.ext hd4, map_one]
  obtain ⟨q, hq, hq1⟩ : ∃ q, indAut e (D * D) q = q ∧ q * q ≠ 1 := by
    by_contra hcon
    exact (hinv _ hφ2).mpr (fun q hq => by_contra fun hq1 => hcon ⟨q, hq, hq1⟩) hφA
  refine ⟨(e.symm q : G), (e.symm q).2, (indAut_fix_iff e (D * D) q).mp hq, fun h => hq1 ?_⟩
  exact mul_self_eq_one_of_symm e q h

theorem QuatAutFacts.not_outer_triple (hQ : QuatAutFacts r) {R : Subgroup G}
    (e : ↥R ≃* QuatGrp r) {c₁ c₂ : G} (h₁ : c₁ ∈ Subgroup.normalizer (R : Set G))
    (h₂ : c₂ ∈ Subgroup.normalizer (R : Set G)) (h₁₂ : c₁ * c₂ = c₂ * c₁) (hc₁ : c₁ * c₁ = 1)
    (hc₂ : c₂ * c₂ = 1) : ¬ (Outer R c₁ ∧ Outer R c₂ ∧ Outer R (c₁ * c₂)) := by
  rintro ⟨o₁, o₂, o₁₂⟩
  obtain ⟨A, hidx, -, -, hinv⟩ := hQ.exists_plus
  have key : ∀ C : ↥(Subgroup.normalizer (R : Set G)), (C : G) * C = 1 → Outer R C →
      indAut e C ∉ A := by
    intro C hC hO
    have hC2 : indAut e C * indAut e C = 1 := by
      rw [← map_mul, show C * C = 1 from Subtype.ext hC, map_one]
    rw [hinv _ hC2]
    intro q hq
    exact mul_self_eq_one_of_symm e q (hO _ (e.symm q).2 ((indAut_fix_iff e C q).mp hq))
  have k₁ := key ⟨c₁, h₁⟩ hc₁ o₁
  have k₂ := key ⟨c₂, h₂⟩ hc₂ o₂
  have h12 : c₁ * c₂ * (c₁ * c₂) = 1 := by
    calc c₁ * c₂ * (c₁ * c₂) = c₁ * (c₂ * c₁) * c₂ := by simp only [mul_assoc]
      _ = c₁ * (c₁ * c₂) * c₂ := by rw [h₁₂]
      _ = (c₁ * c₁) * (c₂ * c₂) := by simp only [mul_assoc]
      _ = 1 := by rw [hc₁, hc₂, one_mul]
  apply key (⟨c₁, h₁⟩ * ⟨c₂, h₂⟩) h12 o₁₂
  rw [map_mul]
  exact (Subgroup.mul_mem_iff_of_index_two hidx).mpr (iff_of_false k₁ k₂)

open scoped Pointwise in
private theorem mem_or_mul_mem_of_mem_sup {R : Subgroup G} {y : G} (hy : y * y = 1)
    (hyR : y ∈ Subgroup.normalizer (R : Set G)) {g : G} (hg : g ∈ R ⊔ Subgroup.zpowers y) :
    g ∈ R ∨ g * y ∈ R := by
  have hg' : g ∈ (R : Set G) * (Subgroup.zpowers y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left R _ (Subgroup.zpowers_le.mpr hyR)]
    exact hg
  obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.mp hg'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  rcases Int.even_or_odd' k with ⟨l, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hy, one_zpow, mul_one]
    exact hs
  · right
    rw [zpow_add, zpow_mul, zpow_two, hy, one_zpow, one_mul, zpow_one, mul_assoc, hy, mul_one]
    exact hs

private theorem dvd_of_dvd_mul_two_sub {m t : ℤ} (h : 8 * m ∣ t * (2 - 4 * m)) : 4 * m ∣ t := by
  have h' : 4 * m ∣ t * (1 - 2 * m) := by
    have h2 : (2 : ℤ) * (4 * m) ∣ 2 * (t * (1 - 2 * m)) := by
      have e1 : (2 : ℤ) * (4 * m) = 8 * m := by ring
      have e2 : (2 : ℤ) * (t * (1 - 2 * m)) = t * (2 - 4 * m) := by ring
      rw [e1, e2]
      exact h
    exact (mul_dvd_mul_iff_left two_ne_zero).mp h2
  have hcop : IsCoprime (4 * m) (1 - 2 * m) := ⟨1 - m, 1 - 2 * m, by ring⟩
  exact hcop.dvd_of_dvd_mul_right h'

theorem outer_of_isSemidihedral [Finite G] (hr : 3 ≤ r) {R : Subgroup G} (e : ↥R ≃* QuatGrp r)
    {y : G} (hy : y * y = 1) (hyR : y ∈ Subgroup.normalizer (R : Set G))
    (hsd : IsSemidihedral (R ⊔ Subgroup.zpowers y)) : Outer R y := by
  obtain ⟨a, b, ha8, hcard, hb2, -, hrel, hcl⟩ := hsd
  have hRinv : ∀ g ∈ R, g * g = 1 → ∀ h ∈ R, g * h = h * g := by
    intro g hg hgg h hh
    have hq : e ⟨g, hg⟩ * e ⟨g, hg⟩ = 1 := by
      rw [← map_mul, show (⟨g, hg⟩ : ↥R) * ⟨g, hg⟩ = 1 from Subtype.ext hgg, map_one]
    have hc : e ⟨g, hg⟩ * e ⟨h, hh⟩ = e ⟨h, hh⟩ * e ⟨g, hg⟩ := by
      rcases (quat_mul_self_eq_one_iff _).mp hq with h0 | h0
      · rw [h0, QuaternionGroup.a_zero, one_mul, mul_one]
      · rw [h0]
        exact quat_a_n_mul_comm _
    have := e.injective (show e (⟨g, hg⟩ * ⟨h, hh⟩) = e (⟨h, hh⟩ * ⟨g, hg⟩) by
      rw [map_mul, map_mul, hc])
    exact congrArg Subtype.val this
  have hcov : ∀ g ∈ R ⊔ Subgroup.zpowers y, g ∈ R ∨ g * y ∈ R :=
    fun g hg => mem_or_mul_mem_of_mem_sup hy hyR hg
  have haP : a ∈ R ⊔ Subgroup.zpowers y := by
    rw [← hcl]
    exact Subgroup.subset_closure (Set.mem_insert a {b})
  have hbP : b ∈ R ⊔ Subgroup.zpowers y := by
    rw [← hcl]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  by_cases hyR' : y ∈ R
  ·
    exfalso
    have hPR : R ⊔ Subgroup.zpowers y = R := sup_eq_left.mpr (Subgroup.zpowers_le.mpr hyR')
    rw [hPR] at haP hbP
    have hab := hRinv b hbP hb2 a haP
    have h1 : a ^ (orderOf a / 2 - 1) = a ^ 1 := by
      rw [← hrel, hab, mul_inv_cancel_right, pow_one]
    have h2 := Nat.ModEq.eq_of_lt_of_lt (pow_eq_pow_iff_modEq.mp h1) (by omega) (by omega)
    omega
  · intro w hw hwy
    have hyP : y ∈ R ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hRP : R ≤ R ⊔ Subgroup.zpowers y := le_sup_left
    have hidx : (R.subgroupOf (R ⊔ Subgroup.zpowers y)).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨y, hyP⟩, fun g => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      rcases hcov g g.2 with h | h
      · exact Or.inr ⟨h, fun h' => hyR' (by simpa using R.mul_mem (R.inv_mem h) h')⟩
      · exact Or.inl ⟨h, fun h' => hyR' (by simpa using R.mul_mem (R.inv_mem h') h)⟩
    have hcardR : Nat.card R = 2 ^ r := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card,
        show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
      congr 1
      omega
    have hN : orderOf a = 2 ^ r := by
      have h1 := Subgroup.card_mul_index (R.subgroupOf (R ⊔ Subgroup.zpowers y))
      rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv, hcardR, hcard] at h1
      omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, orderOf a = 8 * m := ⟨2 ^ (r - 3), by
      rw [hN, show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_add]
      congr 1
      omega⟩
    have hm0 : 0 < m := by omega
    have hc : ((orderOf a / 2 - 1 : ℕ) : ℤ) = 4 * (m : ℤ) - 1 := by
      rw [hm]
      omega
    have hba : ∀ j : ℤ, b * a ^ j = a ^ ((4 * (m : ℤ) - 1) * j) * b := by
      intro j
      have h1 : b * a ^ j * b⁻¹ = a ^ ((4 * (m : ℤ) - 1) * j) := by
        rw [← conj_zpow, hrel, ← zpow_natCast, ← zpow_mul, hc]
      rw [← h1, inv_mul_cancel_right]
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    have mul2 : ∀ p q : ℤ, a ^ p * (a ^ q * b) = a ^ (p + q) * b := fun p q => by
      rw [← mul_assoc, ← zpow_add]
    have mul3 : ∀ p q : ℤ, a ^ p * b * a ^ q = a ^ (p + (4 * (m : ℤ) - 1) * q) * b :=
      fun p q => by rw [mul_assoc, hba, ← mul_assoc, ← zpow_add]
    have mul4 : ∀ p q : ℤ, a ^ p * b * (a ^ q * b) = a ^ (p + (4 * (m : ℤ) - 1) * q) :=
      fun p q => by rw [← mul_assoc, mul3, mul_assoc, hb2, mul_one]
    have hnf : ∀ g ∈ R ⊔ Subgroup.zpowers y, ∃ i : ℤ, g = a ^ i ∨ g = a ^ i * b := by
      intro g hg
      rw [← hcl] at hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        rcases hg with h | h
        · exact ⟨1, Or.inl (by rw [h, zpow_one])⟩
        · exact ⟨0, Or.inr (by rw [Set.mem_singleton_iff.mp h, zpow_zero, one_mul])⟩
      | one => exact ⟨0, Or.inl (zpow_zero a).symm⟩
      | mul g h _ _ ihg ihh =>
        obtain ⟨i, rfl | rfl⟩ := ihg <;> obtain ⟨j, rfl | rfl⟩ := ihh
        · exact ⟨i + j, Or.inl (zpow_add a i j).symm⟩
        · exact ⟨i + j, Or.inr (mul2 i j)⟩
        · exact ⟨_, Or.inr (mul3 i j)⟩
        · exact ⟨_, Or.inl (mul4 i j)⟩
      | inv g _ ih =>
        obtain ⟨i, rfl | rfl⟩ := ih
        · exact ⟨-i, Or.inl (zpow_neg a i).symm⟩
        · exact ⟨_, Or.inr (by rw [mul_inv_rev, hbinv, ← zpow_neg, hba])⟩
    have hpow1 : ∀ p : ℤ, a ^ p = 1 ↔ 8 * (m : ℤ) ∣ p := by
      intro p
      rw [← orderOf_dvd_iff_zpow_eq_one, hm]
      push_cast
      rfl
    have hcancel : ∀ p q : ℤ, a ^ p = a ^ q ↔ 8 * (m : ℤ) ∣ p - q := by
      intro p q
      rw [← hpow1, zpow_sub, mul_inv_eq_one]
    obtain ⟨i, hyi | hyi⟩ := hnf y hyP
    ·
      exfalso
      apply hyR'
      have hi : 8 * (m : ℤ) ∣ 2 * i := by
        rw [← hpow1, two_mul, zpow_add, ← hyi]
        exact hy
      have ha2 : a ^ (2 : ℤ) ∈ R := by
        rcases hcov a haP with h | h
        · exact R.zpow_mem h 2
        · have h2 : (a * y) * (a * y) = a ^ (2 : ℤ) := by
            rw [hyi, ← zpow_one_add, ← zpow_add, hcancel,
              show 1 + i + (1 + i) - 2 = 2 * i by ring]
            exact hi
          rw [← h2]
          exact R.mul_mem h h
      have hi' : 4 * (m : ℤ) ∣ i := by
        have : (2 : ℤ) * (4 * m) ∣ 2 * i := by
          rw [show (2 : ℤ) * (4 * m) = 8 * m by ring]
          exact hi
        exact (mul_dvd_mul_iff_left two_ne_zero).mp this
      obtain ⟨s, hs⟩ := hi'
      rw [hyi, hs, show 4 * (m : ℤ) * s = 2 * (2 * m * s) by ring, zpow_mul]
      exact R.zpow_mem ha2 _
    ·
      have hi : 8 * (m : ℤ) ∣ 4 * m * i := by
        have h := hy
        rw [hyi, mul4, hpow1] at h
        rwa [show i + (4 * (m : ℤ) - 1) * i = 4 * m * i by ring] at h
      have hi2 : (2 : ℤ) ∣ i := by
        have : (4 * (m : ℤ)) * 2 ∣ (4 * m) * i := by
          rw [show (4 * (m : ℤ)) * 2 = 8 * m by ring]
          exact hi
        exact (mul_dvd_mul_iff_left (by positivity)).mp this
      obtain ⟨j, hwj | hwj⟩ := hnf w (hRP hw)
      · rw [hwj, hyi, mul2, mul3] at hwy
        have hj := (hcancel _ _).mp (mul_right_cancel hwy)
        rw [show j + i - (i + (4 * (m : ℤ) - 1) * j) = j * (2 - 4 * m) by ring] at hj
        obtain ⟨s, hs⟩ := dvd_of_dvd_mul_two_sub hj
        rw [hwj, ← zpow_add, hpow1, hs]
        exact ⟨s, by ring⟩
      · rw [hwj, hyi, mul4, mul4] at hwy
        have hj := (hcancel _ _).mp hwy
        rw [show j + (4 * (m : ℤ) - 1) * i - (i + (4 * m - 1) * j) = (j - i) * (2 - 4 * m) by
          ring] at hj
        have h4 := dvd_of_dvd_mul_two_sub hj
        have hj2 : (2 : ℤ) ∣ j := by
          have h2 : (2 : ℤ) ∣ j - i := (Dvd.intro (2 * (m : ℤ)) (by ring)).trans h4
          simpa using dvd_add h2 hi2
        obtain ⟨t, ht⟩ := hj2
        rw [hwj, mul4, hpow1, ht]
        exact ⟨t, by ring⟩

end Elements

end CFSG.ClassicalInvolution.Q3.TL4.LinkDisc.B2b
