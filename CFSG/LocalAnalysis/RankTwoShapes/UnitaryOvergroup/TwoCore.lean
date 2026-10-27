module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.Automorphism
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Sylow
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankTwoShapes

open Polynomial

noncomputable section

section FieldSixteen

variable {K : Type} [Field K]

theorem fieldSixteen_exists_pow_ne_self (hK : Nat.card K = 16) {n : ℕ} (hn : 2 ≤ n) (hn' : n < 16) :
    ∃ a : K, a ^ n ≠ a := by
  classical
  have := finite_of_natCard_eq_sixteen hK
  let : Fintype K := Fintype.ofFinite K
  by_contra hall
  push Not at hall
  have hP := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (X ^ n - X : K[X])
    Finset.univ (fun a _ => by simp [hall a]) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
      simp only [natDegree_X_pow, natDegree_X]
      omega)
  have h := congrArg (fun P => P.coeff n) hP
  have hn1 : n ≠ 1 := by omega
  simp [coeff_X, hn1.symm] at h

theorem fieldSixteen_pow_sixty_four (hK : Nat.card K = 16) (a : K) : a ^ 64 = a ^ 4 := by
  rw [show (64 : ℕ) = 16 * 4 by norm_num, pow_mul, pow_sixteen_eq_self hK]

theorem fieldSixteen_pow_five_hundred_twelve (hK : Nat.card K = 16) (a : K) : a ^ 512 = a ^ 2 := by
  rw [show (512 : ℕ) = 16 * 32 by norm_num, pow_mul, pow_sixteen_eq_self hK,
    show (32 : ℕ) = 16 * 2 by norm_num, pow_mul, pow_sixteen_eq_self hK]

theorem fieldSixteen_semilinear_sq_eq_id (hK : Nat.card K = 16) {c : K} {j : Fin 4}
    (h : ∀ a : K, c * (c * a ^ 2 ^ (j : ℕ)) ^ 2 ^ (j : ℕ) = a) :
    (j = 0 ∧ c = 1) ∨ (j = 2 ∧ c ^ 5 = 1) := by
  have := charP_two_of_natCard_eq_sixteen hK
  have h1 := h 1
  fin_cases j
  · left
    refine ⟨rfl, ?_⟩
    norm_num at h1
    have h1' : c ^ 2 = 1 := by rw [pow_two]; exact h1
    have h2 : (c + 1) ^ 2 = 0 := by
      rw [add_sq, one_pow, mul_one, h1', CharTwo.two_eq_zero, zero_mul, add_zero,
        CharTwo.add_self_eq_zero]
    exact CharTwo.add_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  · exfalso
    obtain ⟨a, ha⟩ := fieldSixteen_exists_pow_ne_self hK (n := 4) (by norm_num) (by norm_num)
    have h' := h a
    norm_num at h' h1
    have hc : c ^ 3 = 1 := by rw [← h1]; ring
    exact ha (by linear_combination h' - a ^ 4 * hc)
  · right
    refine ⟨rfl, ?_⟩
    norm_num at h1
    rw [← h1]
    ring
  · exfalso
    obtain ⟨a, ha⟩ := fieldSixteen_exists_pow_ne_self hK (n := 4) (by norm_num) (by norm_num)
    have h' := h a
    norm_num at h' h1
    have hc : c ^ 9 = 1 := by rw [← h1]; ring
    have h64 := fieldSixteen_pow_sixty_four hK a
    exact ha (by linear_combination h' - a ^ 64 * hc - h64)

theorem fieldSixteen_semilinear_cube_eq_id (hK : Nat.card K = 16) {c : K} {j : Fin 4}
    (h : ∀ a : K, c * (c * (c * a ^ 2 ^ (j : ℕ)) ^ 2 ^ (j : ℕ)) ^ 2 ^ (j : ℕ) = a) :
    j = 0 ∧ c ^ 3 = 1 := by
  have h1 := h 1
  fin_cases j
  · refine ⟨rfl, ?_⟩
    norm_num at h1
    rw [← h1]
    ring
  · exfalso
    obtain ⟨a, ha⟩ := fieldSixteen_exists_pow_ne_self hK (n := 8) (by norm_num) (by norm_num)
    have h' := h a
    norm_num at h' h1
    have hc : c ^ 7 = 1 := by rw [← h1]; ring
    exact ha (by linear_combination h' - a ^ 8 * hc)
  · exfalso
    obtain ⟨a, ha⟩ := fieldSixteen_exists_pow_ne_self hK (n := 4) (by norm_num) (by norm_num)
    have h' := h a
    norm_num at h' h1
    have hc : c ^ 21 = 1 := by rw [← h1]; ring
    have h64 := fieldSixteen_pow_sixty_four hK a
    exact ha (by linear_combination h' - a ^ 64 * hc - h64)
  · exfalso
    obtain ⟨a, ha⟩ := fieldSixteen_exists_pow_ne_self hK (n := 2) (by norm_num) (by norm_num)
    have h' := h a
    norm_num at h' h1
    have hc : c ^ 73 = 1 := by rw [← h1]; ring
    have h512 := fieldSixteen_pow_five_hundred_twelve hK a
    exact ha (by linear_combination h' - a ^ 512 * hc - h512)

end FieldSixteen

section Action

variable {H : Type*} [Group H] {K : Type} [Field K] {hK : Nat.card K = 16}

open UnitaryFourW

@[expose] def unitaryFourConjAction {Q : Subgroup H} [Q.Normal] (e : Q ≃* unitaryFourW K hK) :
    H →* MulAut (unitaryFourW K hK) :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

variable {Q : Subgroup H} [Q.Normal] (e : Q ≃* unitaryFourW K hK)

theorem unitaryFourConjAction_apply_apply (h : H) (q : Q) :
    unitaryFourConjAction e h (e q) = e (MulAut.conjNormal h q) := by
  simp [unitaryFourConjAction, MulAut.congr_apply]

theorem unitaryFourConjAction_apply (h : H) (w : unitaryFourW K hK) :
    unitaryFourConjAction e h w = e (MulAut.conjNormal h (e.symm w)) := by
  rw [← unitaryFourConjAction_apply_apply, MulEquiv.apply_symm_apply]

theorem fst_unitaryFourConjAction_of_mem {q : H} (hq : q ∈ Q) (w : unitaryFourW K hK) :
    fst (unitaryFourConjAction e q w) = fst w := by
  have := charP_two_of_natCard_eq_sixteen hK
  have h : MulAut.conjNormal q (e.symm w) = ⟨q, hq⟩ * e.symm w * (⟨q, hq⟩ : Q)⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [unitaryFourConjAction_apply, h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
    fst_mul, fst_mul, fst_inv]
  ring_nf
  rw [CharTwo.two_eq_zero, mul_zero, zero_add]

theorem mem_of_fst_unitaryFourConjAction_eq (hQ : CFSG.pCore 2 H = Q)
    (hCQ : Subgroup.centralizer (Q : Set H) ≤ Q) {x : H}
    (hx : ∀ w, fst (unitaryFourConjAction e x w) = fst w) : x ∈ Q := by
  have hQp : IsPGroup 2 Q := hQ ▸ pCore_isPGroup
  let X := (firstCoordFixing hK).comap (unitaryFourConjAction e)
  have hXn : X.Normal := Subgroup.Normal.comap inferInstance _
  have hX2 : ∀ y ∈ X, y ^ 2 ∈ Q := fun y hy => by
    have h1 := mul_self_eq_one_of_mem_firstCoordFixing hy
    have h2 : unitaryFourConjAction e (y ^ 2) = 1 := by rw [pow_two, map_mul, h1]
    apply hCQ
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h3 := congrArg (fun α : MulAut (unitaryFourW K hK) => α (e ⟨q, hq⟩)) h2
    simp only [unitaryFourConjAction_apply_apply, MulAut.one_apply] at h3
    have h4 := congrArg Subtype.val (e.injective h3)
    simp only [MulAut.conjNormal_apply] at h4
    calc q * y ^ 2 = (y ^ 2 * q * (y ^ 2)⁻¹) * y ^ 2 := by rw [h4]
      _ = y ^ 2 * q := by group
  have hXp : IsPGroup 2 X := fun g => by
    obtain ⟨n, hn⟩ := hQp ⟨_, hX2 g g.2⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have := congrArg Subtype.val hn
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_succ', pow_mul, this]
  have hXQ : X ≤ Q := hQ ▸ le_sSup ⟨hXn, hXp⟩
  exact hXQ hx

theorem mul_inv_mem_of_fst_unitaryFourConjAction_eq (hQ : CFSG.pCore 2 H = Q)
    (hCQ : Subgroup.centralizer (Q : Set H) ≤ Q) {a b : H}
    (hab : ∀ w, fst (unitaryFourConjAction e a w) = fst (unitaryFourConjAction e b w)) :
    a * b⁻¹ ∈ Q := by
  apply mem_of_fst_unitaryFourConjAction_eq e hQ hCQ
  intro w
  rw [map_mul, MulAut.mul_apply, hab, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    MulAut.one_apply]

end Action

section Core

variable {H : Type*} [Group H] [Finite H] {K : Type} [Field K] {hK : Nat.card K = 16}

open UnitaryFourW

theorem exists_elementaryEight_of_unitaryFour_twoCore (Q : Subgroup H)
    (hQ : CFSG.pCore 2 H = Q) (hCQ : Subgroup.centralizer (Q : Set H) ≤ Q)
    (e : Q ≃* unitaryFourW K hK) (h3 : 3 ∣ Q.index) (h2 : 2 ∣ Q.index) :
    ∃ E : Subgroup H, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
      Nat.card E = 8 := by
  classical
  have : Q.Normal := hQ ▸ pCore_normal
  have hQp : IsPGroup 2 Q := hQ ▸ pCore_isPGroup
  have := charP_two_of_natCard_eq_sixteen hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := unitaryFourConjAction e with hψ
  have hker : ∀ x, (∀ w, fst (ψ x w) = fst w) → x ∈ Q := fun x hx =>
    mem_of_fst_unitaryFourConjAction_eq e hQ hCQ hx
  have hQ3 : ∀ y ∈ Q, y ^ 3 = 1 → y = 1 := fun y hy hy3 => by
    obtain ⟨n, hn⟩ := hQp ⟨y, hy⟩
    have hn' : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 : orderOf y ∣ Nat.gcd (2 ^ n) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn') (orderOf_dvd_of_pow_eq_one hy3)
    rw [Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3), Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    exact h1
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 3 (h3.trans Q.index_dvd_card)
  have hr3 : r ^ 3 = 1 := hr ▸ pow_orderOf_eq_one r
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hr
    norm_num at hr
  obtain ⟨c, j, hcV, hcZ⟩ := exists_units_fin_four_of_mulEquiv (ψ r)
  have hψr3 : ∀ w, ψ r (ψ r (ψ r w)) = w := fun w => by
    have h := congrArg (fun α : MulAut (unitaryFourW K hK) => α w)
      (show ψ (r ^ 3) = 1 by rw [hr3, map_one])
    simpa [pow_succ, MulAut.mul_apply] using h
  obtain ⟨rfl, hc3⟩ : j = 0 ∧ (c : K) ^ 3 = 1 := by
    apply fieldSixteen_semilinear_cube_eq_id hK
    intro a
    obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) a
    rw [← hcV w, ← hcV (ψ r w), ← hcV (ψ r (ψ r w)), hψr3]
  simp only [Fin.val_zero, pow_zero, pow_one] at hcV hcZ
  have hc1 : (c : K) ≠ 1 := by
    intro h
    apply hr1
    refine hQ3 r (hker r fun w => ?_) hr3
    rw [hcV, h, one_mul]
  have hc5 : (c : K) ^ 5 ≠ 1 := by
    intro h
    apply hc1
    calc (c : K) = (c : K) ^ 3 * (c : K) ^ 3 / (c : K) ^ 5 := by
          field_simp [c.ne_zero]
      _ = 1 := by rw [hc3, h]; norm_num
  have hfix : ∀ q ∈ Q, r * q = q * r → q = 1 := fun q hq hrq => by
    set w := e ⟨q, hq⟩ with hw_def
    have hw : ψ r w = w := by
      rw [hw_def, unitaryFourConjAction_apply_apply]
      congr 1
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hrq, mul_inv_cancel_right]
    have h1 : fst w = 0 := by
      have h := hcV w
      rw [hw] at h
      have h' : ((c : K) - 1) * fst w = 0 := by linear_combination -h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd (sub_eq_zero.mp h'') hc1
      · exact h''
    have h2 : snd w = 0 := by
      have h := hcZ w h1
      rw [hw] at h
      have h' : ((c : K) ^ 5 - 1) * snd w = 0 := by linear_combination -h
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd (sub_eq_zero.mp h'') hc5
      · exact h''
    have hw1 : w = 1 := by
      ext
      · rw [h1, fst_one]
      · rw [h2, snd_one]
    have h3' : (⟨q, hq⟩ : Q) = 1 := e.injective (hw1.trans (map_one e).symm)
    exact congrArg Subtype.val h3'
  have hr4 : r ^ 2 * r ^ 2 = r := by
    rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hr3, one_mul]
  have hfixs : ∀ m : ℕ, (m = 1 ∨ m = 2) → ∀ q ∈ Q, r ^ m * q = q * r ^ m → q = 1 := by
    rintro m (rfl | rfl) q hq h
    · exact hfix q hq (by simpa using h)
    · refine hfix q hq ?_
      calc r * q = r ^ 2 * (r ^ 2 * q) := by rw [← mul_assoc, hr4]
        _ = r ^ 2 * (q * r ^ 2) := by rw [h]
        _ = (r ^ 2 * q) * r ^ 2 := (mul_assoc _ _ _).symm
        _ = q * r ^ 2 * r ^ 2 := by rw [h]
        _ = q * r := by rw [mul_assoc, hr4]
  have hconj : ∀ h : H, ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ (h * r * h⁻¹) * (r ^ m)⁻¹ ∈ Q := by
    intro h
    obtain ⟨d, k, hdV, -⟩ := exists_units_fin_four_of_mulEquiv (ψ h)
    have hact : ∀ w, fst (ψ (h * r * h⁻¹) w) = (c : K) ^ 2 ^ (k : ℕ) * fst w := fun w => by
      have hu : ψ h (ψ h⁻¹ w) = w := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hdV, hcV]
      conv_rhs => rw [← hu, hdV]
      ring
    have hr1' : ∀ w, fst (ψ (r ^ 1) w) = (c : K) * fst w := fun w => by rw [pow_one, hcV]
    have hr2' : ∀ w, fst (ψ (r ^ 2) w) = (c : K) ^ 2 * fst w := fun w => by
      rw [pow_two, map_mul, MulAut.mul_apply, hcV, hcV]
      ring
    have hck : (c : K) ^ 2 ^ (k : ℕ) = c ∨ (c : K) ^ 2 ^ (k : ℕ) = c ^ 2 := by
      fin_cases k
      · left
        simp
      · right
        simp
      · left
        show (c : K) ^ 4 = c
        rw [show (c : K) ^ 4 = (c : K) ^ 3 * c by ring, hc3, one_mul]
      · right
        show (c : K) ^ 8 = c ^ 2
        rw [show (c : K) ^ 8 = ((c : K) ^ 3) ^ 2 * c ^ 2 by ring, hc3, one_pow, one_mul]
    rcases hck with hck | hck
    · refine ⟨1, Or.inl rfl, mul_inv_mem_of_fst_unitaryFourConjAction_eq e hQ hCQ fun w => ?_⟩
      rw [hact, hr1', hck]
    · refine ⟨2, Or.inr rfl, mul_inv_mem_of_fst_unitaryFourConjAction_eq e hQ hCQ fun w => ?_⟩
      rw [hact, hr2', hck]
  have hsolve : ∀ m : ℕ, (m = 1 ∨ m = 2) → ∀ q₀ ∈ Q, ∃ q ∈ Q, q * r ^ m * q⁻¹ = q₀ * r ^ m := by
    intro m hm q₀ hq₀
    let θ : Q → Q := fun q => ⟨q * (r ^ m * (q : H)⁻¹ * (r ^ m)⁻¹),
      Q.mul_mem q.2 (Subgroup.Normal.conj_mem inferInstance _ (Q.inv_mem q.2) _)⟩
    have hθ : Function.Injective θ := by
      intro q₁ q₂ h
      have h' : (q₁ : H) * (r ^ m * (q₁ : H)⁻¹ * (r ^ m)⁻¹) =
          q₂ * (r ^ m * (q₂ : H)⁻¹ * (r ^ m)⁻¹) := congrArg Subtype.val h
      have h'' : (q₁ : H) * r ^ m * (q₁ : H)⁻¹ = q₂ * r ^ m * (q₂ : H)⁻¹ := by
        have := congrArg (· * r ^ m) h'
        simpa [mul_assoc] using this
      have hcomm : r ^ m * ((q₂ : H)⁻¹ * q₁) = ((q₂ : H)⁻¹ * q₁) * r ^ m := by
        calc r ^ m * ((q₂ : H)⁻¹ * q₁)
            = (q₂ : H)⁻¹ * (q₂ * r ^ m * (q₂ : H)⁻¹) * q₁ := by group
          _ = (q₂ : H)⁻¹ * (q₁ * r ^ m * (q₁ : H)⁻¹) * q₁ := by rw [h'']
          _ = ((q₂ : H)⁻¹ * q₁) * r ^ m := by group
      have h1 := hfixs m hm _ (Q.mul_mem (Q.inv_mem q₂.2) q₁.2) hcomm
      exact Subtype.ext (inv_mul_eq_one.mp h1).symm
    obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.mp hθ) ⟨q₀, hq₀⟩
    refine ⟨q, q.2, ?_⟩
    have h := congrArg Subtype.val hq
    change (q : H) * (r ^ m * (q : H)⁻¹ * (r ^ m)⁻¹) = q₀ at h
    rw [← h]
    group
  set R := Subgroup.zpowers r with hR
  set M := Subgroup.normalizer (R : Set H) with hM
  have hR3 : ∀ g ∈ R, g ^ 3 = 1 := fun g hg => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hr3, one_zpow]
  have hmemM : ∀ x : H, (x * r * x⁻¹ = r ∨ x * r * x⁻¹ = r ^ 2) → x ∈ M := by
    intro x hx
    have hx' : x⁻¹ * r * x ∈ R := by
      rcases hx with hx | hx
      · have h : x⁻¹ * r * x = r := by
          calc x⁻¹ * r * x = x⁻¹ * (x * r * x⁻¹) * x := by rw [hx]
            _ = r := by group
        rw [h]
        exact Subgroup.mem_zpowers r
      · have h2 : x * r ^ 2 * x⁻¹ = r := by
          rw [← conj_pow, hx, pow_two, hr4]
        have h : x⁻¹ * r * x = r ^ 2 := by
          calc x⁻¹ * r * x = x⁻¹ * (x * r ^ 2 * x⁻¹) * x := by rw [h2]
            _ = r ^ 2 := by group
        rw [h]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers r) 2
    have hxr : x * r * x⁻¹ ∈ R := by
      rcases hx with hx | hx <;> rw [hx]
      · exact Subgroup.mem_zpowers r
      · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers r) 2
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ hxr k
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h : y = (x⁻¹ * r * x⁻¹⁻¹) ^ k := by
        rw [conj_zpow, hk]
        group
      rw [h, inv_inv]
      exact Subgroup.zpow_mem _ hx' k
  have hcoset : ∀ h : H, ∃ q ∈ Q, q⁻¹ * h ∈ M := fun h => by
    obtain ⟨m, hm, hq₀⟩ := hconj h
    obtain ⟨q, hq, hqe⟩ := hsolve m hm _ hq₀
    have hqe' : q * r ^ m * q⁻¹ = h * r * h⁻¹ := by
      rw [hqe]
      group
    refine ⟨q, hq, hmemM _ ?_⟩
    have h' : (q⁻¹ * h) * r * (q⁻¹ * h)⁻¹ = r ^ m := by
      calc (q⁻¹ * h) * r * (q⁻¹ * h)⁻¹ = q⁻¹ * (h * r * h⁻¹) * q := by group
        _ = q⁻¹ * (q * r ^ m * q⁻¹) * q := by rw [hqe']
        _ = r ^ m := by group
    rcases hm with rfl | rfl
    · left
      rw [h', pow_one]
    · right
      exact h'
  have hQM : ∀ q ∈ Q, q ∈ M → q = 1 := fun q hq hqM => by
    have h1 : q * r * q⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hqM r).mp (Subgroup.mem_zpowers r)
    have h2 : q * r * q⁻¹ * r⁻¹ ∈ Q := by
      have h : q * r * q⁻¹ * r⁻¹ = q * (r * q⁻¹ * r⁻¹) := by group
      rw [h]
      exact Q.mul_mem hq (Subgroup.Normal.conj_mem inferInstance _ (Q.inv_mem hq) r)
    have h3' : q * r * q⁻¹ * r⁻¹ ∈ R := R.mul_mem h1 (R.inv_mem (Subgroup.mem_zpowers r))
    have h4 := hQ3 _ h2 (hR3 _ h3')
    apply hfix q hq
    have h5 : q * r * q⁻¹ = r := mul_inv_eq_one.mp h4
    calc r * q = (q * r * q⁻¹) * q := by rw [h5]
      _ = q * r := by group
  obtain ⟨xbar, hxbar⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ Q) 2 h2
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xbar
  have hxQ : x ∉ Q := by
    intro hx
    rw [← QuotientGroup.eq_one_iff] at hx
    rw [hx, orderOf_one] at hxbar
    norm_num at hxbar
  have hx2 : x ^ 2 ∈ Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hxbar, pow_orderOf_eq_one]
  obtain ⟨q, hq, hqM⟩ := hcoset x
  set t := q⁻¹ * x with ht
  have htQ : t ∉ Q := fun h => hxQ (by
    have hx : x = q * t := by rw [ht]; group
    rw [hx]
    exact Q.mul_mem hq h)
  have ht2Q : t ^ 2 ∈ Q := by
    have h : t ^ 2 = q⁻¹ * (x * q⁻¹ * x⁻¹) * x ^ 2 := by
      rw [ht, pow_two, pow_two]
      group
    rw [h]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq)
      (Subgroup.Normal.conj_mem inferInstance _ (Q.inv_mem hq) x)) hx2
  have ht2 : t ^ 2 = 1 := hQM _ ht2Q (M.pow_mem hqM 2)
  have ht1 : t ≠ 1 := fun h => htQ (h ▸ Q.one_mem)
  obtain ⟨c', j', hc'V, hc'Z⟩ := exists_units_fin_four_of_mulEquiv (ψ t)
  have hψt2 : ∀ w, ψ t (ψ t w) = w := fun w => by
    have h := congrArg (fun α : MulAut (unitaryFourW K hK) => α w)
      (show ψ (t ^ 2) = 1 by rw [ht2, map_one])
    simpa [pow_two, MulAut.mul_apply] using h
  have hcases := fieldSixteen_semilinear_sq_eq_id hK (c := (c' : K)) (j := j') fun a => by
    obtain ⟨w, rfl⟩ := exists_fst_eq (hK := hK) a
    rw [← hc'V w, ← hc'V (ψ t w), hψt2]
  have htZ : ∀ w, fst w = 0 → ψ t w = w := by
    rcases hcases with ⟨rfl, hc'1⟩ | ⟨rfl, hc'5⟩
    · exfalso
      apply htQ
      apply hker
      intro w
      rw [hc'V, hc'1]
      simp
    · intro w hw
      ext
      · rw [fst_apply_eq_zero _ hw, hw]
      · rw [hc'Z w hw, hc'5, one_mul]
        exact snd_pow_four_of_fst_eq_zero hw
  let φW : unitaryFourW K hK →* H := Q.subtype.comp e.symm.toMonoidHom
  have hφW : Function.Injective φW := Subtype.val_injective.comp e.symm.injective
  let Z := (Subgroup.center (unitaryFourW K hK)).map φW
  have hZQ : ∀ z ∈ Z, z ∈ Q := by
    rintro _ ⟨w, -, rfl⟩
    exact (e.symm w).2
  have hZt : ∀ z ∈ Z, z * t = t * z := by
    rintro _ ⟨w, hw, rfl⟩
    have hw0 : fst w = 0 := by
      rw [SetLike.mem_coe, center_eq_ker_firstCoord, mem_ker_firstCoord] at hw
      exact hw
    have h := htZ w hw0
    rw [unitaryFourConjAction_apply] at h
    have h' := congrArg (fun v => ((e.symm v : Q) : H)) h
    simp only [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] at h'
    change ((e.symm w : Q) : H) * t = t * ((e.symm w : Q) : H)
    calc ((e.symm w : Q) : H) * t = (t * ↑(e.symm w) * t⁻¹) * t := by rw [h']
      _ = t * ((e.symm w : Q) : H) := by group
  have hZsq : ∀ z ∈ Z, z ^ 2 = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_pow, sq_eq_one_of_mem_center hw, map_one]
  have hZcomm : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ * z₂ = z₂ * z₁ := by
    rintro _ ⟨w₁, -, rfl⟩ _ ⟨w₂, hw₂, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw₂ w₁]
  have hZcard : Nat.card Z = 4 := by
    rw [Subgroup.card_map_of_injective hφW, natCard_center]
  have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hTsq : ∀ y ∈ Subgroup.zpowers t, y ^ 2 = 1 := fun y hy => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hcomm : ∀ (a : Z) (b : Subgroup.zpowers t),
      Commute (Z.subtype a) ((Subgroup.zpowers t).subtype b) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact Commute.zpow_right (hZt a ha) k
  let Φ := MonoidHom.noncommCoprod Z.subtype (Subgroup.zpowers t).subtype hcomm
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hab
    simp only [Φ, MonoidHom.noncommCoprod_apply, Subgroup.coe_subtype] at hab
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hk : t ^ k = t ^ (k % 2) := by
      have h := (zpow_mod_orderOf t k).symm
      rwa [htord, Nat.cast_ofNat] at h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk
      rw [hk, mul_one] at hab
      subst hab
      ext <;> simp [hk]
    · exfalso
      rw [h1, zpow_one] at hk
      rw [hk] at hab
      apply htQ
      have hta : t = a⁻¹ := (eq_inv_of_mul_eq_one_right hab)
      rw [hta]
      exact Q.inv_mem (hZQ a ha)
  refine ⟨Φ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := u
    obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := v
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨k', rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    ext
    · exact hZcomm a ha a' ha'
    · exact (Commute.zpow_zpow_self t k k').eq
  · rintro _ ⟨u, rfl⟩
    rw [← map_pow]
    have hu : u ^ 2 = 1 := by
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := u
      ext
      · exact hZsq a ha
      · exact hTsq b hb
    rw [hu, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, Nat.card_prod, hZcard,
      Nat.card_zpowers, htord]

theorem two_dvd_index_of_lt_sylow {Q : Subgroup H} (P : Sylow 2 H) (hQP : Q < P) :
    2 ∣ Q.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Q.relIndex P ∣ Q.index := by
    rw [← Subgroup.relIndex_mul_index hQP.le]
    exact dvd_mul_right _ _
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have h2 : Q.relIndex P ∣ 2 ^ n := hn ▸ Subgroup.relIndex_dvd_card Q P
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.relIndex_eq_one] at ha
    exact hQP.not_ge ha
  exact (dvd_pow_self 2 ha0).trans (ha ▸ h1)

theorem exists_elementaryEight_le_of_unitaryFour_twoCore (Q : Subgroup H)
    (hQ : CFSG.pCore 2 H = Q) (hCQ : Subgroup.centralizer (Q : Set H) ≤ Q)
    (e : Q ≃* unitaryFourW K hK) (h3 : 3 ∣ Q.index) (P : Sylow 2 H) (hQP : Q < P) :
    ∃ E : Subgroup H, E ≤ P ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
      Nat.card E = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hcomm, hsq, hcard⟩ := exists_elementaryEight_of_unitaryFour_twoCore Q hQ hCQ e h3
    (two_dvd_index_of_lt_sylow P hQP)
  have hE₀ : IsPGroup 2 E₀ := fun g => ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩
  obtain ⟨S', hS'⟩ := hE₀.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S' P
  refine ⟨E₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS' hy)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hsq x hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

theorem unitaryFour_twoCore_threeIndex_overgroup_rank (Q : Subgroup H)
    (hQ : Q = CFSG.pCore 2 H) (hCQ : Subgroup.centralizer (Q : Set H) ≤ Q)
    (hU : ∃ (T : Type) (_ : Group T) (U : Sylow 2 T),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2 ∧
        Nonempty (Q ≃* (U : Subgroup T)))
    (h3 : 3 ∣ Q.index) (P : Sylow 2 H) (hQP : Q < P) :
    3 ≤ CFSG.pRank 2 (P : Subgroup H) := by
  obtain ⟨T, _, U, hT, ⟨eQU⟩⟩ := hU
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨eUW⟩ := nonempty_sylow_equiv_unitaryFourW hT U (GaloisField 2 4) hK
  obtain ⟨E, hEP, hcomm, hsq, hcard⟩ :=
    exists_elementaryEight_le_of_unitaryFour_twoCore Q hQ.symm hCQ (eQU.trans eUW) h3 P hQP
  let A : Subgroup (P : Subgroup H) := E.subgroupOf P
  have hA : IsElementaryAbelian 2 A := {
    toIsMulCommutative := {
      is_comm := {
        comm := fun a b => Subtype.ext (Subtype.ext (hcomm _ a.2 _ b.2))
      }
    }
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro a
      exact Subtype.ext (Subtype.ext (hsq _ a.2))
  }
  have hAcard : Nat.card A = 2 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv, hcard]
    norm_num
  have hbdd : BddAbove {r : ℕ | ∃ B : Subgroup (P : Subgroup H),
      IsElementaryAbelian 2 B ∧ Nat.card B = 2 ^ r} := by
    refine ⟨Nat.card (P : Subgroup H), ?_⟩
    rintro r ⟨B, -, hB⟩
    calc r ≤ 2 ^ r := Nat.lt_two_pow_self.le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card (P : Subgroup H) := Nat.card_le_card_of_injective _ Subtype.val_injective
  exact le_csSup hbdd ⟨A, hA, hAcard⟩

end Core

end

end CFSG.RankTwoShapes
