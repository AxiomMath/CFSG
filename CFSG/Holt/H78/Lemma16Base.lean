module

public import CFSG.Holt.H78.Lemma16Basic

public section

namespace CFSG.Holt.H78

open Subgroup

namespace L16

variable {S : Type*} [Group S]

open Classical in
noncomputable def tauR (R : Subgroup S) (x : S) : ZMod 2 := if x ∈ R then 0 else 1

theorem tauR_eq_zero_iff {R : Subgroup S} {x : S} : tauR R x = 0 ↔ x ∈ R := by
  unfold tauR; split_ifs with h <;> simp [h]

theorem tauR_eq_one_iff {R : Subgroup S} {x : S} : tauR R x = 1 ↔ x ∉ R := by
  unfold tauR; split_ifs with h <;> simp [h]

theorem tauR_congr {R : Subgroup S} {x y : S} (hxy : x ∈ R ↔ y ∈ R) : tauR R x = tauR R y := by
  by_cases hx : x ∈ R
  · rw [tauR_eq_zero_iff.2 hx, tauR_eq_zero_iff.2 (hxy.1 hx)]
  · rw [tauR_eq_one_iff.2 hx, tauR_eq_one_iff.2 (fun hy => hx (hxy.2 hy))]

theorem tauR_inv (R : Subgroup S) (x : S) : tauR R x⁻¹ = tauR R x :=
  tauR_congr inv_mem_iff

theorem tauR_mul {R T : Subgroup S} (h2 : ∀ x ∈ T, ∀ y ∈ T, x ∉ R → y ∉ R → x * y ∈ R)
    {x y : S} (hx : x ∈ T) (hy : y ∈ T) : tauR R (x * y) = tauR R x + tauR R y := by
  by_cases hxR : x ∈ R <;> by_cases hyR : y ∈ R
  · rw [tauR_eq_zero_iff.2 hxR, tauR_eq_zero_iff.2 hyR, tauR_eq_zero_iff.2 (mul_mem hxR hyR)]
    rfl
  · have : x * y ∉ R := fun hxy => hyR (by simpa using mul_mem (inv_mem hxR) hxy)
    rw [tauR_eq_zero_iff.2 hxR, tauR_eq_one_iff.2 hyR, tauR_eq_one_iff.2 this]; rfl
  · have : x * y ∉ R := fun hxy => hxR (by simpa using mul_mem hxy (inv_mem hyR))
    rw [tauR_eq_one_iff.2 hxR, tauR_eq_zero_iff.2 hyR, tauR_eq_one_iff.2 this]; rfl
  · rw [tauR_eq_one_iff.2 hxR, tauR_eq_one_iff.2 hyR,
      tauR_eq_zero_iff.2 (h2 x hx y hy hxR hyR)]; rfl

def eps (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

theorem eps_add (a b : ZMod 2) : eps (a + b) = eps a * eps b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem eps_mul_self (a : ZMod 2) : eps a * eps a = 1 := by
  fin_cases a <;> rfl

theorem eps_eq (a : ZMod 2) : eps a = 1 - 2 * (if a = 1 then 1 else 0) := by
  fin_cases a <;> rfl

noncomputable def qR (R : Subgroup S) (x : S) : ZMod 2 := tauR R (x ^ 2)

noncomputable def bR (R : Subgroup S) (x z : S) : ZMod 2 := tauR R (x⁻¹ * z * x * z⁻¹)

namespace Setting

variable {φ : MulAut S} {A T R : Subgroup S} {N : ℕ} (h : Setting φ A T R N)
include h

theorem tauR_conj {a t : S} (ha : a ∈ A) : tauR R (a * t * a⁻¹) = tauR R t := by
  refine tauR_congr ⟨fun h1 => ?_, fun h1 => h.normR a ha t h1⟩
  have := h.normR a⁻¹ (inv_mem ha) _ h1
  simpa [mul_assoc] using this

theorem tauR_map {t : S} (ht : t ∈ T) : tauR R (φ t) = tauR R t := by
  refine tauR_congr ⟨fun h1 => ?_, fun h1 => h.mapR t h1⟩
  have : t = φ t * (t⁻¹ * φ t)⁻¹ := by group
  rw [this]; exact mul_mem h1 (inv_mem (h.trivT t ht))

variable (h2 : ∀ x ∈ T, ∀ y ∈ T, x ∉ R → y ∉ R → x * y ∈ R)
include h2

theorem qR_mul {x z : S} (hx : x ∈ A) (hz : z ∈ A) :
    qR R (x * z) = qR R x + bR R x z + qR R z := by
  have hx2 := h.sq x hx
  have hz2 := h.sq z hz
  have hc : x⁻¹ * z * x * z⁻¹ ∈ T := by
    have := h.comm_mem (inv_mem hx) hz
    simpa using this
  have e : (x * z) ^ 2 = x ^ 2 * (x⁻¹ * z * x * z⁻¹) * z ^ 2 := by
    rw [pow_two, pow_two, pow_two]; group
  unfold qR bR
  rw [e, tauR_mul h2 (mul_mem hx2 hc) hz2, tauR_mul h2 hx2 hc]

theorem bR_mul_left {x y z : S} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A) :
    bR R (x * y) z = bR R x z + bR R y z := by
  have hc : x⁻¹ * z * x * z⁻¹ ∈ T := by
    have := h.comm_mem (inv_mem hx) hz
    simpa using this
  have hc' : y⁻¹ * z * y * z⁻¹ ∈ T := by
    have := h.comm_mem (inv_mem hy) hz
    simpa using this
  have hyc : y⁻¹ * (x⁻¹ * z * x * z⁻¹) * y⁻¹⁻¹ ∈ T := h.normT _ (inv_mem hy) _ hc
  have e : (x * y)⁻¹ * z * (x * y) * z⁻¹ =
      (y⁻¹ * (x⁻¹ * z * x * z⁻¹) * y⁻¹⁻¹) * (y⁻¹ * z * y * z⁻¹) := by group
  unfold bR
  rw [e, tauR_mul h2 hyc hc', h.tauR_conj (inv_mem hy)]

omit h in
theorem qR_of_mem {t : S} (ht : t ∈ T) : qR R t = 0 := by
  unfold qR
  rw [pow_two, tauR_mul h2 ht ht]
  generalize tauR R t = a
  fin_cases a <;> rfl

theorem bR_of_mem {x t : S} (hx : x ∈ A) (ht : t ∈ T) : bR R x t = 0 := by
  have hxt : x⁻¹ * t * x⁻¹⁻¹ ∈ T := h.normT _ (inv_mem hx) _ ht
  have e : x⁻¹ * t * x * t⁻¹ = (x⁻¹ * t * x⁻¹⁻¹) * t⁻¹ := by group
  unfold bR
  rw [e, tauR_mul h2 hxt (inv_mem ht), h.tauR_conj (inv_mem hx), tauR_inv]
  generalize tauR R t = a
  fin_cases a <;> rfl

theorem qR_mul_of_mem {x t : S} (hx : x ∈ A) (ht : t ∈ T) : qR R (x * t) = qR R x := by
  rw [h.qR_mul h2 hx (h.le_TA ht), h.bR_of_mem h2 hx ht, qR_of_mem h2 ht, add_zero, add_zero]

omit h2 in
theorem qR_map {x : S} (hx : x ∈ A) : qR R (φ x) = qR R x := by
  unfold qR
  rw [← map_pow, h.tauR_map (h.sq x hx)]

omit h h2 in
theorem qR_inv (x : S) : qR R x⁻¹ = qR R x := by
  unfold qR
  rw [inv_pow, tauR_inv]

omit h2 in
def radical : Subgroup S where
  carrier := {z | z ∈ A ∧ ∀ x ∈ A, x⁻¹ * z * x * z⁻¹ ∈ R}
  mul_mem' := by
    rintro z z' ⟨hz, hzR⟩ ⟨hz', hz'R⟩
    refine ⟨mul_mem hz hz', fun x hx => ?_⟩
    have e : x⁻¹ * (z * z') * x * (z * z')⁻¹ =
        (x⁻¹ * z * x * z⁻¹) * (z * (x⁻¹ * z' * x * z'⁻¹) * z⁻¹) := by group
    rw [e]
    exact mul_mem (hzR x hx) (h.normR z hz _ (hz'R x hx))
  one_mem' := ⟨one_mem A, fun x _ => by simp⟩
  inv_mem' := by
    rintro z ⟨hz, hzR⟩
    refine ⟨inv_mem hz, fun x hx => ?_⟩
    have e : x⁻¹ * z⁻¹ * x * z⁻¹⁻¹ = z⁻¹ * (x⁻¹ * z * x * z⁻¹)⁻¹ * z⁻¹⁻¹ := by group
    rw [e]
    exact h.normR _ (inv_mem hz) _ (inv_mem (hzR x hx))

omit h2 in
theorem radical_le : h.radical ≤ A := fun _ hz => hz.1

theorem le_radical : T ≤ h.radical := fun _ ht =>
  ⟨h.le_TA ht, fun _ hx => tauR_eq_zero_iff.1 (h.bR_of_mem h2 hx ht)⟩

omit h2 in
theorem map_mem_radical [Finite S] {z : S} (hz : z ∈ h.radical) : φ z ∈ h.radical := by
  refine ⟨h.mapA z hz.1, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := h.exists_map_eq hx
  have := h.mapR _ (hz.2 y hy)
  simpa [map_mul, map_inv] using this

theorem qR_eq_zero_of_mem_radical [Finite S] {z : S} (hz : z ∈ h.radical) : qR R z = 0 := by
  obtain ⟨w, hw, hwT⟩ := h.exists_twist h.radical_le (fun _ hb => h.map_mem_radical hb) hz
  have hzA := h.radical_le hz
  have hwA := h.radical_le hw
  have e : w⁻¹ * φ w = z * (z⁻¹ * (w⁻¹ * φ w)) := by group
  have h1 : qR R (w⁻¹ * φ w) = qR R z := by rw [e, h.qR_mul_of_mem h2 hzA hwT]
  have h3 : bR R w⁻¹ (φ w) = 0 :=
    tauR_eq_zero_iff.2 (by simpa using (h.map_mem_radical hw).2 _ (inv_mem hwA))
  rw [← h1, h.qR_mul h2 (inv_mem hwA) (h.mapA w hwA), h3, h.qR_map hwA, qR_inv, add_zero]
  generalize qR R w = a
  fin_cases a <;> rfl

omit h h2 in
open Classical in
theorem card_filter_mem [Fintype A] {B : Subgroup S} (hBA : B ≤ A) :
    (Finset.univ.filter fun z : A => (z : S) ∈ B).card = Nat.card B := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun z => ⟨z.1, z.2⟩
      invFun := fun b => ⟨⟨b, hBA b.2⟩, b.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open Classical in
theorem sum_eps_bR [Fintype A] (z : A) :
    ∑ x : A, eps (bR R x z) = if (z : S) ∈ h.radical then (Fintype.card A : ℤ) else 0 := by
  split_ifs with hz
  · have : ∀ x : A, bR R x z = 0 := fun x => tauR_eq_zero_iff.2 (hz.2 x x.2)
    simp [this, eps]
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀ : A, bR R x₀ z = 1 := by
      by_contra hne
      push Not at hne
      refine hz ⟨z.2, fun x hx => tauR_eq_zero_iff.1 ?_⟩
      exact (zmod_two_cases (bR R x z)).resolve_right (hne ⟨x, hx⟩)
    have hsum : ∑ x : A, eps (bR R x z) = ∑ x : A, eps (bR R (x₀ * x : A) z) :=
      (Fintype.sum_equiv (Equiv.mulLeft x₀) _ _ (fun _ => rfl)).symm
    have hneg : ∑ x : A, eps (bR R (x₀ * x : A) z) = -∑ x : A, eps (bR R x z) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [show ((x₀ * x : A) : S) = (x₀ : S) * x from rfl, h.bR_mul_left h2 x₀.2 x.2 z.2, hx₀,
        eps_add, show eps 1 = -1 from rfl, neg_one_mul]
    omega

theorem gauss_sum_sq [Finite S] [Fintype A] :
    (∑ x : A, eps (qR R x)) ^ 2 = (Fintype.card A : ℤ) * Nat.card h.radical := by
  classical
  rw [pow_two, Finset.sum_mul_sum]
  have step : ∀ x : A, ∑ y : A, eps (qR R x) * eps (qR R y) =
      ∑ z : A, eps (bR R x z) * eps (qR R z) := by
    intro x
    rw [← Fintype.sum_equiv (Equiv.mulLeft x) (fun z => eps (qR R x) * eps (qR R (x * z : A)))
      _ (fun _ => rfl)]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [show ((x * z : A) : S) = (x : S) * z from rfl, h.qR_mul h2 x.2 z.2, eps_add, eps_add]
    have := eps_mul_self (qR R x)
    linear_combination (eps (bR R x z) * eps (qR R z)) * this
  rw [Finset.sum_congr rfl (fun x _ => step x), Finset.sum_comm]
  have step2 : ∀ z : A, ∑ x : A, eps (bR R x z) * eps (qR R z) =
      (Fintype.card A : ℤ) * (if (z : S) ∈ h.radical then 1 else 0) := by
    intro z
    rw [← Finset.sum_mul, h.sum_eps_bR h2 z]
    split_ifs with hz
    · rw [h.qR_eq_zero_of_mem_radical h2 hz]; simp [eps]
    · simp
  rw [Finset.sum_congr rfl (fun z _ => step2 z), ← Finset.mul_sum, Finset.sum_boole,
    card_filter_mem h.radical_le]

omit h h2 in
open Classical in
theorem sum_eps_qR [Fintype A] :
    ∑ x : A, eps (qR R x) =
      (Fintype.card A : ℤ) - 2 * (Finset.univ.filter fun x : A => qR R x = 1).card := by
  classical
  rw [Finset.sum_congr rfl (fun x _ => eps_eq _), Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole]
  simp

open Classical in
theorem orderOf_dvd_card_filter [Finite S] [Fintype A] :
    orderOf φ ∣ (Finset.univ.filter fun x : A => qR R x = 1).card := by
  have hA : ∀ x : S, (MulAut.toPerm S φ) x ∈ A ↔ x ∈ A := h.map_mem_iff
  let σA : Equiv.Perm A := (MulAut.toPerm S φ).subtypePerm hA
  have hσA : ∀ x : A, ((σA x : A) : S) = φ x := fun _ => rfl
  have hq : ∀ x : A, qR R (σA x : S) = 1 ↔ qR R (x : S) = 1 := fun x => by
    rw [hσA, h.qR_map x.2]
  let σ : Equiv.Perm {x : A // qR R x = 1} := σA.subtypePerm hq
  have hpow : ∀ (j : ℕ) (x : {x : A // qR R x = 1}),
      (((σ ^ j) x : A) : S) = (φ ^ j) ((x : A) : S) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ, Equiv.Perm.mul_apply, ih, pow_succ, MulAut.mul_apply]
      rfl
  have hk : σ ^ orderOf φ = 1 :=
    Equiv.ext fun x => Subtype.ext (Subtype.ext (by rw [hpow, pow_orderOf_eq_one]; rfl))
  have hfree : ∀ (x : {x : A // qR R x = 1}) (j : ℕ), (σ ^ j) x = x → orderOf φ ∣ j := by
    intro x j hx
    have h1 : (φ ^ j) ((x : A) : S) = x := by rw [← hpow, hx]
    rcases h.semi j _ x.1.2 (by rw [h1, inv_mul_cancel]; exact one_mem T) with hT | h1'
    · exact absurd x.2 (by rw [qR_of_mem h2 hT]; decide)
    · exact orderOf_dvd_of_pow_eq_one h1'
  have := dvd_natCard_of_perm σ hk hfree
  rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at this

theorem sq_mem_of_two [Finite S] : ∀ a ∈ A, a ^ 2 ∈ R := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  have hkb := h.orderOf_dvd_card_filter h2
  have hcount := sum_eps_qR (R := R) (A := A)
  have hgauss := h.gauss_sum_sq h2
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (h.pgroup.to_subgroup T)
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 (h.pgroup.to_subgroup h.radical)
  have har : a ≤ r := by
    have := Subgroup.card_dvd_of_le (h.le_radical h2)
    rw [ha, hr] at this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  have hA : Fintype.card A = 2 ^ (N + a) := by
    have := Subgroup.relIndex_mul_card T A
    rw [inf_eq_left.2 h.le_TA, h.index, ha] at this
    rw [← Nat.card_eq_fintype_card, ← this, pow_add]
  have hb₁lt : (Finset.univ.filter fun x : A => qR R x = 1).card < 2 ^ (N + a) := by
    rw [← hA, ← Finset.card_univ]
    apply Finset.card_lt_card
    refine Finset.filter_ssubset.2 ⟨1, Finset.mem_univ _, ?_⟩
    rw [show ((1 : A) : S) = 1 from rfl, qR_of_mem h2 (one_mem T)]
    exact zero_ne_one
  have hsq : ((2 : ℤ) ^ (N + a) - 2 * (Finset.univ.filter fun x : A => qR R x = 1).card) ^ 2 =
      2 ^ (N + a + r) := by
    have e1 : ((2 : ℤ) ^ (N + a)) = (Fintype.card A : ℤ) := by rw [hA]; push_cast; ring
    rw [e1, ← hcount, hgauss, hr, hA]
    push_cast
    ring
  have hb0 := eq_zero_of_sq_eq_two_pow h.order' hkb hb₁lt har hsq
  intro x hx
  have hq : qR R x ≠ 1 := by
    intro hq
    have hmem : (⟨x, hx⟩ : A) ∈ Finset.univ.filter fun x : A => qR R x = 1 := by
      simp [hq]
    rw [Finset.card_eq_zero.1 hb0] at hmem
    simp at hmem
  exact tauR_eq_zero_iff.1 ((zmod_two_cases _).resolve_right hq)

omit h2 in
theorem inf_eq_of_sq_mem (hsqR : ∀ a ∈ A, a ^ 2 ∈ R) : (autComm φ A ⊔ R) ⊓ T = R := by
  have hcR : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ R :=
    fun a ha b hb => comm_mem_of_sq_mem h.normR hsqR ha hb
  let D : Subgroup S :=
    { carrier := {y | y ∈ A ∧ ∃ w ∈ A, y⁻¹ * (w⁻¹ * φ w) ∈ R}
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, w₁, hw₁, hr₁⟩ ⟨hy₂, w₂, hw₂, hr₂⟩
        refine ⟨mul_mem hy₁ hy₂, w₁ * w₂, mul_mem hw₁ hw₂, ?_⟩
        have hF₁ : w₁⁻¹ * φ w₁ ∈ A := mul_mem (inv_mem hw₁) (h.mapA _ hw₁)
        have hc := hcR _ (inv_mem hF₁) _ (inv_mem hw₂)
        have e : (y₁ * y₂)⁻¹ * ((w₁ * w₂)⁻¹ * φ (w₁ * w₂)) =
            (y₂⁻¹ * ((y₁⁻¹ * (w₁⁻¹ * φ w₁)) * ((w₁⁻¹ * φ w₁)⁻¹ * w₂⁻¹ *
              (w₁⁻¹ * φ w₁)⁻¹⁻¹ * w₂⁻¹⁻¹)) * y₂⁻¹⁻¹) * (y₂⁻¹ * (w₂⁻¹ * φ w₂)) := by
          rw [map_mul]; group
        rw [e]
        exact mul_mem (h.normR _ (inv_mem hy₂) _ (mul_mem hr₁ hc)) hr₂
      one_mem' := ⟨one_mem A, 1, one_mem A, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, w, hw, hr⟩
        refine ⟨inv_mem hy, w⁻¹, inv_mem hw, ?_⟩
        have e : y⁻¹⁻¹ * (w⁻¹⁻¹ * φ w⁻¹) =
            (y * w) * (y⁻¹ * (w⁻¹ * φ w))⁻¹ * (y * w)⁻¹ * (y * w * y⁻¹ * w⁻¹) := by
          rw [map_inv]; group
        rw [e]
        exact mul_mem (h.normR _ (mul_mem hy hw) _ (inv_mem hr)) (hcR _ hy _ hw) }
  have hle : autComm φ A ⊔ R ≤ D := by
    refine sup_le ?_ ?_
    · rw [autComm, Subgroup.closure_le]
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨mul_mem (inv_mem ha) (h.mapA a ha), a, ha, by simp⟩
    · intro r hr
      exact ⟨h.le_TA (h.le_RT hr), 1, one_mem A, by simpa using inv_mem hr⟩
  refine le_antisymm (fun y hy => ?_) (le_inf le_sup_right h.le_RT)
  obtain ⟨-, w, hw, hwR⟩ := hle hy.1
  have hwT : w⁻¹ * φ w ∈ T := by
    have : w⁻¹ * φ w = y * (y⁻¹ * (w⁻¹ * φ w)) := by group
    rw [this]; exact mul_mem hy.2 (h.le_RT hwR)
  have hwR' := h.trivT w ((h.twist_mem_iff hw).1 hwT)
  have : y = (w⁻¹ * φ w) * (y⁻¹ * (w⁻¹ * φ w))⁻¹ := by group
  rw [this]; exact mul_mem hwR' (inv_mem hwR)

theorem inf_eq_of_two [Finite S] : (autComm φ A ⊔ R) ⊓ T = R :=
  h.inf_eq_of_sq_mem (h.sq_mem_of_two h2)

end Setting

end L16

end CFSG.Holt.H78