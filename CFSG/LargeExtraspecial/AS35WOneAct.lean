module

public import CFSG.LargeExtraspecial.AS35WOneCore
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.LargeExtraspecial

namespace AS35W

variable {X : Type} [Group X] {z : X} {R : Subgroup X}

@[expose] def InSix (z a b x : X) : Prop :=
  x = a ∨ x = a * z ∨ x = b ∨ x = b * z ∨ x = a * b ∨ x = a * b * z

open Classical in
@[expose] noncomputable def cls (z a b x : X) : Fin 3 :=
  if x = a ∨ x = a * z then 0 else if x = b ∨ x = b * z then 1 else 2

@[expose] def rep (a b : X) : Fin 3 → X := ![a, b, a * b]

namespace QuatLike

variable (h : QuatLike z R)
include h

theorem ne_one_of_sq {c : X} (hc : c ^ 2 = z) : c ≠ 1 := fun h1 => h.z_ne_one (by
  rw [← hc, h1, one_pow])

theorem ne_z_of_sq {c : X} (hc : c ^ 2 = z) : c ≠ z := fun h1 => h.z_ne_one (by
  have := hc
  rw [h1, sq, h.z_mul_z] at this
  exact this.symm)

theorem distinct {a b : X} (hbR : b ∈ R) (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hne : b ≠ a ∧ b ≠ a * z) :
    a * z ≠ b ∧ a ≠ b * z ∧ a * z ≠ b * z ∧ a * b ≠ a ∧ a * b ≠ a * z ∧ a * b ≠ b ∧
      a * b ≠ b * z ∧ a * b * z ≠ a ∧ a * b * z ≠ a * z ∧ a * b * z ≠ b ∧ a * b * z ≠ b * z := by
  have hb1 := h.ne_one_of_sq hb
  have hbz := h.ne_z_of_sq hb
  have ha1 := h.ne_one_of_sq ha
  have haz := h.ne_z_of_sq ha
  have hzz := h.z_mul_z
  have hzb : b * z = z * b := h.comm_z b hbR
  have hzi := h.z_inv
  refine ⟨fun e => hne.2 e.symm, fun e => hne.2 ?_, fun e => hne.1 (mul_right_cancel e).symm,
    fun e => hb1 (mul_left_cancel (e.trans (mul_one a).symm)), fun e => hbz (mul_left_cancel e),
    fun e => ha1 (mul_right_cancel (e.trans (one_mul b).symm)),
    fun e => haz (mul_right_cancel (e.trans hzb)), fun e => hbz ?_, fun e => hb1 ?_,
    fun e => haz ?_, fun e => ha1 ?_⟩
  · rw [e, mul_assoc, hzz, mul_one]
  · have h1 : a * (b * z) = a * 1 := by rw [← mul_assoc, e, mul_one]
    have h2 : b * z = 1 := mul_left_cancel h1
    rw [← hzi]
    exact eq_inv_of_mul_eq_one_left h2
  · have h1 : a * b = a := mul_right_cancel e
    exact mul_left_cancel (h1.trans (mul_one a).symm)
  · have h1 : a * z * b = 1 * b := by
      rw [one_mul, mul_assoc, ← hzb, ← mul_assoc]
      exact e
    have h2 : a * z = 1 := mul_right_cancel h1
    rw [← hzi]
    exact eq_inv_of_mul_eq_one_left h2
  · have h1 : a * b = b := mul_right_cancel e
    exact mul_right_cancel (h1.trans (one_mul b).symm)

variable {a b : X} (haR : a ∈ R) (hbR : b ∈ R) (ha : a ^ 2 = z) (hb : b ^ 2 = z)
  (hne : b ≠ a ∧ b ≠ a * z)

include hbR ha hb hne in
theorem cls_vals : cls z a b a = 0 ∧ cls z a b (a * z) = 0 ∧ cls z a b b = 1 ∧
    cls z a b (b * z) = 1 ∧ cls z a b (a * b) = 2 ∧ cls z a b (a * b * z) = 2 := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩ := h.distinct hbR ha hb hne
  have e1 : b * z ≠ a := fun e => d2 e.symm
  have e2 : b * z ≠ a * z := fun e => d3 e.symm
  refine ⟨by simp [cls], by simp [cls], ?_, ?_, ?_, ?_⟩ <;>
    simp [cls, hne.1, hne.2, e1, e2, d4, d5, d6, d7, d8, d9, d10, d11]

include hbR ha hb hne in
theorem cls_rep (i : Fin 3) : cls z a b (rep a b i) = i := by
  obtain ⟨c1, -, c3, -, c5, -⟩ := h.cls_vals hbR ha hb hne
  fin_cases i
  · exact c1
  · exact c3
  · exact c5

include hbR ha hb hne in
theorem cls_rep_mul_z (i : Fin 3) : cls z a b (rep a b i * z) = i := by
  obtain ⟨-, c2, -, c4, -, c6⟩ := h.cls_vals hbR ha hb hne
  fin_cases i
  · exact c2
  · exact c4
  · exact c6

include hbR ha hb hne in
theorem rep_cls {x : X} (hx : InSix z a b x) :
    x = rep a b (cls z a b x) ∨ x = rep a b (cls z a b x) * z := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h.cls_vals hbR ha hb hne
  rcases hx with e | e | e | e | e | e <;> rw [e]
  · rw [c1]; left; rfl
  · rw [c2]; right; rfl
  · rw [c3]; left; rfl
  · rw [c4]; right; rfl
  · rw [c5]; left; rfl
  · rw [c6]; right; rfl

include hbR ha hb hne in
theorem cls_mul_z {x : X} (hx : InSix z a b x) : cls z a b (x * z) = cls z a b x := by
  rcases h.rep_cls hbR ha hb hne hx with e | e
  · rw [e, h.cls_rep_mul_z hbR ha hb hne, h.cls_rep hbR ha hb hne]
  · rw [e, mul_assoc, h.z_mul_z, mul_one, h.cls_rep_mul_z hbR ha hb hne,
      h.cls_rep hbR ha hb hne]

include haR hbR ha hb hne in
theorem inSix_of_mem {x : X} (hxR : x ∈ R) (hx1 : x ≠ 1) (hxz : x ≠ z) : InSix z a b x := by
  rcases h.mem_eight haR hbR ha hb hne hxR with e | e | e
  · exact absurd e hx1
  · exact absurd e hxz
  · exact e

include haR hbR in
theorem inSix_mem {x : X} (hx : InSix z a b x) : x ∈ R := by
  have hz := h.z_mem
  rcases hx with e | e | e | e | e | e <;> rw [e]
  · exact haR
  · exact R.mul_mem haR hz
  · exact hbR
  · exact R.mul_mem hbR hz
  · exact R.mul_mem haR hbR
  · exact R.mul_mem (R.mul_mem haR hbR) hz

include ha hne in
theorem inSix_ne {x : X} (hx : InSix z a b x) (hb' : b ^ 2 = z) : x ≠ 1 ∧ x ≠ z := by
  have hzi := h.z_inv
  have hzz := h.z_mul_z
  have k1 : ∀ c : X, c ≠ 1 → c ≠ z → c * z ≠ 1 ∧ c * z ≠ z := fun c c1 cz =>
    ⟨fun e => cz (by rw [← hzi]; exact eq_inv_of_mul_eq_one_left e),
      fun e => c1 (mul_right_cancel (e.trans (one_mul z).symm))⟩
  have ha' := And.intro (h.ne_one_of_sq ha) (h.ne_z_of_sq ha)
  have hb'' := And.intro (h.ne_one_of_sq hb') (h.ne_z_of_sq hb')
  have hab := And.intro (h.mul_ne_one ha hne) (h.mul_ne_z ha hne)
  rcases hx with e | e | e | e | e | e <;> rw [e]
  · exact ha'
  · exact k1 _ ha'.1 ha'.2
  · exact hb''
  · exact k1 _ hb''.1 hb''.2
  · exact hab
  · exact k1 _ hab.1 hab.2

include haR hbR ha hb hne in
theorem conj_formulas : a * b * a⁻¹ = b * z ∧ b * a * b⁻¹ = a * z ∧
    a * b * a * (a * b)⁻¹ = a * z ∧ a * b * b * (a * b)⁻¹ = b * z := by
  have hba : b * a = a * b * z := h.mul_comm_eq haR hbR ha hb hne
  have hza : a * z = z * a := h.comm_z a haR
  have hzb : b * z = z * b := h.comm_z b hbR
  have hzz := h.z_mul_z
  have ha2 : a * a = z := by rw [← sq, ha]
  have hb2 : b * b = z := by rw [← sq, hb]
  have hai : a⁻¹ = a * z := h.inv_eq ha
  have hbi : b⁻¹ = b * z := h.inv_eq hb
  have h1 : a * b * a⁻¹ = b * z := by
    calc a * b * a⁻¹ = a * b * (a * z) := by rw [hai]
      _ = a * (b * a) * z := by group
      _ = a * (a * b * z) * z := by rw [hba]
      _ = (a * a) * b * (z * z) := by group
      _ = z * b := by rw [ha2, hzz, mul_one]
      _ = b * z := hzb.symm
  have h2 : b * a * b⁻¹ = a * z := by
    calc b * a * b⁻¹ = (b * a) * (b * z) := by rw [hbi]
      _ = (a * b * z) * (b * z) := by rw [hba]
      _ = a * (b * (z * b)) * z := by group
      _ = a * (b * (b * z)) * z := by rw [hzb]
      _ = a * (b * b) * (z * z) := by group
      _ = a * z := by rw [hb2, hzz, mul_one]
  refine ⟨h1, h2, ?_, ?_⟩
  · calc a * b * a * (a * b)⁻¹ = a * (b * a * b⁻¹) * a⁻¹ := by group
      _ = a * (a * z) * a⁻¹ := by rw [h2]
      _ = a * (z * a) * a⁻¹ := by rw [hza]
      _ = a * z := by group
  · calc a * b * b * (a * b)⁻¹ = a * b * a⁻¹ := by group
      _ = b * z := h1

include haR hbR ha hb hne in
theorem mem_of_fixes {e : X} (hez : e * z = z * e)
    (hfs : ∀ c : X, c * z = z * c → (∀ r ∈ R, c * r = r * c) → c ∈ R)
    (hea : e * a * e⁻¹ = a ∨ e * a * e⁻¹ = a * z) (heb : e * b * e⁻¹ = b ∨ e * b * e⁻¹ = b * z) :
    e ∈ R := by
  obtain ⟨c1, c2, c3, c4⟩ := h.conj_formulas haR hbR ha hb hne
  have key : ∀ r ∈ R, r * a * r⁻¹ = e * a * e⁻¹ → r * b * r⁻¹ = e * b * e⁻¹ → e ∈ R := by
    intro r hr hra hrb
    have hc : r⁻¹ * e ∈ R := by
      refine hfs _ ?_ ?_
      · rw [mul_assoc, hez, ← mul_assoc, ← mul_assoc]
        congr 1
        have := h.comm_z r hr
        calc r⁻¹ * z = r⁻¹ * (z * r) * r⁻¹ := by group
          _ = r⁻¹ * (r * z) * r⁻¹ := by rw [this]
          _ = z * r⁻¹ := by group
      · have hca : r⁻¹ * e * a = a * (r⁻¹ * e) := by
          calc r⁻¹ * e * a = r⁻¹ * (e * a * e⁻¹) * e := by group
            _ = r⁻¹ * (r * a * r⁻¹) * e := by rw [hra]
            _ = a * (r⁻¹ * e) := by group
        have hcb : r⁻¹ * e * b = b * (r⁻¹ * e) := by
          calc r⁻¹ * e * b = r⁻¹ * (e * b * e⁻¹) * e := by group
            _ = r⁻¹ * (r * b * r⁻¹) * e := by rw [hrb]
            _ = b * (r⁻¹ * e) := by group
        have hcz : r⁻¹ * e * z = z * (r⁻¹ * e) := by
          have := h.comm_z r hr
          calc r⁻¹ * e * z = r⁻¹ * (e * z) := by group
            _ = r⁻¹ * (z * e) := by rw [hez]
            _ = r⁻¹ * (z * r) * r⁻¹ * e := by group
            _ = r⁻¹ * (r * z) * r⁻¹ * e := by rw [this]
            _ = z * (r⁻¹ * e) := by group
        have hC : Commute (r⁻¹ * e) a := hca
        have hD : Commute (r⁻¹ * e) b := hcb
        have hZ : Commute (r⁻¹ * e) z := hcz
        intro x hx
        by_cases hx1 : x = 1
        · rw [hx1, one_mul, mul_one]
        by_cases hxz : x = z
        · rw [hxz]; exact hcz
        rcases h.inSix_of_mem haR hbR ha hb hne hx hx1 hxz with e' | e' | e' | e' | e' | e' <;>
          rw [e']
        · exact hca
        · exact (hC.mul_right hZ).eq
        · exact hcb
        · exact (hD.mul_right hZ).eq
        · exact (hC.mul_right hD).eq
        · exact ((hC.mul_right hD).mul_right hZ).eq
    have : e = r * (r⁻¹ * e) := by group
    rw [this]
    exact R.mul_mem hr hc
  have h1 : (1 : X) * a * 1⁻¹ = a := by group
  have h1' : (1 : X) * b * 1⁻¹ = b := by group
  have hab : a * b ∈ R := R.mul_mem haR hbR
  have haa : a * a * a⁻¹ = a := by group
  have hbb : b * b * b⁻¹ = b := by group
  rcases hea with hea | hea <;> rcases heb with heb | heb
  · exact key 1 R.one_mem (h1.trans hea.symm) (h1'.trans heb.symm)
  · exact key a haR (haa.trans hea.symm) (c1.trans heb.symm)
  · exact key b hbR (c2.trans hea.symm) (hbb.trans heb.symm)
  · exact key (a * b) hab (c3.trans hea.symm) (c4.trans heb.symm)

include haR hbR ha hb hne in
theorem inSix_conj {e x : X} (hez : e * z = z * e) (heR : ∀ r ∈ R, e * r * e⁻¹ ∈ R)
    (hx : InSix z a b x) : InSix z a b (e * x * e⁻¹) := by
  obtain ⟨hx1, hxz⟩ := h.inSix_ne ha hne hx hb
  refine h.inSix_of_mem haR hbR ha hb hne (heR x (h.inSix_mem haR hbR hx)) ?_ ?_
  · intro e1
    apply hx1
    have : x = e⁻¹ * (e * x * e⁻¹) * e := by group
    rw [this, e1]
    group
  · intro e1
    apply hxz
    have : x = e⁻¹ * (e * x * e⁻¹) * e := by group
    rw [this, e1]
    calc e⁻¹ * z * e = e⁻¹ * (z * e) := by group
      _ = e⁻¹ * (e * z) := by rw [hez]
      _ = z := by group

end QuatLike

theorem conj_mul_z {e : X} (hez : e * z = z * e) (w : X) :
    e * (w * z) * e⁻¹ = e * w * e⁻¹ * z := by
  have hconj : e * z * e⁻¹ = z := by rw [hez]; group
  calc e * (w * z) * e⁻¹ = (e * w * e⁻¹) * (e * z * e⁻¹) := by group
    _ = e * w * e⁻¹ * z := by rw [hconj]

theorem inSix_rep {z a b : X} (i : Fin 3) : InSix z a b (rep a b i) := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

@[reducible] noncomputable def classAction (h : QuatLike z R) {a b : X} (haR : a ∈ R)
    (hbR : b ∈ R) (ha : a ^ 2 = z) (hb : b ^ 2 = z) (hne : b ≠ a ∧ b ≠ a * z) (E : Subgroup X)
    (hEz : ∀ e ∈ E, e * z = z * e) (hER : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R) :
    MulAction E (Fin 3) where
  smul e i := cls z a b ((e : X) * rep a b i * (e : X)⁻¹)
  one_smul i := by
    change cls z a b ((1 : X) * rep a b i * (1 : X)⁻¹) = i
    rw [one_mul, inv_one, mul_one, h.cls_rep hbR ha hb hne]
  mul_smul e₁ e₂ i := by
    change cls z a b ((e₁ * e₂ : X) * rep a b i * (e₁ * e₂ : X)⁻¹) =
      cls z a b ((e₁ : X) * rep a b (cls z a b ((e₂ : X) * rep a b i * (e₂ : X)⁻¹)) *
        (e₁ : X)⁻¹)
    have hy := h.inSix_conj haR hbR ha hb hne (hEz _ e₂.2) (hER _ e₂.2) (inSix_rep i)
    have he : (e₁ * e₂ : X) * rep a b i * (e₁ * e₂ : X)⁻¹ =
        (e₁ : X) * ((e₂ : X) * rep a b i * (e₂ : X)⁻¹) * (e₁ : X)⁻¹ := by group
    rw [he]
    rcases h.rep_cls hbR ha hb hne hy with e | e
    · rw [← e]
    · have hw := h.inSix_conj haR hbR ha hb hne (hEz _ e₁.2) (hER _ e₁.2)
        (inSix_rep (cls z a b ((e₂ : X) * rep a b i * (e₂ : X)⁻¹)))
      have hz1 := conj_mul_z (hEz _ e₁.2) (rep a b (cls z a b ((e₂ : X) * rep a b i *
        (e₂ : X)⁻¹)))
      conv_lhs => rw [e]
      rw [hz1, h.cls_mul_z hbR ha hb hne hw]


theorem QuatLike.card_le_four [Finite X] (h : QuatLike z R) {a b : X} (haR : a ∈ R)
    (hbR : b ∈ R) (ha : a ^ 2 = z) (hb : b ^ 2 = z) (hne : b ≠ a ∧ b ≠ a * z) (E : Subgroup X)
    (hE2 : IsPGroup 2 E) (hEz : ∀ e ∈ E, e * z = z * e)
    (hER : ∀ e ∈ E, ∀ r ∈ R, e * r * e⁻¹ ∈ R)
    (hfs : ∀ c : X, c * z = z * c → (∀ r ∈ R, c * r = r * c) → c ∈ R)
    (hE1 : ∀ e ∈ E, e ∈ R → e = 1 ∨ e = z) : Nat.card E ≤ 4 := by
  let _ := classAction h haR hbR ha hb hne E hEz hER
  set φ := MulAction.toPermHom E (Fin 3) with hφ
  have hfix : ∀ k ∈ φ.ker, ∀ i : Fin 3,
      (k : X) * rep a b i * (k : X)⁻¹ = rep a b i ∨
        (k : X) * rep a b i * (k : X)⁻¹ = rep a b i * z := by
    intro k hk i
    have hki : k • i = i := by
      have := congrArg (fun σ : Equiv.Perm (Fin 3) => σ i) (MonoidHom.mem_ker.1 hk)
      simpa [hφ] using this
    change cls z a b ((k : X) * rep a b i * (k : X)⁻¹) = i at hki
    have hy := h.inSix_conj haR hbR ha hb hne (hEz _ k.2) (hER _ k.2) (inSix_rep i)
    have hr := h.rep_cls hbR ha hb hne hy
    rwa [hki] at hr
  have hker : ∀ k ∈ φ.ker, (k : X) = 1 ∨ (k : X) = z := fun k hk =>
    hE1 _ k.2 (h.mem_of_fixes haR hbR ha hb hne (hEz _ k.2) hfs (hfix k hk 0) (hfix k hk 1))
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact h.z_mul_z) h.z_ne_one
  have hcard_ker : Nat.card φ.ker ≤ 2 := by
    have hinj : Function.Injective (fun k : φ.ker => (⟨((k : E) : X), by
        rcases hker k k.2 with e | e
        · rw [e]; exact (Subgroup.zpowers z).one_mem
        · rw [e]; exact Subgroup.mem_zpowers z⟩ : Subgroup.zpowers z)) := by
      intro k₁ k₂ e
      have e' := congrArg Subtype.val e
      exact Subtype.ext (Subtype.ext e')
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_zpowers, hz2] at this
  have hmul := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker] at hmul
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hE2
  have hr6 : Nat.card φ.range ∣ 6 := by
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
    have := Subgroup.card_subgroup_dvd_card φ.range
    rwa [h6] at this
  have hrE : Nat.card φ.range ∣ 2 ^ n := by
    rw [← hn, ← hmul]
    exact Dvd.intro_left _ rfl
  obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hrE
  have hcard_range : Nat.card φ.range ≤ 2 := by
    rw [hm'] at hr6 ⊢
    rcases m with _ | _ | m
    · norm_num
    · norm_num
    · exfalso
      have h4 : 4 ∣ 2 ^ (m + 2) := ⟨2 ^ m, by ring⟩
      have := h4.trans hr6
      omega
  rw [← hmul]
  calc Nat.card φ.ker * Nat.card φ.range ≤ 2 * 2 := Nat.mul_le_mul hcard_ker hcard_range
    _ = 4 := rfl

end AS35W

end CFSG.LargeExtraspecial
