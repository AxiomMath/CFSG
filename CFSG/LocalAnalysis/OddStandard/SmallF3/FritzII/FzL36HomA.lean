module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzShape
public import Certificates.Data.FzJ36

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzJ36 CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] {t x₁ x₂ lam : G} {T₂ : Subgroup G} {a₁₂ a₂₂ a₃₂ : G}

@[simp] theorem fzl_q8Hom_a_one {p q : G} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.a 1) = p := by
  change zmod4Pow p 1 = p
  have : Fact (1 < 4) := ⟨by norm_num⟩
  unfold zmod4Pow
  rw [ZMod.val_one, pow_one]

@[simp] theorem fzl_q8Hom_xa_zero {p q : G} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.xa 0) = q := by
  change q * zmod4Pow p 0 = q
  rw [zmod4Pow_zero, mul_one]

@[simp] theorem fzl_q8Hom_a_two {p q : G} (h : IsQ8Pair p q) :
    q8Hom h (QuaternionGroup.a 2) = p ^ 2 := by
  change zmod4Pow p 2 = p ^ 2
  unfold zmod4Pow
  congr 1

private theorem fzl_q8Hom_commute {p q p' q' : G} (hp : IsQ8Pair p q)
    (hp' : IsQ8Pair p' q') (hpp : Commute p p') (hpq : Commute p q')
    (hqp : Commute q p') (hqq : Commute q q') :
    ∀ x y : Q8, Commute (q8Hom hp x) (q8Hom hp' y) := by
  intro x y
  cases x with
  | a i =>
    cases y with
    | a j => exact (hpp.pow_left i.val).pow_right j.val
    | xa j =>
      exact ((hpq.pow_left i.val)).mul_right ((hpp.pow_left i.val).pow_right j.val)
  | xa i =>
    cases y with
    | a j => exact ((hqp.pow_right j.val)).mul_left ((hpp.pow_right j.val).pow_left i.val)
    | xa j =>
      exact (hqq.mul_right (hqp.pow_right j.val)).mul_left
        ((hpq.pow_left i.val).mul_right ((hpp.pow_left i.val).pow_right j.val))

private theorem fzl_comm₁₂ (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    ∀ x y : Q8, Commute (q8Hom hsh.quat₁ x) (q8Hom hsh.quat₂ y) :=
  fzl_q8Hom_commute hsh.quat₁ hsh.quat₂
    (hsh.comm₁₂ (x₁ * t) (by simp) (x₂ * t) (by simp))
    (hsh.comm₁₂ (x₁ * t) (by simp) a₂₂ (by simp))
    (hsh.comm₁₂ a₁₂ (by simp) (x₂ * t) (by simp))
    (hsh.comm₁₂ a₁₂ (by simp) a₂₂ (by simp))

private theorem fzl_comm₁₃ (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    ∀ x y : Q8, Commute (q8Hom hsh.quat₁ x) (q8Hom hsh.quat₃ y) :=
  fzl_q8Hom_commute hsh.quat₁ hsh.quat₃
    (hsh.comm₁₃ (x₁ * t) (by simp) ((x₁ * x₂)⁻¹ * t) (by simp))
    (hsh.comm₁₃ (x₁ * t) (by simp) a₃₂ (by simp))
    (hsh.comm₁₃ a₁₂ (by simp) ((x₁ * x₂)⁻¹ * t) (by simp))
    (hsh.comm₁₃ a₁₂ (by simp) a₃₂ (by simp))

private theorem fzl_comm₂₃ (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    ∀ x y : Q8, Commute (q8Hom hsh.quat₂ x) (q8Hom hsh.quat₃ y) :=
  fzl_q8Hom_commute hsh.quat₂ hsh.quat₃
    (hsh.comm₂₃ (x₂ * t) (by simp) ((x₁ * x₂)⁻¹ * t) (by simp))
    (hsh.comm₂₃ (x₂ * t) (by simp) a₃₂ (by simp))
    (hsh.comm₂₃ a₂₂ (by simp) ((x₁ * x₂)⁻¹ * t) (by simp))
    (hsh.comm₂₃ a₂₂ (by simp) a₃₂ (by simp))

def fzl_fn (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) : N3 →* G :=
  (q8Hom hsh.quat₁).noncommCoprod
    ((q8Hom hsh.quat₂).noncommCoprod (q8Hom hsh.quat₃) (fzl_comm₂₃ hsh))
    (fun a bc => (fzl_comm₁₂ hsh a bc.1).mul_right (fzl_comm₁₃ hsh a bc.2))

@[simp] theorem fzl_fn_apply (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂)
    (a b c : Q8) :
    fzl_fn hsh (a, b, c) =
      q8Hom hsh.quat₁ a * (q8Hom hsh.quat₂ b * q8Hom hsh.quat₃ c) := by
  simp [fzl_fn]

@[simp] theorem fzl_fn_one (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    fzl_fn hsh 1 = 1 := by
  rw [show (1 : N3) = (1, 1, 1) from rfl, fzl_fn_apply, map_one, map_one, map_one, mul_one,
    mul_one]

private theorem fzl_conj_conj {X : Type*} [Group X] {g a b : X} (h : g * a * g⁻¹ = b)
    (hg : g ^ 2 = 1) : g * b * g⁻¹ = a := by
  have hg' : g * g = 1 := by rw [← pow_two]; exact hg
  rw [← h]
  calc g * (g * a * g⁻¹) * g⁻¹ = (g * g) * a * (g⁻¹ * g⁻¹) := by group
    _ = a := by rw [hg', ← mul_inv_rev, hg', inv_one]; group

private theorem fzl_conj_eq_self_of_commute {X : Type*} [Group X] {g x : X}
    (h : Commute g x) : g * x * g⁻¹ = x := by
  rw [h.eq]; group

def fzl_lamHom (lam : G) (h : lam ^ 2 = 1) : Multiplicative (ZMod 2) →* G where
  toFun e := if e = 1 then 1 else lam
  map_one' := by simp
  map_mul' a b := by
    have h2 : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
    have hne : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    have hmul : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    have hl : lam * lam = 1 := by rw [← pow_two]; exact h
    rcases h2 a with rfl | rfl <;> rcases h2 b with rfl | rfl <;> simp [hne, hmul, hl]

private theorem fzl_ofAdd_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

@[simp] theorem fzl_lamHom_one (lam : G) (h : lam ^ 2 = 1) :
    fzl_lamHom lam h 1 = 1 := by simp [fzl_lamHom]

@[simp] theorem fzl_lamHom_gen (lam : G) (h : lam ^ 2 = 1) :
    fzl_lamHom lam h (Multiplicative.ofAdd 1) = lam := by
  simp [fzl_lamHom, fzl_ofAdd_ne_one]

private theorem fzl_lam_conj₁ (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (q : Q8) :
    lam * q8Hom hsh.quat₁ q * lam⁻¹ = q8Hom hsh.quat₂ q := by
  cases q with
  | a i =>
      change lam * (x₁ * t) ^ i.val * lam⁻¹ = (x₂ * t) ^ i.val
      rw [← MulAut.conj_apply, map_pow]
      simp only [MulAut.conj_apply, hsh.lam_a₁₁]
  | xa i =>
      change lam * (a₁₂ * (x₁ * t) ^ i.val) * lam⁻¹ = a₂₂ * (x₂ * t) ^ i.val
      rw [← MulAut.conj_apply, map_mul, map_pow]
      simp only [MulAut.conj_apply, hsh.lam_a₁₂, hsh.lam_a₁₁]

private theorem fzl_lam_conj₂ (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (q : Q8) :
    lam * q8Hom hsh.quat₂ q * lam⁻¹ = q8Hom hsh.quat₁ q := by
  have hx : lam * (x₂ * t) * lam⁻¹ = x₁ * t := fzl_conj_conj hsh.lam_a₁₁ hsh.lam_sq
  have ha : lam * a₂₂ * lam⁻¹ = a₁₂ := fzl_conj_conj hsh.lam_a₁₂ hsh.lam_sq
  cases q with
  | a i =>
      change lam * (x₂ * t) ^ i.val * lam⁻¹ = (x₁ * t) ^ i.val
      rw [← MulAut.conj_apply, map_pow]
      simp only [MulAut.conj_apply, hx]
  | xa i =>
      change lam * (a₂₂ * (x₂ * t) ^ i.val) * lam⁻¹ = a₁₂ * (x₁ * t) ^ i.val
      rw [← MulAut.conj_apply, map_mul, map_pow]
      simp only [MulAut.conj_apply, ha, hx]

private theorem fzl_lam_conj₃ (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) (q : Q8) :
    lam * q8Hom hsh.quat₃ q * lam⁻¹ = q8Hom hsh.quat₃ q := by
  have hx : lam * ((x₁ * x₂)⁻¹ * t) * lam⁻¹ = (x₁ * x₂)⁻¹ * t :=
    fzl_conj_eq_self_of_commute hsh.lam_comm₃.1
  have ha : lam * a₃₂ * lam⁻¹ = a₃₂ := fzl_conj_eq_self_of_commute hsh.lam_comm₃.2
  cases q with
  | a i =>
      change lam * ((x₁ * x₂)⁻¹ * t) ^ i.val * lam⁻¹ = ((x₁ * x₂)⁻¹ * t) ^ i.val
      rw [← MulAut.conj_apply, map_pow]
      simp only [MulAut.conj_apply, hx]
  | xa i =>
      change lam * (a₃₂ * ((x₁ * x₂)⁻¹ * t) ^ i.val) * lam⁻¹
        = a₃₂ * ((x₁ * x₂)⁻¹ * t) ^ i.val
      rw [← MulAut.conj_apply, map_mul, map_pow]
      simp only [MulAut.conj_apply, ha, hx]

private theorem fzl_lam_conj_triple (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂)
    (a b c : Q8) :
    lam * (q8Hom hsh.quat₁ a * (q8Hom hsh.quat₂ b * q8Hom hsh.quat₃ c)) * lam⁻¹
      = q8Hom hsh.quat₁ b * (q8Hom hsh.quat₂ a * q8Hom hsh.quat₃ c) := by
  rw [← MulAut.conj_apply, map_mul, map_mul]
  simp only [MulAut.conj_apply, fzl_lam_conj₁ hsh a, fzl_lam_conj₂ hsh b,
    fzl_lam_conj₃ hsh c]
  calc q8Hom hsh.quat₂ a * (q8Hom hsh.quat₁ b * q8Hom hsh.quat₃ c)
      = (q8Hom hsh.quat₂ a * q8Hom hsh.quat₁ b) * q8Hom hsh.quat₃ c := by group
    _ = (q8Hom hsh.quat₁ b * q8Hom hsh.quat₂ a) * q8Hom hsh.quat₃ c := by
        rw [(fzl_comm₁₂ hsh b a).eq.symm]
    _ = q8Hom hsh.quat₁ b * (q8Hom hsh.quat₂ a * q8Hom hsh.quat₃ c) := by group

theorem fzl_forall_eq (e : Multiplicative (ZMod 2)) :
    e = 1 ∨ e = Multiplicative.ofAdd 1 := by
  have h : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
  exact h e

private theorem fzl_coherence (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) :
    ∀ e : Multiplicative (ZMod 2),
      (fzl_fn hsh).comp ((act e).toMonoidHom) =
        (MulAut.conj (fzl_lamHom lam hsh.lam_sq e)).toMonoidHom.comp (fzl_fn hsh) := by
  intro e
  ext n
  obtain ⟨a, b, c⟩ := n
  rcases fzl_forall_eq e with rfl | rfl
  · simp [fzl_lamHom_one, act, MulAut.conj_apply]
  · have hact : (MulEquiv.toMonoidHom (act (Multiplicative.ofAdd 1))) (a, b, c)
        = (b, a, c) := by
      simp [act, fzl_ofAdd_ne_one, swapAut]
    simp only [MonoidHom.comp_apply, fzl_lamHom_gen, hact, fzl_fn_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (fzl_lam_conj_triple hsh a b c).symm

def fzl_pi (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂) : Model →* G :=
  SemidirectProduct.lift (fzl_fn hsh) (fzl_lamHom lam hsh.lam_sq) (fzl_coherence hsh)

@[simp] theorem fzl_pi_mk (hsh : FzSpShape t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂)
    (n : N3) (e : Multiplicative (ZMod 2)) :
    fzl_pi hsh ⟨n, e⟩ = fzl_fn hsh n * fzl_lamHom lam hsh.lam_sq e := by
  simp [fzl_pi, SemidirectProduct.lift]

end CFSG.OddStandard.SmallF3.FritzII
