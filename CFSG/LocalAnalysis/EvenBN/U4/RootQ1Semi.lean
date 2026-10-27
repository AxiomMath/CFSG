module

public import CFSG.LocalAnalysis.EvenBN.U4.RootP1Weights
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.SemilinearPlane

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient

section ModSubgroup

variable {Γ : Type*} [Group Γ] {E : Subgroup Γ}

theorem mul_inv_mem_trans {x y z : Γ} (h₁ : x * y⁻¹ ∈ E) (h₂ : y * z⁻¹ ∈ E) : x * z⁻¹ ∈ E := by
  have := mul_mem h₁ h₂
  rwa [mul_assoc, inv_mul_cancel_left] at this

theorem mul_inv_mem_symm {x y : Γ} (h₁ : x * y⁻¹ ∈ E) : y * x⁻¹ ∈ E := by
  have := inv_mem h₁
  rwa [mul_inv_rev, inv_inv] at this

theorem mul_inv_mem_conj {n x y : Γ} (hn : n ∈ normalizer (E : Set Γ)) (h₁ : x * y⁻¹ ∈ E) :
    (n * x * n⁻¹) * (n * y * n⁻¹)⁻¹ ∈ E := by
  have := (mem_normalizer_iff.1 hn _).1 h₁
  rwa [show n * (x * y⁻¹) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹)⁻¹ by group] at this

theorem commutator_conj (x y i : Γ) :
    (i⁻¹ * x * i) * (i⁻¹ * y * i) * (i⁻¹ * x * i)⁻¹ * (i⁻¹ * y * i)⁻¹ =
      i⁻¹ * (x * y * x⁻¹ * y⁻¹) * i := by
  group

end ModSubgroup

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem normalizer_Q1_le_normalizer_E (hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) ≤
      normalizer (miyamotoEG h L η Q : Set G) := by
  intro g hg
  have hgP := hS.normalizer_Q1_le_normalizer_P1 hg
  refine mem_normalizer_fintype fun e he => ?_
  rw [SetLike.mem_coe, ← hS.centerIn_P1] at he ⊢
  obtain ⟨heP, heC⟩ := mem_inf.1 he
  refine mem_inf.2 ⟨(mem_normalizer_iff.1 hgP e).1 heP, mem_centralizer_iff.2 fun x hx => ?_⟩
  have hx' : g⁻¹ * x * g ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := by
    have := (mem_normalizer_iff.1 (inv_mem hgP) x).1 hx
    rwa [inv_inv] at this
  have hc : g⁻¹ * x * g * e = e * (g⁻¹ * x * g) := mem_centralizer_iff.1 heC _ hx'
  calc x * (g * e * g⁻¹) = g * (g⁻¹ * x * g * e) * g⁻¹ := by group
    _ = g * (e * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
    _ = g * e * g⁻¹ * x := by group

theorem commutator_mul_left_of_mem_F1 (hS : Setting h L η t Q T) {x f₀ y : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) (hf₀ : f₀ ∈ miyamotoF1G h L η t)
    (hy : y ∈ miyamotoF1G h L η t) :
    f₀ * x * y * (f₀ * x)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hz : x * y * x⁻¹ ∈ miyamotoF1G h L η t :=
    (mem_normalizer_iff.1 (hS.P1_le_normalizer_F1 hx) y).1 hy
  calc f₀ * x * y * (f₀ * x)⁻¹ * y⁻¹ = f₀ * (x * y * x⁻¹) * f₀⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hS.F1_comm hf₀ hz, mul_inv_cancel_right]

theorem commutator_mul_right_mod_E (hS : Setting h L η t Q T) {x w y : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) (hw : w ∈ miyamotoFG h L η t Q)
    (hy : y ∈ miyamotoF1G h L η t) :
    (x * (w * y) * x⁻¹ * (w * y)⁻¹) * (x * y * x⁻¹ * y⁻¹)⁻¹ ∈ miyamotoEG h L η Q := by
  have hcF : x * y * x⁻¹ * y⁻¹ ∈ miyamotoF1G h L η t :=
    hS.F_le_F1 (hS.commutator_P1_F1_mem_F hx hy)
  have hd : x * w * x⁻¹ * w⁻¹ ∈ miyamotoEG h L η Q := by
    have := inv_mem (hS.commutator_F_P1_mem_E hw hx)
    rwa [show (w * x * w⁻¹ * x⁻¹)⁻¹ = x * w * x⁻¹ * w⁻¹ by group] at this
  have hcomm := hS.F1_comm (hS.F_le_F1 hw) hcF
  have e : (x * (w * y) * x⁻¹ * (w * y)⁻¹) * (x * y * x⁻¹ * y⁻¹)⁻¹ =
      (x * w * x⁻¹ * w⁻¹) * (w * (x * y * x⁻¹ * y⁻¹) * w⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹) := by
    group
  rw [e, hcomm, mul_inv_cancel_right, mul_inv_cancel, mul_one]
  exact hd

theorem commutator_mul_left_mod_E (hS : Setting h L η t Q T) {x x' y : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η)
    (hx' : x' ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) (hy : y ∈ miyamotoF1G h L η t) :
    (x * x' * y * (x * x')⁻¹ * y⁻¹) * ((x * y * x⁻¹ * y⁻¹) * (x' * y * x'⁻¹ * y⁻¹))⁻¹ ∈
      miyamotoEG h L η Q := by
  have hcF : x * y * x⁻¹ * y⁻¹ ∈ miyamotoF1G h L η t :=
    hS.F_le_F1 (hS.commutator_P1_F1_mem_F hx hy)
  have hc'F : x' * y * x'⁻¹ * y⁻¹ ∈ miyamotoFG h L η t Q := hS.commutator_P1_F1_mem_F hx' hy
  have hd : x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x' * y * x'⁻¹ * y⁻¹)⁻¹ ∈ miyamotoEG h L η Q := by
    have := inv_mem (hS.commutator_F_P1_mem_E hc'F hx)
    rwa [show ((x' * y * x'⁻¹ * y⁻¹) * x * (x' * y * x'⁻¹ * y⁻¹)⁻¹ * x⁻¹)⁻¹ =
      x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x' * y * x'⁻¹ * y⁻¹)⁻¹ by group] at this
  have hcomm := hS.F1_comm (hS.F_le_F1 hc'F) hcF
  have e : (x * x' * y * (x * x')⁻¹ * y⁻¹) * ((x * y * x⁻¹ * y⁻¹) * (x' * y * x'⁻¹ * y⁻¹))⁻¹ =
      (x * (x' * y * x'⁻¹ * y⁻¹) * x⁻¹ * (x' * y * x'⁻¹ * y⁻¹)⁻¹) *
        ((x' * y * x'⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) * (x' * y * x'⁻¹ * y⁻¹)⁻¹ *
          (x * y * x⁻¹ * y⁻¹)⁻¹) := by
    group
  rw [e, hcomm, mul_inv_cancel_right, mul_inv_cancel, mul_one]
  exact hd

theorem mem_F1_of_commutator_mem_E (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η)
    (hc : ∀ y ∈ miyamotoF1G h L η t, x * y * x⁻¹ * y⁻¹ ∈ miyamotoEG h L η Q) :
    x ∈ miyamotoF1G h L η t := by
  obtain ⟨f₀, hf₀, p, hp, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hx
  have hpP1 : p ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η := mem_sup_right hp
  have hpA : p ∈ miyamotoA1G h L η := by
    refine hS.mem_A1_of_commutator_mem_ZP hp fun a ha => ?_
    have haF := hS.A1_le_F1 ha
    have h1 := hc a haF
    rw [hS.commutator_mul_left_of_mem_F1 hpP1 hf₀ haF] at h1
    have h2 : p * a * p⁻¹ * a⁻¹ ∈ miyamotoA1G h L η :=
      mul_mem ((mem_normalizer_iff.1 (hS.PG_le_normalizer_A1 hp) a).1 ha) (inv_mem ha)
    rw [← hS.E_inf_A1]
    exact mem_inf.2 ⟨h1, h2⟩
  exact mul_mem hf₀ (hS.A1_le_F1 hpA)

def IsBalanced (hS : Setting h L η t Q T) (φ : K → K) : Prop :=
  ∃ ψ : G → G, (∀ y ∈ miyamotoF1G h L η t, ψ y ∈ miyamotoF1G h L η t) ∧
    ∀ (κ : K), ∀ y ∈ miyamotoF1G h L η t,
      (hS.rootElt (φ κ) * y * (hS.rootElt (φ κ))⁻¹ * y⁻¹) *
        (hS.rootElt κ * ψ y * (hS.rootElt κ)⁻¹ * (ψ y)⁻¹)⁻¹ ∈ miyamotoEG h L η Q

theorem torusElt_mul (hS : Setting h L η t Q T) (p p' : Kˣ × Kˣ) (hp : miyamotoIParam h p = 1)
    (hp' : miyamotoIParam h p' = 1) :
    hS.torusElt p hp * hS.torusElt p' hp' =
      hS.torusElt (p * p') (by rw [map_mul, hp, hp', mul_one]) := by
  simp only [torusElt]
  rw [← L.coe_mul, ← map_mul]
  congr 3
  exact Subtype.ext (map_mul (miyamotoIHom h) p p').symm

theorem exists_conj_eq_mul_of_weightB (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) (hpB : miyamotoWeightB h p = 1) {y : G}
    (hy : y ∈ miyamotoF1G h L η t) :
    (∃ w ∈ miyamotoFG h L η t Q, (hS.torusElt p hp)⁻¹ * y * hS.torusElt p hp = w * y) ∧
      ∃ w ∈ miyamotoFG h L η t Q, hS.torusElt p hp * y * (hS.torusElt p hp)⁻¹ = w * y := by
  refine ⟨⟨_, hS.conj_mem_F_of_weightB p hp hpB hy, by group⟩, ?_⟩
  have hpinv : miyamotoIParam h p⁻¹ = 1 := by rw [map_inv, hp, inv_one]
  have hpB' : miyamotoWeightB h p⁻¹ = 1 := by rw [map_inv, hpB, inv_one]
  have := hS.conj_mem_F_of_weightB p⁻¹ hpinv hpB' hy
  rw [← hS.torusElt_inv p hp, inv_inv] at this
  exact ⟨_, this, by group⟩

theorem IsBalanced.eq_mul (hS : Setting h L η t Q T) {φ : K → K} (hφ : hS.IsBalanced φ)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (lam κ : K) : φ (lam * κ) = lam * φ κ := by
  have : CharP K 2 := h.charP
  have hφ0 : φ 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  by_cases hlam : lam = 0
  · rw [hlam, zero_mul, zero_mul, hφ0]
  obtain ⟨ψ, hψ, hbal⟩ := hφ
  obtain ⟨p, hp, hpB, hpA⟩ := exists_miyamotoIParam_eq_one_weightB_eq_one h (Units.mk0 lam hlam)
  set i := hS.torusElt p hp with hi
  have hiI := hS.torusElt_mem_IG p hp
  have hiE := hS.IG_le_normalizer_E hiI
  have hconj : ∀ a : K, i⁻¹ * hS.rootElt a * i = hS.rootElt (lam * a) := fun a => by
    rw [hi, hS.torusElt_conj_rootElt p hp a, hpA, Units.val_mk0]
  set a := φ (lam * κ)
  set b := lam * φ κ
  have key : ∀ y ∈ miyamotoF1G h L η t,
      (hS.rootElt a * y * (hS.rootElt a)⁻¹ * y⁻¹) *
        (hS.rootElt b * y * (hS.rootElt b)⁻¹ * y⁻¹)⁻¹ ∈ miyamotoEG h L η Q := by
    intro y hy
    have hψy := hψ y hy
    obtain ⟨w, hw, hwe⟩ := (hS.exists_conj_eq_mul_of_weightB p hp hpB hψy).2
    rw [← hi] at hwe
    have h1 : (hS.rootElt (lam * κ) * ψ y * (hS.rootElt (lam * κ))⁻¹ * (ψ y)⁻¹) *
        (i⁻¹ * (hS.rootElt κ * ψ y * (hS.rootElt κ)⁻¹ * (ψ y)⁻¹) * i)⁻¹ ∈
          miyamotoEG h L η Q := by
      have e : hS.rootElt (lam * κ) * ψ y * (hS.rootElt (lam * κ))⁻¹ * (ψ y)⁻¹ =
          i⁻¹ * (hS.rootElt κ * (w * ψ y) * (hS.rootElt κ)⁻¹ * (w * ψ y)⁻¹) * i := by
        rw [← hwe, ← hconj κ]
        group
      rw [e]
      have := mul_inv_mem_conj (inv_mem hiE)
        (hS.commutator_mul_right_mod_E (hS.rootElt_mem_P1 κ) hw hψy)
      simpa only [inv_inv] using this
    obtain ⟨w', hw', hw'e⟩ := (hS.exists_conj_eq_mul_of_weightB p hp hpB hy).1
    rw [← hi] at hw'e
    have h2 : (i⁻¹ * (hS.rootElt (φ κ) * y * (hS.rootElt (φ κ))⁻¹ * y⁻¹) * i) *
        (hS.rootElt b * y * (hS.rootElt b)⁻¹ * y⁻¹)⁻¹ ∈ miyamotoEG h L η Q := by
      have e : i⁻¹ * (hS.rootElt (φ κ) * y * (hS.rootElt (φ κ))⁻¹ * y⁻¹) * i =
          hS.rootElt b * (w' * y) * (hS.rootElt b)⁻¹ * (w' * y)⁻¹ := by
        rw [← hw'e, ← hconj (φ κ), commutator_conj]
      rw [e]
      exact hS.commutator_mul_right_mod_E (hS.rootElt_mem_P1 b) hw' hy
    have h3 : (i⁻¹ * (hS.rootElt κ * ψ y * (hS.rootElt κ)⁻¹ * (ψ y)⁻¹) * i) *
        (i⁻¹ * (hS.rootElt (φ κ) * y * (hS.rootElt (φ κ))⁻¹ * y⁻¹) * i)⁻¹ ∈
          miyamotoEG h L η Q := by
      have := mul_inv_mem_conj (inv_mem hiE) (mul_inv_mem_symm (hbal κ y hy))
      simpa only [inv_inv] using this
    exact mul_inv_mem_trans (mul_inv_mem_trans (mul_inv_mem_trans (hbal (lam * κ) y hy) h1) h3)
      h2
  have hab : hS.rootElt (a + b) ∈ miyamotoF1G h L η t := by
    refine hS.mem_F1_of_commutator_mem_E (hS.rootElt_mem_P1 _) fun y hy => ?_
    have hbF : hS.rootElt b * y * (hS.rootElt b)⁻¹ * y⁻¹ ∈ miyamotoF1G h L η t :=
      hS.F_le_F1 (hS.commutator_P1_F1_mem_F (hS.rootElt_mem_P1 b) hy)
    have hsq := hS.F1_mul_self _ hbF
    have hinv : (hS.rootElt b * y * (hS.rootElt b)⁻¹ * y⁻¹)⁻¹ =
        hS.rootElt b * y * (hS.rootElt b)⁻¹ * y⁻¹ := inv_eq_of_mul_eq_one_right hsq
    have h1 := hS.commutator_mul_left_mod_E (hS.rootElt_mem_P1 a) (hS.rootElt_mem_P1 b) hy
    rw [← hS.rootElt_add] at h1
    have h2 := key y hy
    rw [hinv] at h2
    have := mul_mem h1 h2
    rwa [inv_mul_cancel_right] at this
  rw [hS.rootElt_mem_F1_iff] at hab
  have := CharTwo.add_eq_zero.1 hab
  exact this

theorem torusElt_congr (hS : Setting h L η t Q T) {p p' : Kˣ × Kˣ} (e : p = p')
    (hp : miyamotoIParam h p = 1) (hp' : miyamotoIParam h p' = 1) :
    hS.torusElt p hp = hS.torusElt p' hp' := by
  subst e
  rfl

theorem isBalanced_mul (hS : Setting h L η t Q T) {c : K} (hc : c ∈ h.fixedField) :
    hS.IsBalanced (fun κ => c * κ) := by
  have : CharP K 2 := h.charP
  have hc' : h.bar c = c := hc
  by_cases hc0 : c = 0
  · refine ⟨fun _ => 1, fun _ _ => one_mem _, fun κ y _ => ?_⟩
    simp [hc0, hS.rootElt_zero]
  have hq : 2 ^ (f - 1) * 2 = 2 ^ f := by
    rw [← pow_succ]
    congr 1
    have := h.one_le
    omega
  set b : K := c ^ 2 ^ (f - 1) with hb
  have hbb : b * b = c := by
    rw [hb, ← pow_two, ← pow_mul, hq, ← h.bar_apply, hc']
  have hb0 : b ≠ 0 := pow_ne_zero _ hc0
  have hbar : h.bar b = b := by rw [hb, map_pow, hc']
  set u : Kˣ := Units.mk0 b hb0 with hu
  have hbarinv : h.bar b⁻¹ = b⁻¹ := by rw [map_inv₀, hbar]
  have hp₂ : miyamotoIParam h (u, u) = 1 := by
    apply Units.ext
    simp only [miyamotoIParam, MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
      MonoidHom.inv_apply, MonoidHom.coe_comp, Function.comp_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      Units.val_one, hu, Units.val_mk0, hbar]
    field_simp
  have hj : miyamotoIParam h (u, u⁻¹) = 1 := by
    apply Units.ext
    simp only [miyamotoIParam, MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
      MonoidHom.inv_apply, MonoidHom.coe_comp, Function.comp_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      Units.val_one, hu, Units.val_mk0, hbar, hbarinv]
    field_simp
  have hjp : (u, u⁻¹) * (u, u) = (Units.mk0 c hc0, 1) := by
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · simp [hu, hbb]
    · simp
  have hp₁ : miyamotoIParam h (Units.mk0 c hc0, 1) = 1 := by
    rw [← hjp, map_mul, hj, hp₂, mul_one]
  have hp₁B : miyamotoWeightB h (Units.mk0 c hc0, 1) = 1 := by
    apply Units.ext
    simp
  have hp₁A : ((miyamotoWeightA (Units.mk0 c hc0, 1) : Kˣ) : K) = c := by simp
  have hp₂A : ((miyamotoWeightA (u, u) : Kˣ) : K) = 1 := by simp [hu, hb0]
  have hjC : miyamotoWeightC h (u, u⁻¹) = 1 := by
    apply Units.ext
    simp [hu, hbarinv, hb0]
  set i₁ := hS.torusElt (Units.mk0 c hc0, 1) hp₁ with hi₁
  set i₂ := hS.torusElt (u, u) hp₂ with hi₂
  set ij := hS.torusElt (u, u⁻¹) hj with hij
  have hi₁eq : i₁ = ij * i₂ := by
    rw [hi₁, hij, hi₂, hS.torusElt_mul]
    exact hS.torusElt_congr hjp.symm _ _
  have hi₂I : i₂ ∈ miyamotoIG h L η := hS.torusElt_mem_IG (u, u) hp₂
  have hi₁E : i₁ ∈ normalizer (miyamotoEG h L η Q : Set G) :=
    hS.IG_le_normalizer_E (hS.torusElt_mem_IG _ hp₁)
  have hi₂E : i₂ ∈ normalizer (miyamotoEG h L η Q : Set G) := hS.IG_le_normalizer_E hi₂I
  have hi₂F : i₂ ∈ normalizer (miyamotoF1G h L η t : Set G) := hS.IG_le_normalizer_F1 hi₂I
  refine ⟨fun y => i₂⁻¹ * y * i₂, fun y hy => ?_, fun κ y hy => ?_⟩
  · have := (mem_normalizer_iff.1 (inv_mem hi₂F) y).1 hy
    rwa [inv_inv] at this
  obtain ⟨w, hw, hwe⟩ := (hS.exists_conj_eq_mul_of_weightB _ hp₁ hp₁B hy).2
  rw [← hi₁] at hwe
  have hconj₁ : i₁⁻¹ * hS.rootElt κ * i₁ = hS.rootElt (c * κ) := by
    rw [hi₁, hS.torusElt_conj_rootElt, hp₁A]
  have hconj₂ : i₂⁻¹ * hS.rootElt κ * i₂ = hS.rootElt κ := by
    rw [hi₂, hS.torusElt_conj_rootElt, hp₂A, one_mul]
  have h1 : (hS.rootElt (c * κ) * y * (hS.rootElt (c * κ))⁻¹ * y⁻¹) *
      (i₁⁻¹ * (hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) * i₁)⁻¹ ∈ miyamotoEG h L η Q := by
    have e : hS.rootElt (c * κ) * y * (hS.rootElt (c * κ))⁻¹ * y⁻¹ =
        i₁⁻¹ * (hS.rootElt κ * (w * y) * (hS.rootElt κ)⁻¹ * (w * y)⁻¹) * i₁ := by
      rw [← hwe, ← hconj₁]
      group
    rw [e]
    have := mul_inv_mem_conj (inv_mem hi₁E)
      (hS.commutator_mul_right_mod_E (hS.rootElt_mem_P1 κ) hw hy)
    simpa only [inv_inv] using this
  have hvF := hS.commutator_P1_F1_mem_F (hS.rootElt_mem_P1 κ) hy
  have h2 : (i₁⁻¹ * (hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) * i₁) *
      (i₂⁻¹ * (hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) * i₂)⁻¹ ∈ miyamotoEG h L η Q := by
    have hE := hS.conj_mem_E_of_weightC (u, u⁻¹) hj hjC hvF
    rw [← hij] at hE
    have := (mem_normalizer_iff.1 (inv_mem hi₂E) _).1 hE
    rw [hi₁eq]
    convert this using 1
    group
  have e3 : i₂⁻¹ * (hS.rootElt κ * y * (hS.rootElt κ)⁻¹ * y⁻¹) * i₂ =
      hS.rootElt κ * (i₂⁻¹ * y * i₂) * (hS.rootElt κ)⁻¹ * (i₂⁻¹ * y * i₂)⁻¹ := by
    conv_rhs => rw [← hconj₂]
    exact (commutator_conj _ _ _).symm
  have := mul_inv_mem_trans h1 h2
  rwa [e3] at this

theorem conjAct_conjAct_inv (hS : Setting h L η t Q T)
    (g : normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) (κ : K) :
    hS.conjAct g (hS.conjAct g⁻¹ κ) = κ := by
  have := congrArg (fun φ : AddMonoid.End K => φ κ)
    (show hS.conjAct g * hS.conjAct g⁻¹ = 1 by rw [← map_mul, mul_inv_cancel, map_one])
  exact this

theorem IsBalanced.conjAct (hS : Setting h L η t Q T) {φ : K → K} (hφ : hS.IsBalanced φ)
    (g : normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) :
    hS.IsBalanced (fun κ => hS.conjAct g (φ (hS.conjAct g⁻¹ κ))) := by
  obtain ⟨ψ, hψ, hbal⟩ := hφ
  have hgF := hS.normalizer_Q1_le_normalizer_F1 g.2
  have hgE := hS.normalizer_Q1_le_normalizer_E g.2
  have hF1 : ∀ y ∈ miyamotoF1G h L η t, (g : G)⁻¹ * y * g ∈ miyamotoF1G h L η t := fun y hy => by
    have := (mem_normalizer_iff.1 (inv_mem hgF) y).1 hy
    rwa [inv_inv] at this
  refine ⟨fun y => (g : G) * ψ ((g : G)⁻¹ * y * g) * (g : G)⁻¹,
    fun y hy => (mem_normalizer_iff.1 hgF _).1 (hψ _ (hF1 y hy)), fun κ y hy => ?_⟩
  simp only
  set κ₀ := hS.conjAct g⁻¹ κ with hκ₀
  set y' := (g : G)⁻¹ * y * g with hy'
  have hy'F := hF1 y hy
  have hψ' := hψ y' hy'F
  have hx := hS.conj_mem_P1 g.2 (hS.rootElt_mem_P1 (φ κ₀))
  have hspec := hS.coordP1_spec hx
  have e1 : hS.rootElt (hS.conjAct g (φ κ₀)) * y * (hS.rootElt (hS.conjAct g (φ κ₀)))⁻¹ * y⁻¹ =
      (g : G) * (hS.rootElt (φ κ₀) * y' * (hS.rootElt (φ κ₀))⁻¹ * y'⁻¹) * (g : G)⁻¹ := by
    rw [hS.conjAct_apply]
    set x := (g : G) * hS.rootElt (φ κ₀) * (g : G)⁻¹ with hxdef
    have hsx : hS.rootElt (hS.coordP1 x) = (x * (hS.rootElt (hS.coordP1 x))⁻¹)⁻¹ * x := by group
    rw [hsx, hS.commutator_mul_left_of_mem_F1 hx (inv_mem hspec) hy, hxdef, hy']
    group
  have hx₀ := hS.conj_mem_P1 g.2 (hS.rootElt_mem_P1 κ₀)
  have hspec₀ := hS.coordP1_spec hx₀
  have hcoord : hS.coordP1 ((g : G) * hS.rootElt κ₀ * (g : G)⁻¹) = κ := by
    rw [← hS.conjAct_apply, hκ₀, hS.conjAct_conjAct_inv]
  rw [hcoord] at hspec₀
  have hψg : (g : G) * ψ y' * (g : G)⁻¹ ∈ miyamotoF1G h L η t := (mem_normalizer_iff.1 hgF _).1 hψ'
  have e2 : hS.rootElt κ * ((g : G) * ψ y' * (g : G)⁻¹) * (hS.rootElt κ)⁻¹ *
      ((g : G) * ψ y' * (g : G)⁻¹)⁻¹ =
      (g : G) * (hS.rootElt κ₀ * ψ y' * (hS.rootElt κ₀)⁻¹ * (ψ y')⁻¹) * (g : G)⁻¹ := by
    set x₀ := (g : G) * hS.rootElt κ₀ * (g : G)⁻¹ with hx₀def
    have hsx : hS.rootElt κ = (x₀ * (hS.rootElt κ)⁻¹)⁻¹ * x₀ := by group
    rw [hsx, hS.commutator_mul_left_of_mem_F1 hx₀ (inv_mem hspec₀) hψg, hx₀def]
    group
  rw [e1, e2]
  exact mul_inv_mem_conj hgE (hbal κ₀ y' hy'F)

theorem exists_conjAct_mul (hS : Setting h L η t Q T)
    (g : normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) :
    ∃ σ : h.fixedField →+* h.fixedField, ∀ (c : h.fixedField) (κ : K),
      hS.conjAct g ((c : K) * κ) = (σ c : K) * hS.conjAct g κ := by
  have hρρ' : ∀ κ, hS.conjAct g (hS.conjAct g⁻¹ κ) = κ := hS.conjAct_conjAct_inv g
  have hρ'ρ : ∀ κ, hS.conjAct g⁻¹ (hS.conjAct g κ) = κ := fun κ => by
    have := hS.conjAct_conjAct_inv g⁻¹ κ
    rwa [inv_inv] at this
  set ν : K → K := fun c => hS.conjAct g (c * hS.conjAct g⁻¹ 1) with hνdef
  have hν : ∀ c ∈ h.fixedField, ∀ κ, hS.conjAct g (c * κ) = ν c * hS.conjAct g κ := by
    intro c hc κ
    have hbal := (hS.isBalanced_mul hc).conjAct hS g
    have hadd : ∀ a b, (fun κ => hS.conjAct g (c * hS.conjAct g⁻¹ κ)) (a + b) =
        (fun κ => hS.conjAct g (c * hS.conjAct g⁻¹ κ)) a +
          (fun κ => hS.conjAct g (c * hS.conjAct g⁻¹ κ)) b := fun a b => by
      simp only [map_add, mul_add]
    have := IsBalanced.eq_mul hS hbal hadd (hS.conjAct g κ) 1
    simp only [mul_one, hρ'ρ] at this
    rw [this, mul_comm]
  have hνmul : ∀ c ∈ h.fixedField, ∀ d ∈ h.fixedField, ν (c * d) = ν c * ν d := by
    intro c hc d _
    simp only [hνdef]
    rw [mul_assoc, hν c hc]
  have hνone : ν 1 = 1 := by simp only [hνdef, one_mul, hρρ']
  have hνpow : ∀ c ∈ h.fixedField, ∀ n : ℕ, ν (c ^ n) = ν c ^ n := by
    intro c hc n
    induction n with
    | zero => simp [hνone]
    | succ n ih => rw [pow_succ, hνmul _ (pow_mem hc n) _ hc, ih, pow_succ]
  have hνmem : ∀ c ∈ h.fixedField, ν c ∈ h.fixedField := by
    intro c hc
    have hc' : h.bar c = c := hc
    change h.bar (ν c) = ν c
    rw [h.bar_apply, ← hνpow c hc, ← h.bar_apply, hc']
  refine ⟨{ toFun := fun c => ⟨ν c, hνmem c c.2⟩
            map_one' := Subtype.ext hνone
            map_mul' := fun c d => Subtype.ext (hνmul c c.2 d d.2)
            map_zero' := Subtype.ext (by simp [hνdef])
            map_add' := fun c d => Subtype.ext (by simp [hνdef, add_mul]) },
    fun c κ => hν c c.2 κ⟩

theorem exists_mem_normalizer_Q1_crossed_not_mem_F1 (hS : Setting h L η t Q T) :
    ∃ g ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G),
      (∀ x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η, g * x * g⁻¹ * x⁻¹ ∈ miyamotoF1G h L η t) ∧
        (g * t)⁻¹ * (t * g) ∉ miyamotoF1G h L η t := by
  have := h.finite
  by_contra hcon
  push Not at hcon
  have hHN : normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) ≤
      normalizer (miyamotoF1G h L η t : Set G) := hS.normalizer_Q1_le_normalizer_F1
  set φ : normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) →*
      Bar (miyamotoF1G h L η t) := (proj (miyamotoF1G h L η t)).comp (inclusion hHN) with hφ
  have hrange : φ.range = bar (miyamotoF1G h L η t)
      (normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) := by
    rw [hφ, MonoidHom.range_comp, inclusion_range]
    rfl
  have hindex : ((centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t)))).comap φ).index =
      (2 ^ f) ^ 2 := by
    rw [index_comap, hrange]
    exact hS.orbit_shape_bar.2.2
  have hker : hS.conjAct.ker ≤
      (centralizer ({hS.tBar} : Set (Bar (miyamotoF1G h L η t)))).comap φ := by
    intro g hg
    have h2 := hcon g g.2 ((hS.conjAct_eq_one_iff g).1 (MonoidHom.mem_ker.1 hg))
    rw [mem_comap, mem_centralizer_singleton_iff]
    change proj _ ⟨(g : G), hHN g.2⟩ * hS.tBar = hS.tBar * proj _ ⟨(g : G), hHN g.2⟩
    rw [tBar, ← map_mul, ← map_mul, proj_eq_proj_iff]
    exact h2
  have hdvd : 2 ^ (2 * f) ∣ hS.conjAct.ker.index := by
    have := index_dvd_of_le hker
    rwa [hindex, ← pow_mul, mul_comm] at this
  have hF : Nat.card h.fixedField = 2 ^ f := h.card_fixedField
  have hW : Module.finrank h.fixedField K = 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := h.fixedField) (V := K)
    rw [h.card_eq_sq, hF] at h1
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
    exact (Nat.pow_right_injective hq h1).symm
  refine not_two_pow_two_mul_dvd_index_ker hF hW hS.conjAct (fun g => ?_) hdvd
  obtain ⟨σ, hσ⟩ := hS.exists_conjAct_mul g
  exact ⟨σ, fun c w => by simp only [Subfield.smul_def, smul_eq_mul]; exact hσ c w⟩

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
