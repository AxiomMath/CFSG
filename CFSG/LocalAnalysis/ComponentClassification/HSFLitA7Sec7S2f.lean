module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2e

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem act_Q₁_E₁ {c : X} (hc : c ∈ C.D₁.Q₁) : act c C.E₁ = C.E₁ := by
  rw [C.E₁_eq]; exact C.act_Q₁ hc C.t_mem_Q₁

theorem conj_Fv_of_Q₁ {c : X} (hc : c ∈ C.D₁.Q₁) (hcv : c * C.v' = C.v' * c) :
    ∀ f ∈ C.Fv, c * f * c⁻¹ = f :=
  C.conj_Fv_of hcv fun _ he => C.conj_eq_of_mem_Q₁ hc he

theorem not_cong_one_v' : ¬ C.Cong 1 C.v' := fun h => C.v'_not_mem_E0 (by
  have := inv_mem (C.cong_def.mp h)
  rwa [one_mul, inv_inv] at this)

theorem cong_mul_conj_one {q d : X} (hd : d ∈ C.D₁.Q₁) (h : C.Cong (q * d * q⁻¹) d) :
    C.Cong (d * (q * d * q⁻¹)) 1 :=
  C.cong_trans (C.cong_mul hd (C.cong_refl d) h) (C.cong_sq hd)

theorem Fv_comm_v' {f : X} (hf : f ∈ C.Fv) : f * C.v' = C.v' * f := by
  have hle : C.Fv ≤ centralizer ({C.v'} : Set X) := by
    refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]; exact (C.comm_v'_E0 he).symm
    · rw [mem_centralizer_singleton_iff]
  exact mem_centralizer_singleton_iff.mp (hle hf)

theorem Fv_comm {f g : X} (hf : f ∈ C.Fv) (hg : g ∈ C.Fv) : f * g = g * f := by
  have hle : C.Fv ≤ centralizer ({f} : Set X) := by
    refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]; exact C.comm_E0_Q₁ he (C.Fv_le_Q₁ hf)
    · rw [mem_centralizer_singleton_iff]; exact (C.Fv_comm_v' hf).symm
  exact (mem_centralizer_singleton_iff.mp (hle hg)).symm

theorem sq_prod_mem {a b : X} (ha : a ∈ C.S₂) (hb : b ∈ C.S₂) (a0 : act a C.E₁ = C.G₁)
    (a1 : act a C.G₁ = C.E₁) (a2 : act a C.G₂ = C.G₃) (a3 : act a C.G₃ = C.G₂)
    (b0 : act b C.E₁ = C.G₂) (b2 : act b C.G₂ = C.E₁) (b1 : act b C.G₁ = C.G₃)
    (b3 : act b C.G₃ = C.G₁) (aF : ∀ f ∈ C.Fv, a * f * a⁻¹ = f)
    (bF : ∀ f ∈ C.Fv, b * f * b⁻¹ = f) (ha2 : a ^ 2 * C.w₁'⁻¹ ∈ C.Fv)
    (hb2 : b ^ 2 * C.D₁.w₂⁻¹ ∈ C.Fv) : (a * b) ^ 2 ∈ C.Fv := by
  have haN := C.S₂_le ha
  have hbN := C.S₂_le hb
  obtain ⟨-, ca1, ca2⟩ := C.cong_q₁ haN a0 a1 a2
  obtain ⟨-, cb1, cb2⟩ := C.cong_q₂ hbN b0 b1 b2
  have hvF : C.v' ∈ C.Fv := mem_sup_right (mem_zpowers _)
  obtain ⟨f₁, hf₁, ha2'⟩ : ∃ f ∈ C.Fv, a ^ 2 = f * C.w₁' := ⟨_, ha2, by group⟩
  obtain ⟨f₂, hf₂, hb2'⟩ : ∃ f ∈ C.Fv, b ^ 2 = f * C.D₁.w₂ := ⟨_, hb2, by group⟩
  obtain ⟨e₁, he₁, he₁w⟩ : ∃ e ∈ C.E₀, b * C.w₁' * b⁻¹ = e * (C.v' * C.w₁') :=
    ⟨_, C.cong_def.mp cb1, by group⟩
  obtain ⟨e₂, he₂, he₂w⟩ : ∃ e ∈ C.E₀, a * C.D₁.w₂ * a⁻¹ = e * (C.v' * C.D₁.w₂) :=
    ⟨_, C.cong_def.mp ca2, by group⟩
  set d := a * b * a⁻¹ * b⁻¹ with hd
  have hdS : d ∈ C.S₂ := mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hdQ : d ∈ C.D₁.Q₁ := by
    refine C.mem_Q₁_of_fix hdS ?_ ?_
    · rw [act_mul, act_mul, act_mul, act_inv_eq b2, act_inv_eq a3, b3, a1]
    · rw [act_mul, act_mul, act_mul, act_inv_eq b0, act_inv_eq a1, b1, a3]
  have hdv : d * C.v' = C.v' * d := by
    have ha' : a⁻¹ * C.v' * a = C.v' := by
      calc a⁻¹ * C.v' * a = a⁻¹ * (a * C.v' * a⁻¹) * a := by rw [aF _ hvF]
        _ = C.v' := by group
    have hb' : b⁻¹ * C.v' * b = C.v' := by
      calc b⁻¹ * C.v' * b = b⁻¹ * (b * C.v' * b⁻¹) * b := by rw [bF _ hvF]
        _ = C.v' := by group
    have : d * C.v' * d⁻¹ = C.v' := by
      rw [hd, show a * b * a⁻¹ * b⁻¹ * C.v' * (a * b * a⁻¹ * b⁻¹)⁻¹ =
        a * (b * (a⁻¹ * (b⁻¹ * C.v' * b) * a) * b⁻¹) * a⁻¹ by group, hb', ha', bF _ hvF,
        aF _ hvF]
    calc d * C.v' = d * C.v' * d⁻¹ * d := by group
      _ = C.v' * d := by rw [this]
  have R1 : C.Cong (d * (b * d * b⁻¹)) C.v' := by
    have h1 : d * (b * d * b⁻¹) = (a * b ^ 2 * a⁻¹) * (b ^ 2)⁻¹ := by rw [hd, pow_two]; group
    have h2 : a * b ^ 2 * a⁻¹ = f₂ * (e₂ * (C.v' * C.D₁.w₂)) := by
      rw [hb2', show a * (f₂ * C.D₁.w₂) * a⁻¹ = (a * f₂ * a⁻¹) * (a * C.D₁.w₂ * a⁻¹) by group,
        aF _ hf₂, he₂w]
    have hev : e₂ * C.v' ∈ C.Fv := mul_mem (mem_sup_left he₂) hvF
    rw [h1, h2, hb2', show f₂ * (e₂ * (C.v' * C.D₁.w₂)) * (f₂ * C.D₁.w₂)⁻¹ =
      f₂ * (e₂ * C.v') * f₂⁻¹ by group, C.Fv_comm hf₂ hev, mul_inv_cancel_right]
    exact C.cong_of_mem_E0 he₂
  have R2 : C.Cong (d⁻¹ * (a * d⁻¹ * a⁻¹)) C.v' := by
    have h1 : d⁻¹ * (a * d⁻¹ * a⁻¹) = (b * a ^ 2 * b⁻¹) * (a ^ 2)⁻¹ := by
      rw [hd, pow_two]; group
    have h2 : b * a ^ 2 * b⁻¹ = f₁ * (e₁ * (C.v' * C.w₁')) := by
      rw [ha2', show b * (f₁ * C.w₁') * b⁻¹ = (b * f₁ * b⁻¹) * (b * C.w₁' * b⁻¹) by group,
        bF _ hf₁, he₁w]
    have hev : e₁ * C.v' ∈ C.Fv := mul_mem (mem_sup_left he₁) hvF
    rw [h1, h2, ha2', show f₁ * (e₁ * (C.v' * C.w₁')) * (f₁ * C.w₁')⁻¹ =
      f₁ * (e₁ * C.v') * f₁⁻¹ by group, C.Fv_comm hf₁ hev, mul_inv_cancel_right]
    exact C.cong_of_mem_E0 he₁
  have bad1 : ¬ C.Cong (b * d * b⁻¹) d := fun h =>
    C.not_cong_one_v' (C.cong_trans (C.cong_symm (C.cong_mul_conj_one hdQ h)) R1)
  have bad2 : ¬ C.Cong (a * d * a⁻¹) d := fun h => C.not_cong_one_v' (C.cong_trans
    (C.cong_symm (C.cong_mul_conj_one (inv_mem hdQ)
      (by rw [show a * d⁻¹ * a⁻¹ = (a * d * a⁻¹)⁻¹ by group]; exact C.cong_inv hdQ h))) R2)
  rcases C.mem_B_cases hdQ hdv with h | h | h | h
  · exact (bad1 (by rw [bF _ h]; exact C.cong_refl _)).elim
  · obtain ⟨f, hf, hfd⟩ : ∃ f ∈ C.Fv, d = f * C.w₁' := ⟨_, h, by group⟩
    refine (bad2 ?_).elim
    rw [hfd, show a * (f * C.w₁') * a⁻¹ = (a * f * a⁻¹) * (a * C.w₁' * a⁻¹) by group, aF _ hf]
    exact C.cong_mul (C.Fv_le_Q₁ hf) (C.cong_refl f) ca1
  · obtain ⟨f, hf, hfd⟩ : ∃ f ∈ C.Fv, d = f * C.D₁.w₂ := ⟨_, h, by group⟩
    refine (bad1 ?_).elim
    rw [hfd, show b * (f * C.D₁.w₂) * b⁻¹ = (b * f * b⁻¹) * (b * C.D₁.w₂ * b⁻¹) by group,
      bF _ hf]
    exact C.cong_mul (C.Fv_le_Q₁ hf) (C.cong_refl f) cb2
  · obtain ⟨f, hf, hfd⟩ : ∃ f ∈ C.Fv, d = f * (C.w₁' * C.D₁.w₂) := ⟨_, h, by group⟩
    set g := f₁ * (e₁ * C.v') with hgdef
    have hg : g ∈ C.Fv := mul_mem hf₁ (mul_mem (mem_sup_left he₁) hvF)
    have hba : b * a ^ 2 * b⁻¹ = g * C.w₁' := by
      rw [ha2', show b * (f₁ * C.w₁') * b⁻¹ = (b * f₁ * b⁻¹) * (b * C.w₁' * b⁻¹) by group,
        bF _ hf₁, he₁w, hgdef]
      group
    have e1 : (a * b) ^ 2 = d * (b * a ^ 2 * b⁻¹) * b ^ 2 := by rw [hd, pow_two, pow_two]; group
    have c1 : (C.w₁' * C.D₁.w₂) * g = g * (C.w₁' * C.D₁.w₂) := by
      rw [mul_assoc, ← C.Fv_comm_w₂ hg, ← mul_assoc, ← C.Fv_comm_w₁' hg, mul_assoc]
    have c2 : (C.w₁' * C.D₁.w₂ * C.w₁') * f₂ = f₂ * (C.w₁' * C.D₁.w₂ * C.w₁') := by
      rw [mul_assoc, mul_assoc, ← C.Fv_comm_w₁' hf₂, ← mul_assoc C.D₁.w₂, ← C.Fv_comm_w₂ hf₂,
        mul_assoc, ← mul_assoc C.w₁', ← C.Fv_comm_w₁' hf₂]
      group
    rw [e1, hfd, hba, hb2']
    have e2 : f * (C.w₁' * C.D₁.w₂) * (g * C.w₁') * (f₂ * C.D₁.w₂) =
        (f * g * f₂) * (C.w₁' * C.D₁.w₂) ^ 2 := by
      calc f * (C.w₁' * C.D₁.w₂) * (g * C.w₁') * (f₂ * C.D₁.w₂) =
            f * ((C.w₁' * C.D₁.w₂) * g) * C.w₁' * f₂ * C.D₁.w₂ := by group
        _ = f * (g * (C.w₁' * C.D₁.w₂)) * C.w₁' * f₂ * C.D₁.w₂ := by rw [c1]
        _ = f * g * ((C.w₁' * C.D₁.w₂ * C.w₁') * f₂) * C.D₁.w₂ := by group
        _ = f * g * (f₂ * (C.w₁' * C.D₁.w₂ * C.w₁')) * C.D₁.w₂ := by rw [c2]
        _ = (f * g * f₂) * (C.w₁' * C.D₁.w₂) ^ 2 := by rw [pow_two]; group
    rw [e2]
    exact mul_mem (mul_mem (mul_mem hf hg) hf₂)
      (mem_sup_left (C.sq_mem_E0 (mul_mem C.w₁'_mem_Q₁ C.w₂_mem_Q₁)))

theorem conj_Fv_mul {b c : X} (bF : ∀ f ∈ C.Fv, b * f * b⁻¹ = f) (hc : c ∈ C.D₁.Q₁)
    (hcv : c * C.v' = C.v' * c) : ∀ f ∈ C.Fv, (b * c) * f * (b * c)⁻¹ = f := fun f hf => by
  rw [show b * c * f * (b * c)⁻¹ = b * (c * f * c⁻¹) * b⁻¹ by group,
    C.conj_Fv_of_Q₁ hc hcv f hf, bF f hf]

theorem good_q₂_of {x : X} (hx : x ∈ normalizer (C.D₁.Q₁ : Set X)) (x0 : act x C.E₁ = C.G₁)
    (x1 : act x C.G₁ = C.E₁) (x3 : act x C.G₃ = C.G₂) (xF : ∀ f ∈ C.Fv, x * f * x⁻¹ = f)
    (x2 : x ^ 2 ∈ C.Fv) : ∃ q ∈ C.S₂, act q C.E₁ = C.G₂ ∧ act q C.G₂ = C.E₁ ∧
      act q C.G₁ = C.G₃ ∧ act q C.G₃ = C.G₁ ∧ (∀ f ∈ C.Fv, q * f * q⁻¹ = f) ∧
      q ^ 2 ∈ C.Fv := by
  obtain ⟨b, hb, b0, b2, b1, b3, bv⟩ := C.exists_q₂'
  obtain ⟨δ, hδ, d0, d1, d2, d3⟩ := C.exists_δ
  have hbN := C.S₂_le hb
  have bF := C.conj_Fv_of bv (C.conj_E0_q₂ hbN b0 b1 b2)
  have hn : δ * x * δ⁻¹ ∈ normalizer (C.D₁.Q₁ : Set X) := mul_mem (mul_mem hδ hx) (inv_mem hδ)
  have n0 : act (δ * x * δ⁻¹) C.E₁ = act b C.E₁ := by
    rw [act_mul, act_mul, act_inv_eq d0, x0, d1, b0]
  have n1 : act (δ * x * δ⁻¹) C.G₁ = act b C.G₁ := by
    rw [act_mul, act_mul, act_inv_eq d3, x3, d2, b1]
  have n2 : act (δ * x * δ⁻¹) C.G₂ = act b C.G₂ := by
    rw [act_mul, act_mul, act_inv_eq d1, x1, d0, b2]
  obtain ⟨c, hc, hcv, hbc⟩ := C.transfer hn (C.conj_conj_Fv hδ xF) (C.sq_conj_mem_Fv hδ x2) hb
    bF (C.sq_cases_q₂ hb b0 b1 b2).1 n0 n1 n2
  refine ⟨b * c, mul_mem hb (C.S₁_le_S₂ (C.Q₁_le_S₁ hc)), ?_, ?_, ?_, ?_,
    C.conj_Fv_mul bF hc hcv, hbc⟩
  · rw [act_mul, C.act_Q₁_E₁ hc, b0]
  · rw [act_mul, C.act_Q₁ hc C.r₂_mem, b2]
  · rw [act_mul, C.act_Q₁ hc C.r₁_mem, b1]
  · rw [act_mul, C.act_Q₁ hc C.r₃_mem, b3]

theorem good_q₁_core {x ε : X} (hx : x ∈ normalizer (C.D₁.Q₁ : Set X))
    (hε : ε ∈ normalizer (C.D₁.Q₁ : Set X)) (xF : ∀ f ∈ C.Fv, x * f * x⁻¹ = f)
    (x2 : x ^ 2 ∈ C.Fv) (e0 : act (ε * x * ε⁻¹) C.E₁ = C.G₁)
    (e1 : act (ε * x * ε⁻¹) C.G₁ = C.E₁) (e2 : act (ε * x * ε⁻¹) C.G₂ = C.G₃) :
    ∃ q ∈ C.S₂, act q C.E₁ = C.G₁ ∧ act q C.G₁ = C.E₁ ∧ act q C.G₂ = C.G₃ ∧
      act q C.G₃ = C.G₂ ∧ (∀ f ∈ C.Fv, q * f * q⁻¹ = f) ∧ q ^ 2 ∈ C.Fv := by
  obtain ⟨a, ha, a0, a1, a2, a3, av⟩ := C.exists_q₁'
  have haN := C.S₂_le ha
  have aF := C.conj_Fv_of av (C.conj_E0_q₁ haN a0 a1 a2)
  have hn : ε * x * ε⁻¹ ∈ normalizer (C.D₁.Q₁ : Set X) := mul_mem (mul_mem hε hx) (inv_mem hε)
  obtain ⟨c, hc, hcv, hac⟩ := C.transfer hn (C.conj_conj_Fv hε xF) (C.sq_conj_mem_Fv hε x2) ha
    aF (C.sq_cases_q₁ ha a0 a1 a2 a3).1 (e0.trans a0.symm) (e1.trans a1.symm)
    (e2.trans a2.symm)
  refine ⟨a * c, mul_mem ha (C.S₁_le_S₂ (C.Q₁_le_S₁ hc)), ?_, ?_, ?_, ?_,
    C.conj_Fv_mul aF hc hcv, hac⟩
  · rw [act_mul, C.act_Q₁_E₁ hc, a0]
  · rw [act_mul, C.act_Q₁ hc C.r₁_mem, a1]
  · rw [act_mul, C.act_Q₁ hc C.r₂_mem, a2]
  · rw [act_mul, C.act_Q₁ hc C.r₃_mem, a3]

theorem exists_good : ∃ q₁ ∈ C.S₂, ∃ q₂ ∈ C.S₂,
    (act q₁ C.E₁ = C.G₁ ∧ act q₁ C.G₁ = C.E₁ ∧ act q₁ C.G₂ = C.G₃ ∧ act q₁ C.G₃ = C.G₂ ∧
      (∀ f ∈ C.Fv, q₁ * f * q₁⁻¹ = f) ∧ q₁ ^ 2 ∈ C.Fv) ∧
    (act q₂ C.E₁ = C.G₂ ∧ act q₂ C.G₂ = C.E₁ ∧ act q₂ C.G₁ = C.G₃ ∧ act q₂ C.G₃ = C.G₁ ∧
      (∀ f ∈ C.Fv, q₂ * f * q₂⁻¹ = f) ∧ q₂ ^ 2 ∈ C.Fv) := by
  obtain ⟨a, ha, a0, a1, a2, a3, av⟩ := C.exists_q₁'
  obtain ⟨b, hb, b0, b2, b1, b3, bv⟩ := C.exists_q₂'
  obtain ⟨δ, hδ, d0, d1, d2, d3⟩ := C.exists_δ
  have haN := C.S₂_le ha
  have hbN := C.S₂_le hb
  have aF := C.conj_Fv_of av (C.conj_E0_q₁ haN a0 a1 a2)
  have bF := C.conj_Fv_of bv (C.conj_E0_q₂ hbN b0 b1 b2)
  have pair : ∀ q₁ ∈ C.S₂, act q₁ C.E₁ = C.G₁ → act q₁ C.G₁ = C.E₁ → act q₁ C.G₂ = C.G₃ →
      act q₁ C.G₃ = C.G₂ → (∀ f ∈ C.Fv, q₁ * f * q₁⁻¹ = f) → q₁ ^ 2 ∈ C.Fv →
      ∃ q₁ ∈ C.S₂, ∃ q₂ ∈ C.S₂,
        (act q₁ C.E₁ = C.G₁ ∧ act q₁ C.G₁ = C.E₁ ∧ act q₁ C.G₂ = C.G₃ ∧
          act q₁ C.G₃ = C.G₂ ∧ (∀ f ∈ C.Fv, q₁ * f * q₁⁻¹ = f) ∧ q₁ ^ 2 ∈ C.Fv) ∧
        (act q₂ C.E₁ = C.G₂ ∧ act q₂ C.G₂ = C.E₁ ∧ act q₂ C.G₁ = C.G₃ ∧
          act q₂ C.G₃ = C.G₁ ∧ (∀ f ∈ C.Fv, q₂ * f * q₂⁻¹ = f) ∧ q₂ ^ 2 ∈ C.Fv) := by
    intro q₁ hq₁ x0 x1 x2 x3 xF xsq
    obtain ⟨q₂, hq₂, h⟩ := C.good_q₂_of (C.S₂_le hq₁) x0 x1 x3 xF xsq
    exact ⟨q₁, hq₁, q₂, hq₂, ⟨x0, x1, x2, x3, xF, xsq⟩, h⟩
  rcases (C.sq_cases_q₁ ha a0 a1 a2 a3).2.2 with ha2 | ha2
  · exact pair a ha a0 a1 a2 a3 aF ha2
  rcases (C.sq_cases_q₂ hb b0 b1 b2).2.2 with hb2 | hb2
  ·
    obtain ⟨q₁, hq₁, x0, x1, x2, x3, xF, xsq⟩ := C.good_q₁_core hbN (inv_mem hδ) bF hb2
      (by rw [act_mul, act_mul, inv_inv, d0, b0, act_inv_eq d1])
      (by rw [act_mul, act_mul, inv_inv, d1, b2, act_inv_eq d0])
      (by rw [act_mul, act_mul, inv_inv, d2, b3, act_inv_eq d3])
    exact pair q₁ hq₁ x0 x1 x2 x3 xF xsq
  ·
    have hp2 := C.sq_prod_mem ha hb a0 a1 a2 a3 b0 b2 b1 b3 aF bF ha2 hb2
    have pF : ∀ f ∈ C.Fv, (a * b) * f * (a * b)⁻¹ = f := fun f hf => by
      rw [show a * b * f * (a * b)⁻¹ = a * (b * f * b⁻¹) * a⁻¹ by group, bF f hf, aF f hf]
    obtain ⟨q₁, hq₁, x0, x1, x2, x3, xF, xsq⟩ := C.good_q₁_core (mul_mem haN hbN) hδ pF hp2
      (by rw [act_mul, act_mul, act_mul, act_inv_eq d0, b0, a2, d3])
      (by rw [act_mul, act_mul, act_mul, act_inv_eq d3, b3, a1, d0])
      (by rw [act_mul, act_mul, act_mul, act_inv_eq d1, b1, a3, d2])
    exact pair q₁ hq₁ x0 x1 x2 x3 xF xsq

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
