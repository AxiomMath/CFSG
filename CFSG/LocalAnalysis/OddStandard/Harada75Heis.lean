module

public import CFSG.LocalAnalysis.OddStandard.Harada75Isom

public section

namespace CFSG.OddStandard.Harada75

@[expose] def beta (w w' : W₀) : ZMod 2 := w'.1 * w.2.2.1 + w'.2.1 * w.2.2.2

@[ext] structure Heis where
  w : W₀
  k : ZMod 2
  deriving DecidableEq

namespace Heis

instance : Mul Heis := ⟨fun a b => ⟨a.w + b.w, a.k + b.k + beta a.w b.w⟩⟩
instance : One Heis := ⟨⟨0, 0⟩⟩
instance : Inv Heis := ⟨fun a => ⟨a.w, a.k + beta a.w a.w⟩⟩

@[simp] theorem mul_w (a b : Heis) : (a * b).w = a.w + b.w := rfl
@[simp] theorem mul_k (a b : Heis) : (a * b).k = a.k + b.k + beta a.w b.w := rfl
@[simp] theorem one_w : (1 : Heis).w = 0 := rfl
@[simp] theorem one_k : (1 : Heis).k = 0 := rfl
@[simp] theorem inv_w (a : Heis) : (a⁻¹).w = a.w := rfl
@[simp] theorem inv_k (a : Heis) : (a⁻¹).k = a.k + beta a.w a.w := rfl

theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

instance : Group Heis where
  mul_assoc a b c := by
    refine Heis.ext ?_ ?_
    · simp only [mul_w, add_assoc]
    · simp only [mul_k, mul_w, beta, Prod.fst_add, Prod.snd_add]; ring
  one_mul a := by
    refine Heis.ext ?_ ?_
    · simp only [mul_w, one_w, zero_add]
    · simp [beta]
  mul_one a := by
    refine Heis.ext ?_ ?_
    · simp only [mul_w, one_w, add_zero]
    · simp [beta]
  inv_mul_cancel a := by
    refine Heis.ext ?_ ?_
    · simp only [mul_w, inv_w, one_w]
      exact CharTwo.add_self_eq_zero _
    · simp only [mul_k, inv_k, inv_w, one_k, beta]; ring_nf; simp [two_eq_zero]

instance : Fintype Heis :=
  Fintype.ofEquiv (W₀ × ZMod 2)
    ⟨fun p => ⟨p.1, p.2⟩, fun h => (h.w, h.k), fun _ => rfl, fun _ => rfl⟩

theorem card_heis : Nat.card Heis = 32 := by
  rw [Nat.card_eq_fintype_card]; decide

@[expose] def z₀ : Heis := ⟨0, 1⟩

@[expose] def Zc (k : ZMod 2) : Heis := ⟨0, k⟩

theorem comm_formula : ∀ a b : Heis, a * b * a⁻¹ * b⁻¹ = Zc (b₀ a.w b.w) := by decide

theorem sq_formula : ∀ a : Heis, a * a = Zc (q₀ a.w) := by decide

theorem Zc_central : ∀ (a : Heis) (k : ZMod 2), a * Zc k = Zc k * a := by decide

theorem Zc_add : ∀ k k' : ZMod 2, Zc k * Zc k' = Zc (k + k') := by decide

theorem eq_mul_Zc : ∀ h : Heis, h = ⟨h.w, 0⟩ * Zc h.k := by decide

theorem mk_zero_mul : ∀ (a b : W₀), (⟨a, 0⟩ : Heis) * ⟨b, 0⟩ = ⟨a + b, beta a b⟩ := by decide

theorem conj_formula : ∀ (v : W₀) (h : Heis),
    (⟨v, 0⟩ : Heis) * h * (⟨v, 0⟩ : Heis)⁻¹ = ⟨h.w, h.k + b₀ v h.w⟩ := by decide

theorem Zc_zero : Zc 0 = 1 := rfl

theorem Zc_one : Zc 1 = z₀ := rfl

@[expose] def E₀ : Subgroup Heis where
  carrier := {h | h.w.2.2.1 = 0 ∧ h.w.2.2.2 = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · show a.w.2.2.1 + b.w.2.2.1 = 0
      rw [ha.1, hb.1]; rfl
    · show a.w.2.2.2 + b.w.2.2.2 = 0
      rw [ha.2, hb.2]; rfl
  inv_mem' := by
    intro a ha
    exact ha

theorem mem_E₀ (h : Heis) : h ∈ E₀ ↔ h.w.2.2.1 = 0 ∧ h.w.2.2.2 = 0 := Iff.rfl

instance (h : Heis) : Decidable (h ∈ E₀) :=
  decidable_of_iff (h.w.2.2.1 = 0 ∧ h.w.2.2.2 = 0) (mem_E₀ h).symm

theorem card_E₀ : Nat.card E₀ = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem Zc_mem_E₀ (k : ZMod 2) : Zc k ∈ E₀ := ⟨rfl, rfl⟩


@[expose] def lin (φ : Heis →* Heis) (w : W₀) : W₀ := (φ ⟨w, 0⟩).w

section lin

variable (φ : Heis →* Heis) (hz : φ z₀ = z₀)
include hz

theorem phi_Zc (k : ZMod 2) : φ (Zc k) = Zc k := by
  rcases zmod2_cases k with rfl | rfl
  · rw [Zc_zero, map_one]
  · rw [Zc_one, hz]

theorem phi_eq (h : Heis) : φ h = ⟨lin φ h.w, (φ ⟨h.w, 0⟩).k + h.k⟩ := by
  conv_lhs => rw [eq_mul_Zc h]
  rw [map_mul, phi_Zc φ hz]
  refine Heis.ext ?_ ?_
  · simp [lin, Zc]
  · simp [Zc, beta]

theorem lin_add (a b : W₀) : lin φ (a + b) = lin φ a + lin φ b := by
  have h1 : φ (⟨a, 0⟩ * ⟨b, 0⟩) = φ ⟨a, 0⟩ * φ ⟨b, 0⟩ := map_mul φ _ _
  rw [mk_zero_mul, phi_eq φ hz] at h1
  have := congrArg Heis.w h1
  simp only [mul_w] at this
  rw [this]
  rfl

theorem lin_q (w : W₀) : q₀ (lin φ w) = q₀ w := by
  have h1 : φ (⟨w, 0⟩ * ⟨w, 0⟩) = φ ⟨w, 0⟩ * φ ⟨w, 0⟩ := map_mul φ _ _
  rw [sq_formula, sq_formula, phi_Zc φ hz] at h1
  have := congrArg Heis.k h1
  simpa [Zc, lin] using this.symm

theorem isIsom_lin (hE : ∀ h : Heis, φ h ∈ E₀ ↔ h ∈ E₀) : IsIsom (lin φ) := by
  refine ⟨lin_add φ hz, lin_q φ hz, fun w => ?_⟩
  have := hE ⟨w, 0⟩
  rw [phi_eq φ hz] at this
  exact this

end lin

theorem lin_comp (φ ψ : Heis →* Heis) (hφ : φ z₀ = z₀) (w : W₀) :
    lin (φ.comp ψ) w = lin φ (lin ψ w) := by
  have := phi_eq φ hφ (ψ ⟨w, 0⟩)
  have h2 := congrArg Heis.w this
  simpa [lin] using h2

theorem lin_id (w : W₀) : lin (MonoidHom.id Heis) w = w := rfl

@[expose] def linPerm (φ φ' : Heis →* Heis) (h1 : φ.comp φ' = MonoidHom.id Heis)
    (h2 : φ'.comp φ = MonoidHom.id Heis) (hz : φ z₀ = z₀) (hz' : φ' z₀ = z₀) :
    Equiv.Perm W₀ where
  toFun := lin φ
  invFun := lin φ'
  left_inv w := by
    rw [← lin_comp φ' φ hz', h2]; rfl
  right_inv w := by
    rw [← lin_comp φ φ' hz, h1]; rfl

theorem linPerm_apply (φ φ' : Heis →* Heis) (h1 : φ.comp φ' = MonoidHom.id Heis)
    (h2 : φ'.comp φ = MonoidHom.id Heis) (hz : φ z₀ = z₀) (hz' : φ' z₀ = z₀) (w : W₀) :
    linPerm φ φ' h1 h2 hz hz' w = lin φ w := rfl

theorem exists_conj_of_lin_eq_id (φ : Heis →* Heis) (hz : φ z₀ = z₀) (h : ∀ w, lin φ w = w) :
    ∃ h₀ : Heis, ∀ x : Heis, φ x = h₀ * x * h₀⁻¹ := by
  let μ : W₀ → ZMod 2 := fun w => (φ ⟨w, 0⟩).k
  have hφ : ∀ x : Heis, φ x = ⟨x.w, μ x.w + x.k⟩ := by
    intro x
    rw [phi_eq φ hz x]
    simp only [μ, h]
  have hμadd : ∀ a b : W₀, μ (a + b) = μ a + μ b := by
    intro a b
    have h1 : φ (⟨a, 0⟩ * ⟨b, 0⟩) = φ ⟨a, 0⟩ * φ ⟨b, 0⟩ := map_mul φ _ _
    rw [mk_zero_mul, hφ, hφ, hφ] at h1
    have := congrArg Heis.k h1
    simp only [mul_k] at this
    simp only [beta] at this
    have h3 : μ (a + b) + (b.1 * a.2.2.1 + b.2.1 * a.2.2.2) =
        μ a + μ b + (b.1 * a.2.2.1 + b.2.1 * a.2.2.2) := by
      simpa [beta, add_assoc] using this
    exact add_right_cancel h3
  have hlin : ∀ w : W₀, μ w = w.1 * μ e1 + w.2.1 * μ e2 + w.2.2.1 * μ f1 + w.2.2.2 * μ f2 := by
    intro w
    have hw : w = (w.1, 0, 0, 0) + (0, w.2.1, 0, 0) + (0, 0, w.2.2.1, 0) + (0, 0, 0, w.2.2.2) := by
      ext <;> simp
    have hm0 : μ 0 = 0 := by
      have := hμadd 0 0
      simpa using this
    have h1 : ∀ a : ZMod 2, μ (a, 0, 0, 0) = a * μ e1 := by
      intro a
      rcases zmod2_cases a with rfl | rfl
      · rw [zero_mul]; exact hm0
      · simp [e1]
    have h2 : ∀ a : ZMod 2, μ (0, a, 0, 0) = a * μ e2 := by
      intro a
      rcases zmod2_cases a with rfl | rfl
      · rw [zero_mul]; exact hm0
      · simp [e2]
    have h3 : ∀ a : ZMod 2, μ (0, 0, a, 0) = a * μ f1 := by
      intro a
      rcases zmod2_cases a with rfl | rfl
      · rw [zero_mul]; exact hm0
      · simp [f1]
    have h4 : ∀ a : ZMod 2, μ (0, 0, 0, a) = a * μ f2 := by
      intro a
      rcases zmod2_cases a with rfl | rfl
      · rw [zero_mul]; exact hm0
      · simp [f2]
    conv_lhs => rw [hw]
    rw [hμadd, hμadd, hμadd, h1, h2, h3, h4]
  refine ⟨⟨(μ f1, μ f2, μ e1, μ e2), 0⟩, fun x => ?_⟩
  rw [conj_formula, hφ]
  refine Heis.ext rfl ?_
  show μ x.w + x.k = x.k + b₀ (μ f1, μ f2, μ e1, μ e2) x.w
  rw [hlin x.w]
  simp only [b₀]
  ring

end Heis

end CFSG.OddStandard.Harada75
