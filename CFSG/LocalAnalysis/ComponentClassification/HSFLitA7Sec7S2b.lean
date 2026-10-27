module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2a

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

def Cong (x y : X) : Prop := x * y⁻¹ ∈ C.E₀

theorem cong_def {x y : X} : C.Cong x y ↔ x * y⁻¹ ∈ C.E₀ := by unfold Cong; rfl

theorem cong_refl (x : X) : C.Cong x x := C.cong_def.mpr (by rw [mul_inv_cancel]; exact one_mem _)

theorem cong_symm {x y : X} (h : C.Cong x y) : C.Cong y x := C.cong_def.mpr (by
  have := inv_mem (C.cong_def.mp h)
  rwa [mul_inv_rev, inv_inv] at this)

theorem cong_trans {x y w : X} (h1 : C.Cong x y) (h2 : C.Cong y w) : C.Cong x w :=
  C.cong_def.mpr (by
    have := mul_mem (C.cong_def.mp h1) (C.cong_def.mp h2)
    rwa [show x * y⁻¹ * (y * w⁻¹) = x * w⁻¹ by group] at this)

theorem cong_mul {a a' b b' : X} (ha : a ∈ C.D₁.Q₁) (h1 : C.Cong a a') (h2 : C.Cong b b') :
    C.Cong (a * b) (a' * b') := C.cong_def.mpr (by
  have h := C.cong_def.mp h2
  rw [show a * b * (a' * b')⁻¹ = (a * (b * b'⁻¹) * a⁻¹) * (a * a'⁻¹) by group,
    C.conj_eq_of_mem_Q₁ ha h]
  exact mul_mem h (C.cong_def.mp h1))

theorem cong_inv {a b : X} (hb : b ∈ C.D₁.Q₁) (h : C.Cong a b) : C.Cong a⁻¹ b⁻¹ :=
  C.cong_def.mpr (by
    have h1 := C.cong_def.mp h
    rw [inv_inv, show a⁻¹ * b = b⁻¹ * (b * a⁻¹) * b by group]
    have h2 := inv_mem h1
    rw [mul_inv_rev, inv_inv] at h2
    have := C.conj_eq_of_mem_Q₁ (inv_mem hb) h2
    rw [inv_inv] at this
    rw [this]
    exact h2)

theorem cong_comm {a b : X} (ha : a ∈ C.D₁.Q₁) (hb : b ∈ C.D₁.Q₁) : C.Cong (a * b) (b * a) :=
  C.cong_def.mpr (by
    rw [show a * b * (b * a)⁻¹ = a * b * a⁻¹ * b⁻¹ by group]
    exact C.comm_mem_E0 ha hb)

theorem cong_of_mem_E0 {e x : X} (he : e ∈ C.E₀) : C.Cong (e * x) x :=
  C.cong_def.mpr (by rw [mul_inv_cancel_right]; exact he)

theorem sq_mem_E0 {x : X} (hx : x ∈ C.D₁.Q₁) : x ^ 2 ∈ C.E₀ := by
  let H : Subgroup X :=
    { carrier := {x | x ∈ C.D₁.Q₁ ∧ x ^ 2 ∈ C.E₀}
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        obtain ⟨c, hcdef⟩ : ∃ c, c = b * a * b⁻¹ * a⁻¹ := ⟨_, rfl⟩
        have hc : c ∈ C.E₀ := hcdef ▸ C.comm_mem_E0 hb ha
        have hba : b * a = c * a * b := by rw [hcdef]; group
        have key : (a * b) ^ 2 = c * a ^ 2 * b ^ 2 := by
          calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
            _ = (a * c) * a * (b * b) := by rw [hba]; group
            _ = (c * a) * a * (b * b) := by rw [← C.comm_E0_Q₁ hc ha]
            _ = c * a ^ 2 * b ^ 2 := by rw [pow_two, pow_two]; group
        rw [key]
        exact mul_mem (mul_mem hc ha2) hb2
      one_mem' := ⟨one_mem _, by rw [one_pow]; exact one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        exact ⟨inv_mem ha, by rw [inv_pow]; exact inv_mem ha2⟩ }
  have hle : C.D₁.Q₁ ≤ H := by
    rw [C.Q₁_eq]
    have hE : C.E₀ ≤ H := fun e he => ⟨C.E0_le_Q₁ he,
      by rw [(C.isRefl_y.elemAbelianTwo_E0 C.isK_k).sq_eq_one e he]; exact one_mem _⟩
    have hg : ∀ {g : X}, g ∈ C.D₁.Q₁ → g ^ 2 ∈ C.E₀ → zpowers g ≤ H :=
      fun hg hg2 => zpowers_le.mpr ⟨hg, hg2⟩
    refine sup_le (sup_le (sup_le ?_ (hg C.v'_mem_Q₁ C.v'_sq_mem_E0))
      (hg C.w₁'_mem_Q₁ C.w₁'_sq_mem_E0)) (hg C.w₂_mem_Q₁ C.w₂_sq_mem)
    rw [C.E₁_eq]
    exact sup_le hE (hg C.t_mem_Q₁ C.t_sq_mem)
  exact (hle hx).2

theorem cong_sq {x : X} (hx : x ∈ C.D₁.Q₁) : C.Cong (x * x) 1 :=
  C.cong_def.mpr (by rw [inv_one, mul_one, ← pow_two]; exact C.sq_mem_E0 hx)

theorem cong_self_inv {x : X} (hx : x ∈ C.D₁.Q₁) : C.Cong x⁻¹ x :=
  C.cong_def.mpr (by rw [← mul_inv_rev, ← pow_two]; exact inv_mem (C.sq_mem_E0 hx))

theorem cong_of_act {q a b : X} (hq : q ∈ normalizer (C.D₁.Q₁ : Set X)) (ha0 : a ∉ C.E₀)
    (hb : b ∈ C.D₁.Q₁) (hb2 : b ^ 2 ∈ C.E₀)
    (h : act q (C.E₀ ⊔ zpowers a) = C.E₀ ⊔ zpowers b) : C.Cong (q * a * q⁻¹) b := by
  have hmem : q * a * q⁻¹ ∈ C.E₀ ⊔ zpowers b := by
    rw [← h]; exact ⟨a, mem_sup_right (mem_zpowers a), rfl⟩
  have hnot : q * a * q⁻¹ ∉ C.E₀ := fun h' => ha0 (by
    have := C.conj_E0_of_mem_normalizer (inv_mem hq) h'
    rwa [show q⁻¹ * (q * a * q⁻¹) * q⁻¹⁻¹ = a by group] at this)
  rcases mem_or_of_mem_sup_zpowers (C.normalizes_E0_of_mem_Q₁ hb) hb2 hmem with h' | h'
  · exact absurd h' hnot
  · exact C.cong_def.mpr h'

theorem t_not_mem_E0 : S.t ∉ C.E₀ := C.isRefl_y.t_not_mem_E0 C.isK_k

theorem act_Fv {q : X} (hq : q ∈ normalizer (C.D₁.Q₁ : Set X)) : act q C.Fv = C.Fv := by
  have h1 : act q C.Fv = C.E₀ ⊔ zpowers (q * C.v' * q⁻¹) := C.map_sup_zpowers hq C.v'
  have hx := C.conj_mem_Q₁ hq C.v'_mem_Q₁
  have hx2 := conj_sq_one (n := q) C.v'_sq
  have hx0 : q * C.v' * q⁻¹ ∉ C.E₀ := fun h' => C.v'_not_mem_E0 (by
    have := C.conj_E0_of_mem_normalizer (inv_mem hq) h'
    rwa [show q⁻¹ * (q * C.v' * q⁻¹) * q⁻¹⁻¹ = C.v' by group] at this)
  have hback : ∀ A ∈ C.Ω, act q C.Fv = A → False := by
    intro A hA hFA
    have hF : C.Fv = act q⁻¹ A := by
      rw [← hFA, ← act_mul, inv_mul_cancel]; ext x; simp
    obtain ⟨n, hn, hnA⟩ := C.conj₁_def.mp (C.conj₁_iff.mpr (C.act_mem_Ω (inv_mem hq) hA))
    exact C.map_ne_Fv n (hnA.trans hF.symm)
  rcases C.sup_cases hx hx2 hx0 with h | h | h | h | h
  · exact (hback C.E₁ C.mem_Ω_E₁ (h1.trans (h.trans C.E₁_eq.symm))).elim
  · exact h1.trans h
  · exact (hback C.G₁ C.mem_Ω_G₁ (h1.trans h)).elim
  · exact (hback C.G₂ C.mem_Ω_G₂ (h1.trans h)).elim
  · exact (hback C.G₃ C.mem_Ω_G₃ (h1.trans h)).elim

theorem cong_v' {q : X} (hq : q ∈ normalizer (C.D₁.Q₁ : Set X)) :
    C.Cong (q * C.v' * q⁻¹) C.v' :=
  C.cong_of_act hq C.v'_not_mem_E0 C.v'_mem_Q₁ C.v'_sq_mem_E0 (C.act_Fv hq)

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
