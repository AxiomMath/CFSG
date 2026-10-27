module

public import CFSG.ClassicalInvolution.Generic.Frame


public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO

open CFSG.ClassicalInvolution.Generic

section M

variable {Y : Type*} [Group Y]

@[expose] def InM (C O Q : Subgroup Y) (m : Y) : Prop :=
  m ∈ C ∧ ∀ l ∈ Q, m * l * m⁻¹ * l⁻¹ ∈ O

variable {C O Q : Subgroup Y}

theorem InM.one : InM C O Q 1 := ⟨C.one_mem, fun l _ => by simpa using O.one_mem⟩

theorem InM.mul (hO : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O) {m₁ m₂ : Y} (h₁ : InM C O Q m₁)
    (h₂ : InM C O Q m₂) : InM C O Q (m₁ * m₂) := by
  refine ⟨C.mul_mem h₁.1 h₂.1, fun l hl => ?_⟩
  have e : m₁ * m₂ * l * (m₁ * m₂)⁻¹ * l⁻¹ =
      m₁ * (m₂ * l * m₂⁻¹ * l⁻¹) * m₁⁻¹ * (m₁ * l * m₁⁻¹ * l⁻¹) := by group
  rw [e]
  exact O.mul_mem (hO m₁ h₁.1 _ (h₂.2 l hl)) (h₁.2 l hl)

theorem InM.inv (hO : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O) (hQC : Q ≤ C) {m : Y} (h : InM C O Q m) :
    InM C O Q m⁻¹ := by
  refine ⟨C.inv_mem h.1, fun l hl => ?_⟩
  have ho : m * l⁻¹ * m⁻¹ * l⁻¹⁻¹ ∈ O := h.2 l⁻¹ (Q.inv_mem hl)
  have e : m⁻¹ * l * m⁻¹⁻¹ * l⁻¹ = m⁻¹ * (l * (m * l⁻¹ * m⁻¹ * l⁻¹⁻¹) * l⁻¹) * m⁻¹⁻¹ := by group
  rw [e]
  exact hO _ (C.inv_mem h.1) _ (hO l (hQC hl) _ ho)

theorem InM.pow (hO : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O) {m : Y} (h : InM C O Q m) (k : ℕ) :
    InM C O Q (m ^ k) := by
  induction k with
  | zero => simpa using InM.one
  | succ k ih => rw [pow_succ]; exact InM.mul hO ih h

theorem InM.of_mem (hOC : O ≤ C) (hO : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O) (hQC : Q ≤ C) {o : Y}
    (ho : o ∈ O) : InM C O Q o := by
  refine ⟨hOC ho, fun l hl => ?_⟩
  have e : o * l * o⁻¹ * l⁻¹ = o * (l * o⁻¹ * l⁻¹) := by group
  rw [e]
  exact O.mul_mem ho (hO l (hQC hl) _ (O.inv_mem ho))

theorem InM.conj (hO : ∀ c ∈ C, ∀ o ∈ O, c * o * c⁻¹ ∈ O) (hQ : ∀ c ∈ C, ∀ l ∈ Q, c * l * c⁻¹ ∈ Q)
    {c m : Y} (hc : c ∈ C) (h : InM C O Q m) : InM C O Q (c * m * c⁻¹) := by
  refine ⟨C.mul_mem (C.mul_mem hc h.1) (C.inv_mem hc), fun l hl => ?_⟩
  have hl' : c⁻¹ * l * c⁻¹⁻¹ ∈ Q := hQ c⁻¹ (C.inv_mem hc) l hl
  have ho := hO c hc _ (h.2 _ hl')
  have e : c * m * c⁻¹ * l * (c * m * c⁻¹)⁻¹ * l⁻¹ =
      c * (m * (c⁻¹ * l * c⁻¹⁻¹) * m⁻¹ * (c⁻¹ * l * c⁻¹⁻¹)⁻¹) * c⁻¹ := by group
  rw [e]
  exact ho

end M

theorem not_swap_of_odd {Y : Type*} [Group Y] {A B : Subgroup Y} (hAB : A ≠ B) {y : Y}
    (h1 : conjSub y A = B) (h2 : conjSub y B = A) {N : ℕ} (hN : Odd N) (hyN : y ^ N = 1) : False := by
  have hB2 : conjSub (y * y) B = B := by rw [conjSub_mul, h2, h1]
  have key : ∀ k : ℕ, conjSub (y ^ (2 * k)) B = B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hy2 : y ^ (2 * (k + 1)) = y ^ (2 * k) * (y * y) := by
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_two]
      rw [hy2, conjSub_mul, hB2, ih]
  obtain ⟨k, rfl⟩ := hN
  have h3 : conjSub (y ^ (2 * k + 1)) A = B := by
    rw [pow_succ, conjSub_mul, h1]
    exact key k
  rw [hyN, conjSub_one] at h3
  exact hAB h3

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsO
