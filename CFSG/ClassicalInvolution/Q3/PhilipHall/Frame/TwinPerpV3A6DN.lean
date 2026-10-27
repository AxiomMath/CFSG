module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6DN

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

theorem sq_eq_one_of_mem_closure {X : Type*} [Group X] {s : Set X}
    (hcomm : ∀ x ∈ s, ∀ y ∈ s, Commute x y) (hsq : ∀ x ∈ s, x * x = 1) :
    ∀ d ∈ Subgroup.closure s, d * d = 1 := by
  have h1 : ∀ d ∈ Subgroup.closure s, ∀ y ∈ s, Commute d y := by
    intro d hd y hy
    induction hd using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx y hy
    | one => exact Commute.one_left y
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  have h2 : ∀ d ∈ Subgroup.closure s, ∀ e ∈ Subgroup.closure s, Commute d e := by
    intro d hd e he
    induction he using Subgroup.closure_induction with
    | mem x hx => exact h1 d hd x hx
    | one => exact Commute.one_right d
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem x hx => exact hsq x hx
  | one => exact mul_one 1
  | mul a b ha' hb' ha hb =>
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [(h2 b hb' a ha').eq]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
  | inv a _ ha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [ha, inv_one]

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

theorem ae6D_sq_eq_one (hE : V3AE6E n) (hC : V3AE6EComm n) {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}
    {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y} (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (fr : AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y) :
    ∀ d ∈ ae6D Ω[R] W (u₁ * u₂), d * d = 1 := by
  have hEab := (hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr).1
  have hcomm := hC Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr
  set E := ae6E Ω[R] (u₁ * u₂) with hEdef
  set M := MGrp Ω[R] W with hMdef
  set s : Set Y := ⋃ m : ↥M, (conjSub (m : Y) E : Set Y) with hs
  have hD : ae6D Ω[R] W (u₁ * u₂) = Subgroup.closure s := by
    unfold ae6D
    rw [hs, Subgroup.closure_iUnion]
    simp only [Subgroup.closure_eq]
    rfl
  have hmem : ∀ x ∈ s, ∃ m ∈ M, ∃ e ∈ E, x = m * e * m⁻¹ := by
    intro x hx
    rw [hs, Set.mem_iUnion] at hx
    obtain ⟨m, hx⟩ := hx
    rw [SetLike.mem_coe, mem_conjSub_iff] at hx
    exact ⟨m, m.2, _, hx, by group⟩
  rw [hD]
  refine sq_eq_one_of_mem_closure ?_ ?_
  · intro x hx z hz
    obtain ⟨m, hm, e, he, rfl⟩ := hmem x hx
    obtain ⟨m', hm', e', he', rfl⟩ := hmem z hz
    have h := hcomm (m⁻¹ * m') (M.mul_mem (M.inv_mem hm) hm') e he e' he'
    have h' : Commute (m * e * m⁻¹) (m * ((m⁻¹ * m') * e' * (m⁻¹ * m')⁻¹) * m⁻¹) :=
      (h.map (MulAut.conj m).toMonoidHom)
    have e1 : m * ((m⁻¹ * m') * e' * (m⁻¹ * m')⁻¹) * m⁻¹ = m' * e' * m'⁻¹ := by group
    rwa [e1] at h'
  · intro x hx
    obtain ⟨m, hm, e, he, rfl⟩ := hmem x hx
    calc m * e * m⁻¹ * (m * e * m⁻¹) = m * (e * e) * m⁻¹ := by group
      _ = 1 := by rw [hEab.2 e he]; group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6DN
