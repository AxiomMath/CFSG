module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourSplitting
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearFieldFourRoots

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFour

open Subgroup LinearFlag CFSG.ComponentClassification
open scoped commutatorElement

variable {k E : Type*} [Field k] [Group E] [Finite E]

omit [Finite E] in
theorem mul_comm_of_conj_root (η : E →* projectiveSL 3 k) (r : k → projectiveSL 3 k) (g : E)
    (hg : ∀ a, (η g)⁻¹ * r a * η g = wP a)
    (hW : ∀ z₁ z₂ : E, (∃ c, η z₁ = wP c) → (∃ c, η z₂ = wP c) → z₁ * z₂ = z₂ * z₁)
    (z₁ z₂ : E) (h₁ : ∃ a, η z₁ = r a) (h₂ : ∃ a, η z₂ = r a) : z₁ * z₂ = z₂ * z₁ := by
  obtain ⟨a₁, ha₁⟩ := h₁
  obtain ⟨a₂, ha₂⟩ := h₂
  have h := hW (g⁻¹ * z₁ * g) (g⁻¹ * z₂ * g)
    ⟨a₁, by rw [map_mul, map_mul, map_inv, ha₁, hg]⟩
    ⟨a₂, by rw [map_mul, map_mul, map_inv, ha₂, hg]⟩
  have h' : g⁻¹ * (z₁ * z₂) * g = g⁻¹ * (z₂ * z₁) * g := by
    calc g⁻¹ * (z₁ * z₂) * g = (g⁻¹ * z₁ * g) * (g⁻¹ * z₂ * g) := by group
      _ = (g⁻¹ * z₂ * g) * (g⁻¹ * z₁ * g) := h
      _ = g⁻¹ * (z₂ * z₁) * g := by group
  simpa using h'

theorem exists_cover_witnesses (hk : Nat.card k = 4) (η : E →* projectiveSL 3 k)
    (hη : Function.Surjective η) (hker : ∀ z, η z = 1 → z ∈ center E) :
    ∃ t s x : E, t * t = 1 ∧ s * s = 1 ∧ η t = wP 1 ∧ η s ≠ 1 ∧ ⁅t, s⁆ = 1 ∧ ⁅t, x⁆ = 1 ∧
      ⁅s, x⁆ ≠ 1 := by
  have := charP_two_of_card_eq_four hk
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hk
  have hω2 : ω * ω = ω + 1 := omega_mul_omega hk hω0 hω1
  have hω3 : ω * ω * ω = 1 := omega_cube hk hω0
  have hω4 : 1 + ω + ω * ω = 0 := one_add_omega_add_omega_sq hk hω0 hω1
  have h2 : ∀ a : k, a + a = 0 := CharTwo.add_self_eq_zero
  have hωω : ω + ω * ω = 1 := by linear_combination hω4 - h2 1
  obtain ⟨u, hu⟩ := hη (hP ω hω3)
  obtain ⟨g₂₃, hg₂₃⟩ := hη s₂₃P
  obtain ⟨g₁₂, hg₁₂⟩ := hη s₁₂P
  have hWcomm : ∀ z₁ z₂ : E, (∃ c, η z₁ = wP c) → (∃ c, η z₂ = wP c) → z₁ * z₂ = z₂ * z₁ := by
    rintro z₁ z₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    obtain ⟨x₀, hx₀⟩ := hη (xP c₂)
    obtain ⟨y₀, hy₀⟩ := hη (yP 1)
    have hz : η (⁅x₀, y₀⁆⁻¹ * z₂) = 1 := by
      rw [map_mul, map_inv, map_commutatorElement, hx₀, hy₀, commutatorElement_xP_yP, mul_one,
        h₂, inv_mul_cancel]
    have hζ := hker _ hz
    have hcx : ⁅z₁, x₀⁆ ∈ center E := hker _ (by
      rw [map_commutatorElement, h₁, hx₀, commutatorElement_eq_one_iff_mul_comm]
      exact wP_mul_xP c₁ c₂)
    have hcy : ⁅z₁, y₀⁆ ∈ center E := hker _ (by
      rw [map_commutatorElement, h₁, hy₀, commutatorElement_eq_one_iff_mul_comm]
      exact wP_mul_yP c₁ 1)
    have h1 := commute_commutatorElement_of_mem_center hcx hcy
    calc z₁ * z₂ = z₁ * ⁅x₀, y₀⁆ * (⁅x₀, y₀⁆⁻¹ * z₂) := by group
      _ = ⁅x₀, y₀⁆ * (z₁ * (⁅x₀, y₀⁆⁻¹ * z₂)) := by rw [h1, mul_assoc]
      _ = ⁅x₀, y₀⁆ * ((⁅x₀, y₀⁆⁻¹ * z₂) * z₁) := by rw [mem_center_iff.mp hζ z₁]
      _ = z₂ * z₁ := by group
  have hXcomm := mul_comm_of_conj_root η xP g₂₃ (fun a => by rw [hg₂₃, s₂₃P_conj_xP]) hWcomm
  have hYcomm := mul_comm_of_conj_root η yP g₁₂ (fun b => by rw [hg₁₂, s₁₂P_conj_yP]) hWcomm
  have hsq : ∀ (r : k → projectiveSL 3 k), (∀ a b, r (a + b) = r a * r b) → (∀ a, r a * r a = 1) :=
    fun r hr a => by
      have h0 : r 0 = 1 := by
        have h := hr 0 0
        rw [add_zero] at h
        exact left_eq_mul.mp h
      rw [← hr, h2, h0]
  obtain ⟨ρw, hρw, hρw_add, hρw_conj⟩ := exists_equivariant_additive_lift η hker wP wP_add
    (hsq wP wP_add) (fun c => hη _) hWcomm u (ω * ω) (fun c => by rw [hu, hP_conj_wP])
    (by linear_combination hω4 + ω * hω3)
  obtain ⟨ρx, hρx, hρx_add, hρx_conj⟩ := exists_equivariant_additive_lift η hker xP xP_add
    (hsq xP xP_add) (fun a => hη _) hXcomm u ω (fun a => by rw [hu, hP_conj_xP]) hω4
  obtain ⟨ρy, hρy, hρy_add, hρy_conj⟩ := exists_equivariant_additive_lift η hker yP yP_add
    (hsq yP yP_add) (fun b => hη _) hYcomm u ω (fun b => by rw [hu, hP_conj_yP]) hω4
  have hzero : ∀ ρ : k → E, (∀ a b, ρ (a + b) = ρ a * ρ b) → ρ 0 = 1 := fun ρ hρ => by
    have h := hρ 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hρw0 := hzero ρw hρw_add
  have hρx0 := hzero ρx hρx_add
  have hinv : ∀ ρ : k → E, (∀ a b, ρ (a + b) = ρ a * ρ b) → ∀ a, ρ a * ρ a = 1 :=
    fun ρ hρ a => by rw [← hρ, h2, hzero ρ hρ]
  have hfc : ∀ c a, ⁅ρw c, ρx a⁆ ∈ center E := fun c a => hker _ (by
    rw [map_commutatorElement, hρw, hρx, commutatorElement_eq_one_iff_mul_comm]
    exact wP_mul_xP c a)
  have hgc : ∀ c b, ⁅ρw c, ρy b⁆ ∈ center E := fun c b => hker _ (by
    rw [map_commutatorElement, hρw, hρy, commutatorElement_eq_one_iff_mul_comm]
    exact wP_mul_yP c b)
  have hcentral : ∀ z ∈ center E, u * z * u⁻¹ = z := fun z hz => by
    rw [mem_center_iff.mp hz u, mul_inv_cancel_right]
  have hconj : ∀ z₁ z₂ : E, u * ⁅z₁, z₂⁆ * u⁻¹ = ⁅u * z₁ * u⁻¹, u * z₂ * u⁻¹⁆ := fun z₁ z₂ => by
    simp only [commutatorElement_def]
    group
  have hcube : ∀ c : k, ω * ω * (ω * c) = c := fun c => by linear_combination c * hω3
  have hf_shift : ∀ c a, ⁅ρw c, ρx (ω * a)⁆ = ⁅ρw (ω * c), ρx a⁆ := fun c a => by
    have h := hconj (ρw (ω * c)) (ρx a)
    rw [hcentral _ (hfc _ _), hρw_conj, hρx_conj, hcube] at h
    exact h.symm
  have hg_shift : ∀ c b, ⁅ρw c, ρy (ω * b)⁆ = ⁅ρw (ω * c), ρy b⁆ := fun c b => by
    have h := hconj (ρw (ω * c)) (ρy b)
    rw [hcentral _ (hgc _ _), hρw_conj, hρy_conj, hcube] at h
    exact h.symm
  have hf_one : ∀ c a, ⁅ρw c, ρx a⁆ = ⁅ρw (c * a), ρx 1⁆ := fun c a => by
    rcases eq_zero_or_eq_one_or hk hω0 hω1 a with rfl | rfl | rfl | rfl
    · rw [hρx0, mul_zero, hρw0, commutatorElement_one_right, commutatorElement_one_left]
    · rw [mul_one]
    · have e := hf_shift c 1
      rw [mul_one] at e
      rw [e, mul_comm]
    · have e1 := hf_shift c ω
      have e2 := hf_shift (ω * c) 1
      rw [mul_one] at e2
      rw [← hω2, e1, e2, show c * (ω * ω) = ω * (ω * c) by ring]
  have hg_one : ∀ c b, ⁅ρw c, ρy b⁆ = ⁅ρw (c * b), ρy 1⁆ := fun c b => by
    rcases eq_zero_or_eq_one_or hk hω0 hω1 b with rfl | rfl | rfl | rfl
    · rw [hzero ρy hρy_add, mul_zero, hρw0, commutatorElement_one_right,
        commutatorElement_one_left]
    · rw [mul_one]
    · have e := hg_shift c 1
      rw [mul_one] at e
      rw [e, mul_comm]
    · have e1 := hg_shift c ω
      have e2 := hg_shift (ω * c) 1
      rw [mul_one] at e2
      rw [← hω2, e1, e2, show c * (ω * ω) = ω * (ω * c) by ring]
  have hL_add : ∀ z z', ⁅ρw (z + z'), ρx 1⁆ = ⁅ρw z, ρx 1⁆ * ⁅ρw z', ρx 1⁆ := fun z z' => by
    rw [hρw_add, commutatorElement_mul_left_of_mem_center (hfc z' 1)]
  have hLM : ∀ b, ⁅ρw b, ρx 1⁆ = ⁅ρw (b * b), ρy 1⁆ := fun b => by
    have hd : η ((ρw b)⁻¹ * ⁅ρx 1, ρy b⁆) = 1 := by
      rw [map_mul, map_inv, map_commutatorElement, hρw, hρx, hρy, commutatorElement_xP_yP,
        one_mul, inv_mul_cancel]
    have hκ := hker _ hd
    have hdw : ⁅ρx 1, ρy b⁆ = ρw b * ((ρw b)⁻¹ * ⁅ρx 1, ρy b⁆) := by group
    have e1 : ⁅⁅ρx 1, ρy b⁆, ρx 1⁆ = ⁅ρw b, ρx 1⁆ := by
      conv_lhs => rw [hdw]
      exact CentralExtensions.commutator_mul_center_left _ _ _ hκ
    have e2 : ⁅⁅ρx 1, ρy b⁆, ρy b⁆ = ⁅ρw b, ρy b⁆ := by
      conv_lhs => rw [hdw]
      exact CentralExtensions.commutator_mul_center_left _ _ _ hκ
    have e3 := commutatorElement_commutatorElement_eq_of_involutions (hinv ρx hρx_add 1)
      (hinv ρy hρy_add b)
    rw [← e1, e3, e2, hg_one]
  have hz4 : ∀ z : k, z * z * (z * z) = z := fun z => by
    linear_combination pow_four_eq_self hk z
  have hML : ∀ z, ⁅ρw z, ρy 1⁆ = ⁅ρw (z * z), ρx 1⁆ := fun z => by
    rw [hLM (z * z), hz4]
  by_cases hL : ∀ z, ⁅ρw z, ρx 1⁆ = 1
  · refine ⟨ρw 1, ρx 1, ρy 1, hinv ρw hρw_add 1, hinv ρx hρx_add 1, hρw 1, ?_, hL 1, ?_, ?_⟩
    · rw [hρx]
      exact fun h => one_ne_zero ((xP_eq_one_iff 1).mp h)
    · rw [hML, mul_one, hL]
    · intro h
      have h' := congrArg η h
      rw [map_commutatorElement, hρx, hρy, commutatorElement_xP_yP, mul_one, map_one,
        wP_eq_one_iff] at h'
      exact one_ne_zero h'
  · obtain ⟨a, ha⟩ := not_forall.mp hL
    refine ⟨ρw 1, ρw ω, ρx a * ρy (a * a), hinv ρw hρw_add 1, hinv ρw hρw_add ω, hρw 1, ?_, ?_,
      ?_, ?_⟩
    · rw [hρw]
      exact fun h => hω0 ((wP_eq_one_iff ω).mp h)
    · rw [commutatorElement_eq_one_iff_mul_comm, ← hρw_add, ← hρw_add, add_comm]
    · rw [commutatorElement_mul_right_of_mem_center' (hgc 1 (a * a)), hf_one, hg_one, one_mul,
        one_mul, hML, hz4, ← hL_add, h2, hρw0, commutatorElement_one_left]
    · rw [commutatorElement_mul_right_of_mem_center' (hgc ω (a * a)), hf_one, hg_one, hML,
        ← hL_add]
      have e : ω * a + ω * (a * a) * (ω * (a * a)) = a := by
        have ha4 : a * a * (a * a) = a := hz4 a
        linear_combination a * hωω + (ω * ω) * ha4
      rwa [e]

end LinearFieldFour

end CFSG.LocalAnalysis.ComponentInitial
