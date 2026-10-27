module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Alt2a

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

@[expose] def sec1011_w0 : Fin 5 → ZMod 2 := sec1011_wfour 0 + sec1011_wfour 1

theorem sec1011_w0_even : IsEvenVec sec1011_w0 :=
  sec1011_isEvenVec_add (sec1011_wfour_even 0) (sec1011_wfour_even 1)

theorem sec1011_w0_weight : vecWeight sec1011_w0 = 2 :=
  sec1011_wfour_add_weight (by decide)

private theorem sec1011p_u_even (v : Fin 6 → ZMod 2) :
    IsEvenVec (∑ i : Fin 5, v i.succ • sec1011_wfour i) := by
  revert v
  unfold IsEvenVec sec1011_wfour
  decide +kernel

private theorem sec1011p_f4 (x : Fin 5 → ZMod 2) (hx : IsEvenVec x) :
    ∃ v : Fin 6 → ZMod 2, IsEvenVec v ∧ (∑ i : Fin 5, v i.succ • sec1011_wfour i) = x := by
  revert x
  unfold IsEvenVec sec1011_wfour
  decide +kernel

theorem sec1011_phi6_vtriple (h : Sec1011Core B t K φ) :
    sec1011_phi6 t φ sec1011_vtriple = t * φ sec1011_w0 := by
  letI : CommGroup A := { ‹Group A› with mul_comm := h.comm }
  have e0 := sec1011_phi6_single h 0
  have e1 := sec1011_phi6_single h 1
  have e2 := sec1011_phi6_single h 2
  rw [sec1011_delta_zero] at e0
  have h1 : sec1011_delta t φ 1 = t * φ (sec1011_wfour 0) := sec1011_delta_succ t φ 0
  have h2 : sec1011_delta t φ 2 = t * φ (sec1011_wfour 1) := sec1011_delta_succ t φ 1
  unfold sec1011_vtriple
  rw [sec1011_phi6_hom h, sec1011_phi6_hom h, e0, e1, e2, h1, h2, sec1011_w0,
    h.hom _ _ (sec1011_wfour_even 0) (sec1011_wfour_even 1)]
  calc t * (t * φ (sec1011_wfour 0)) * (t * φ (sec1011_wfour 1))
      = (t * t) * (t * (φ (sec1011_wfour 0) * φ (sec1011_wfour 1))) := by ac_rfl
    _ = t * (φ (sec1011_wfour 0) * φ (sec1011_wfour 1)) := by rw [h.t_sq, one_mul]

theorem sec1011_phi6_mem_B (h : Sec1011Core B t K φ) {u : Fin 6 → ZMod 2} (hu : IsEvenVec u) :
    sec1011_phi6 t φ u ∈ B := by
  have hu' : (∑ i, u i) = 0 := hu
  unfold sec1011_phi6
  rw [hu', ZMod.val_zero, pow_zero, one_mul]
  exact h.mem (sec1011p_u_even u)

theorem sec1011_phi6_even_surj (h : Sec1011Core B t K φ) {b : A} (hb : b ∈ B) :
    ∃ u : Fin 6 → ZMod 2, IsEvenVec u ∧ sec1011_phi6 t φ u = b := by
  obtain ⟨x, hx, hxφ⟩ := (h.mem_B b).1 hb
  obtain ⟨v, hv, hvu⟩ := sec1011p_f4 x hx
  have hv' : (∑ i, v i) = 0 := hv
  refine ⟨v, hv, ?_⟩
  unfold sec1011_phi6
  rw [hv', hvu, ZMod.val_zero, pow_zero, one_mul, hxφ]

theorem sec1011_p2_abs (h : Sec1011A2 B t K φ) :
    ∃ α₁ ∈ K, ∃ α₂ ∈ K,
      α₁ (t * φ sec1011_w0) = t * φ sec1011_w0 ∧ α₂ (t * φ sec1011_w0) = t * φ sec1011_w0 ∧
      α₁ * α₂ = α₂ * α₁ ∧ α₁ ^ 3 = 1 ∧ α₂ ^ 3 = 1 ∧
      ∀ b ∈ B, ∃ b₁ ∈ B, ∃ b₂ ∈ B, b = b₁ * α₁ b₁ * (b₂ * α₂ b₂) := by
  have hc := h.core
  obtain ⟨ρ, hinj, hact, hrange⟩ := sec1011_alt2_act h
  have hmem : sec1011_rho1 ∈ ρ.range ∧ sec1011_rho2 ∈ ρ.range := by
    rcases hrange with h' | h'
    · rw [h']
      exact sec1011_rho_mem_alt
    · rw [h']
      exact ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩
  obtain ⟨a1, ha1⟩ := MonoidHom.mem_range.mp hmem.1
  obtain ⟨a2, ha2⟩ := MonoidHom.mem_range.mp hmem.2
  have hφ : ∀ (a : ↥K) (v : Fin 6 → ZMod 2),
      (a : MulAut A) (sec1011_phi6 t φ v) = sec1011_phi6 t φ (permVec (ρ a) v) :=
    fun a v => sec1011_phi6_act hc (ρ a) (hact a) v
  have hcomm : a1 * a2 = a2 * a1 :=
    hinj (by rw [map_mul, map_mul, ha1, ha2, sec1011_rho_comm])
  have hcube1 : a1 ^ 3 = 1 := hinj (by rw [map_pow, ha1, map_one]; exact sec1011_rho_cube.1)
  have hcube2 : a2 ^ 3 = 1 := hinj (by rw [map_pow, ha2, map_one]; exact sec1011_rho_cube.2)
  have key : ∀ w1 w2 : Fin 6 → ZMod 2,
      sec1011_phi6 t φ w1 * (a1 : MulAut A) (sec1011_phi6 t φ w1) *
          (sec1011_phi6 t φ w2 * (a2 : MulAut A) (sec1011_phi6 t φ w2)) =
        sec1011_phi6 t φ ((w1 + permVec sec1011_rho1 w1) + (w2 + permVec sec1011_rho2 w2)) := by
    intro w1 w2
    rw [hφ a1 w1, ha1, hφ a2 w2, ha2, sec1011_phi6_hom hc, sec1011_phi6_hom hc,
      sec1011_phi6_hom hc]
  refine ⟨a1, a1.2, a2, a2.2, ?_, ?_, congrArg Subtype.val hcomm, congrArg Subtype.val hcube1,
    congrArg Subtype.val hcube2, ?_⟩
  · rw [← sec1011_phi6_vtriple hc, hφ, ha1, sec1011_rho_fix.1]
  · rw [← sec1011_phi6_vtriple hc, hφ, ha2, sec1011_rho_fix.2]
  · intro b hb
    obtain ⟨u, hu, rfl⟩ := sec1011_phi6_even_surj hc hb
    obtain ⟨w1, w2, hw1, hw2, hcase⟩ := sec1011_rho_span u hu
    refine ⟨sec1011_phi6 t φ w1, sec1011_phi6_mem_B hc hw1, sec1011_phi6 t φ w2,
      sec1011_phi6_mem_B hc hw2, ?_⟩
    rw [key]
    rcases hcase with h1 | h2
    · rw [← h1]
    · have hone : sec1011_phi6 t φ sec1011_one6 = 1 :=
        (sec1011_phi6_ker hc sec1011_one6).2 (Or.inr rfl)
      rw [← h2, sec1011_phi6_hom hc, hone, mul_one]

end CFSG.OddStandard.SmallF3.Omega
