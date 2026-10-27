module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModE
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModARank

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Inst

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : Type*} [Group B]

variable {ρ : B →* (V ≃ₗ[ZMod 2] V)} {x t z h : B}

theorem modA_base (H : HypM ρ x t z h) (hA6 : Nonempty (Jbar ρ x ≃* alternatingGroup (Fin 6))) :
    A6Base (Jbar ρ x) (ρ x) where
  dim := H.dim
  mem := E25_rho_mem_Jbar ρ x
  ord := H.ord_x
  fix := H.fix
  iso := hA6

theorem modA_twist (H : HypM ρ x t z h) : A6Twist (Jbar ρ x) (ρ x) (ρ t) where
  sq := H.t_sq
  norm := fun g hg => by
    have h1 := E25_Jbar_conj ρ x t hg
    rwa [inv_eq_of_mul_eq_one_right H.t_sq] at h1
  comm := by rw [← map_mul, ← map_mul, H.tx]
  nc := E25_tbar_not_central H

end Inst

theorem module_A6_abs {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : Type*} [Group B]
    [Finite B] {ρ : B →* (V ≃ₗ[ZMod 2] V)} {x t z h : B}
    (H : HypM ρ x t z h) (hA6 : Nonempty (Jbar ρ x ≃* alternatingGroup (Fin 6))) :
    ∃ V₁ V₂ : Submodule (ZMod 2) V, finrank (ZMod 2) V₁ = 4 ∧ IsCompl V₁ V₂ ∧
      V₂ = V₁.map (ρ t : V →ₗ[ZMod 2] V) ∧ (∀ g ∈ Jbar ρ x, Stable g V₁ ∧ Stable g V₂) ∧
      (∀ U : Submodule (ZMod 2) V, U ≤ V₁ → (∀ g ∈ Jbar ρ x, Stable g U) → U = ⊥ ∨ U = V₁) ∧
      (∀ U : Submodule (ZMod 2) V, U ≤ V₂ → (∀ g ∈ Jbar ρ x, Stable g U) → U = ⊥ ∨ U = V₂) ∧
      (∀ g ∈ Jbar ρ x, (∀ v ∈ V₁, g v = v) → g = 1) ∧
      (∀ g ∈ Jbar ρ x, (∀ v ∈ V₂, g v = v) → g = 1) ∧
      (∀ U : Submodule (ZMod 2) V, (∀ g ∈ Jbar ρ x, Stable g U) →
        U = ⊥ ∨ U = V₁ ∨ U = V₂ ∨ U = ⊤) ∧
      centralizer ((Jbar ρ x : Subgroup (V ≃ₗ[ZMod 2] V)) : Set (V ≃ₗ[ZMod 2] V)) = ⊥ ∧
      (∀ b : B, (V₁.map (ρ b : V →ₗ[ZMod 2] V) = V₁ ∧ V₂.map (ρ b : V →ₗ[ZMod 2] V) = V₂) ∨
        (V₁.map (ρ b : V →ₗ[ZMod 2] V) = V₂ ∧ V₂.map (ρ b : V →ₗ[ZMod 2] V) = V₁)) := by
  have Bs := modA_base H hA6
  have Tw := modA_twist H
  obtain ⟨M, hM, sM⟩ := modA_exists_four Bs
  have sM2 := modA_stable_map Tw sM
  have hM2 := modA_finrank_map hM (ρ t)
  refine ⟨M, M.map (ρ t : V →ₗ[ZMod 2] V), hM, modA_isCompl Bs Tw hM sM, rfl,
    fun g hg => ⟨sM g hg, sM2 g hg⟩, fun U hUM hU => modA_stable_le_four Bs hM hU hUM,
    fun U hUM hU => modA_stable_le_four Bs hM2 hU hUM, modA_faithful Bs hM sM,
    modA_faithful Bs hM2 sM2, fun U hU => modA_classify Bs Tw hM sM hU,
    modA_centralizer Bs Tw hM sM, fun b => ?_⟩
  exact modA_perm Bs Tw hM sM (fun g hg => E25_Jbar_conj ρ x b hg)

section RankThree

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : Type*} [Group B] [Finite B]

variable {ρ : B →* (V ≃ₗ[ZMod 2] V)} {x t z h : B}

omit [Finite B] in
theorem modA_E25_rk_summand (H : HypM ρ x t z h) {M : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (sM : ∀ g ∈ Jbar ρ x, Stable g M)
    (hpow : ∀ g ∈ Jbar ρ x, ∃ k : ℕ, ∀ v ∈ M, g v = (ρ x) ^ k • v) {s : B}
    (hs2 : ρ s * ρ s = 1) (hs : ρ s ∈ modA_stab M) :
    rk (modA_restr M ⟨ρ s, hs⟩) = 0 ∨ rk (modA_restr M ⟨ρ s, hs⟩) = 2 := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  set a₁ : M ≃ₗ[ZMod 2] M := modA_resJ (Jbar ρ x) M sM ⟨ρ x, E25_rho_mem_Jbar ρ x⟩ with ha₁
  set g₁ : M ≃ₗ[ZMod 2] M := modA_restr M ⟨ρ s, hs⟩ with hg₁
  have hinv : (ρ s)⁻¹ = ρ s := inv_eq_of_mul_eq_one_right hs2
  have hx5 : ρ x ^ 5 = 1 := by rw [← H.ord_x]; exact pow_orderOf_eq_one _
  have ha5 : a₁ ^ 5 = 1 := by
    have : (⟨ρ x, E25_rho_mem_Jbar ρ x⟩ : Jbar ρ x) ^ 5 = 1 := Subtype.ext hx5
    rw [ha₁, ← map_pow, this, map_one]
  have hfix : ∀ w : M, a₁ w = w → w = 0 := fun w hw =>
    Subtype.ext (H.fix w (congrArg Subtype.val hw))
  have hg2 : g₁ * g₁ = 1 := by
    have : (⟨ρ s, hs⟩ : modA_stab M) * ⟨ρ s, hs⟩ = 1 := Subtype.ext hs2
    rw [hg₁, ← map_mul, this, map_one]
  have hg' : ρ s * ρ x * ρ s ∈ Jbar ρ x := by
    have h1 := E25_Jbar_conj ρ x s (E25_rho_mem_Jbar ρ x)
    rwa [hinv] at h1
  obtain ⟨k, hk⟩ := hpow _ hg'
  have hpowk : ∀ (n : ℕ) (w : M), ((a₁ ^ n) w : V) = ((ρ x) ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, pow_succ]
      exact ih (a₁ w)
  have hk' : g₁ * a₁ * g₁⁻¹ = a₁ ^ k := by
    rw [inv_eq_of_mul_eq_one_right hg2]
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rw [hpowk k w]
    exact hk w w.2
  have hne1 := modA_rk_ne_one hM ha5 hfix hg2 hk'
  have hle : 2 * rk g₁ ≤ 4 := by
    have := two_mul_rk_le g₁ hg2
    rwa [hM] at this
  omega

theorem modA_E25_no_rank_three (H : HypM ρ x t z h)
    (hab : ∀ a ∈ Jbar ρ x, ∀ b ∈ Jbar ρ x, a * b = b * a) {s : B} (hs2 : ρ s * ρ s = 1) :
    rk (ρ s) ≠ 3 := by
  intro hs3
  obtain ⟨-, V₁, V₂, hd₁, hc, hV₂, hst, hperm, hpow, -⟩ := module_E25_abs H hab
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  have hd₂ : finrank (ZMod 2) V₂ = 4 := by
    rw [hV₂]
    exact (LinearEquiv.finrank_map_eq (ρ t) V₁).trans hd₁
  rcases hperm s with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hM₁ := modA_mem_stab_of_map_eq e1
    have hM₂ := modA_mem_stab_of_map_eq e2
    have h1 := modA_E25_rk_summand H hd₁ (fun g hg => (hst g hg).1) (fun g hg => (hpow g hg).1)
      hs2 hM₁
    have h2 := modA_E25_rk_summand H hd₂ (fun g hg => (hst g hg).2) (fun g hg => (hpow g hg).2)
      hs2 hM₂
    rw [modA_rk_add hc hM₁ hM₂] at hs3
    omega
  · have h4 := modA_rk_swap hc hd₁ H.dim hs2 (fun v hv => e1 ▸ ⟨v, hv, rfl⟩)
    omega

theorem modA_A6_rk_four (H : HypM ρ x t z h)
    (hA6 : Nonempty (Jbar ρ x ≃* alternatingGroup (Fin 6))) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ Jbar ρ x) (hg2 : g * g = 1) (hg1 : g ≠ 1) : rk g = 4 := by
  obtain ⟨V₁, V₂, hd₁, hc, hV₂, hst, -, -, -, -, -, -, -⟩ := module_A6_abs H hA6
  have Bs := modA_base H hA6
  haveI : Module.Finite (ZMod 2) V := modA_finite Bs
  have hd₂ : finrank (ZMod 2) V₂ = 4 := by
    rw [hV₂]
    exact (LinearEquiv.finrank_map_eq (ρ t) V₁).trans hd₁
  have sV₁ : ∀ g ∈ Jbar ρ x, Stable g V₁ := fun g hg => (hst g hg).1
  have sV₂ : ∀ g ∈ Jbar ρ x, Stable g V₂ := fun g hg => (hst g hg).2
  have hM₁ : g ∈ modA_stab V₁ := modA_le_stab sV₁ hg
  have hM₂ : g ∈ modA_stab V₂ := modA_le_stab sV₂ hg
  have hg2' : (⟨g, hg⟩ : Jbar ρ x) * ⟨g, hg⟩ = 1 := Subtype.ext hg2
  have hg1' : (⟨g, hg⟩ : Jbar ρ x) ≠ 1 := fun h1 => hg1 (congrArg Subtype.val h1)
  have r1 : rk (modA_restr V₁ ⟨g, hM₁⟩) = 2 := modA_rk_involution_two Bs hd₁ sV₁ ⟨g, hg⟩ hg2' hg1'
  have r2 : rk (modA_restr V₂ ⟨g, hM₂⟩) = 2 := modA_rk_involution_two Bs hd₂ sV₂ ⟨g, hg⟩ hg2' hg1'
  rw [modA_rk_add hc hM₁ hM₂, r1, r2]

theorem modA_A6_not_mem (H : HypM ρ x t z h)
    (hA6 : Nonempty (Jbar ρ x ≃* alternatingGroup (Fin 6))) {s : B} (hs2 : ρ s * ρ s = 1)
    (hs3 : rk (ρ s) = 3) : ρ s ∉ Jbar ρ x := by
  intro hmem
  haveI : Module.Finite (ZMod 2) V := modA_finite (modA_base H hA6)
  have hne : ρ s ≠ 1 := fun h1 => by
    rw [h1, modA_rk_one] at hs3
    omega
  have h4 := modA_A6_rk_four H hA6 hmem hs2 hne
  omega

theorem rank_three_abs (H : HypM ρ x t z h) {s : B}
    (hJ : Nonempty (Jbar ρ x ≃* alternatingGroup (Fin 6)) ∨
      ∀ a ∈ Jbar ρ x, ∀ b ∈ Jbar ρ x, a * b = b * a)
    (hs2 : ρ s * ρ s = 1) (hs3 : rk (ρ s) = 3) :
    Nonempty (Jbar ρ x ≃* alternatingGroup (Fin 6)) ∧ ρ s ∉ Jbar ρ x ∧
      ∃ V₁ : Submodule (ZMod 2) V, finrank (ZMod 2) V₁ = 4 ∧ (∀ g ∈ Jbar ρ x, Stable g V₁) ∧
        IsCompl V₁ (V₁.map (ρ t : V →ₗ[ZMod 2] V)) ∧ V₁.map (ρ s : V →ₗ[ZMod 2] V) = V₁ := by
  rcases hJ with hA6 | hab
  · obtain ⟨V₁, V₂, hd₁, hc, hV₂, hst, -, -, -, -, -, -, hperm⟩ := module_A6_abs H hA6
    haveI : Module.Finite (ZMod 2) V := modA_finite (modA_base H hA6)
    refine ⟨hA6, modA_A6_not_mem H hA6 hs2 hs3, V₁, hd₁, fun g hg => (hst g hg).1,
      hV₂ ▸ hc, ?_⟩
    rcases hperm s with ⟨e1, -⟩ | ⟨e1, -⟩
    · exact e1
    · exfalso
      have h4 := modA_rk_swap hc hd₁ H.dim hs2 (fun v hv => e1 ▸ ⟨v, hv, rfl⟩)
      omega
  · exact absurd hs3 (modA_E25_no_rank_three H hab hs2)

end RankThree

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
