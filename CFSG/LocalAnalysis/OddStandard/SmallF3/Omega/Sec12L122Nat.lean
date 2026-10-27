module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Mod

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem isPermModuleMod_bot_of_via {n : ℕ} {φ : (Fin n → ZMod 2) → G} {E H : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin n))} (hHE : H ≤ normalizer (E : Set G))
    (h : IsPermModuleVia IsEvenVec φ E H Alt) :
    IsPermModuleMod IsEvenVec {0} φ E ⊥ H Alt := by
  have h0ev : IsEvenVec (0 : Fin n → ZMod 2) := by simp [IsEvenVec]
  have hφ0 : φ 0 = 1 := by
    have h00 := h.1 0 0 h0ev h0ev
    rw [add_zero] at h00
    exact mul_eq_left.1 h00.symm
  have hbot : H ≤ normalizer (⊥ : Subgroup G) := Subgroup.le_normalizer_of_normal
  refine ⟨bot_le, ?_, hHE, hbot, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf]; infer_instance
  · intro v hv
    exact (h.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
  · intro v w hv hw
    rw [h.1 v w hv hw, inv_mul_cancel]
    exact Subgroup.one_mem ⊥
  · intro v hv
    rw [Subgroup.mem_bot, Set.mem_singleton_iff]
    constructor
    · intro hφv
      exact h.2.1 v 0 hv h0ev (by rw [hφv, hφ0])
    · intro hv0
      rw [hv0, hφ0]
  · intro x hx
    obtain ⟨v, hv, hφv⟩ := (h.2.2.1 x).mp hx
    exact ⟨v, hv, by rw [Subgroup.mem_bot, ← hφv, inv_mul_cancel]⟩
  · intro x hx
    obtain ⟨σ, hσ, hσφ⟩ := h.2.2.2.1 x hx
    exact ⟨σ, hσ, fun v hv => by rw [Subgroup.mem_bot, hσφ v hv, inv_mul_cancel]⟩
  · intro σ hσ
    obtain ⟨x, hx, hxφ⟩ := h.2.2.2.2 σ hσ
    exact ⟨x, hx, fun v hv => by rw [Subgroup.mem_bot, hxφ v hv, inv_mul_cancel]⟩

private theorem sec122_f_conj {t y p : G} (hy : y * t = t * y) :
    sec12f t (y * p * y⁻¹) = y * sec12f t p * y⁻¹ := by
  have hyt : y⁻¹ * t * y = t := by rw [mul_assoc, ← hy]; group
  have hyinv : y⁻¹ * t⁻¹ = t⁻¹ * y⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hy]
  rw [sec12f, sec12f]
  calc (y * p * y⁻¹) * t * (y * p * y⁻¹)⁻¹ * t⁻¹
      = y * p * (y⁻¹ * t * y) * p⁻¹ * (y⁻¹ * t⁻¹) := by group
    _ = y * p * t * p⁻¹ * (t⁻¹ * y⁻¹) := by rw [hyt, hyinv]
    _ = y * (p * t * p⁻¹ * t⁻¹) * y⁻¹ := by group

theorem sec122_act_W {t : G} {V B Y W : Subgroup G} {φ s : (Fin 5 → ZMod 2) → G}
    (hM : Sec122Mod t V B Y W φ s) {x : G} (hxN : x ∈ normalizer (W : Set G))
    (hxt : x * t = t * x) {σ : Equiv.Perm (Fin 5)}
    (hσ : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) :
    ∀ n, IsEvenVec n → x * s n * x⁻¹ = s (permVec σ n) := by
  intro n hn
  have hsnW : s n ∈ W := (hM.hW (s n)).mpr ⟨n, hn, rfl⟩
  have hconjW : x * s n * x⁻¹ ∈ W :=
    (Subgroup.mem_set_normalizer_iff.mp hxN (s n)).mp hsnW
  obtain ⟨m, hm, hsm⟩ := (hM.hW (x * s n * x⁻¹)).mp hconjW
  have h1 : sec12f t (x * s n * x⁻¹) = φ (permVec σ n) := by
    rw [sec122_f_conj hxt, hM.sf n hn, hσ n hn]
  have h2 : sec12f t (s m) = φ m := hM.sf m hm
  have hφeq : φ (permVec σ n) = φ m := by rw [← h1, ← h2, hsm]
  have hm_eq : permVec σ n = m :=
    hM.perm.2.1 (permVec σ n) m (isEvenVec_permVec σ hn) hm hφeq
  rw [hsm, ← hm_eq]

private theorem sec122_via_B {t : G} {V B Y W : Subgroup G} {φ s : (Fin 5 → ZMod 2) → G}
    (hM : Sec122Mod t V B Y W φ s) {X : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 5))}
    (hact : ∀ x ∈ X, ∃ σ ∈ Alt, ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (hsurj : ∀ σ ∈ Alt, ∃ x ∈ X, ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) :
    IsPermModuleVia IsEvenVec φ B X Alt :=
  ⟨hM.perm.1, hM.perm.2.1, hM.perm.2.2.1, hact, hsurj⟩

private theorem sec122_via_W {t : G} {V B Y W : Subgroup G} {φ s : (Fin 5 → ZMod 2) → G}
    (hM : Sec122Mod t V B Y W φ s) {X : Subgroup G} {Alt : Subgroup (Equiv.Perm (Fin 5))}
    (hXW : X ≤ normalizer (W : Set G)) (hXt : ∀ x ∈ X, x * t = t * x)
    (hact : ∀ x ∈ X, ∃ σ ∈ Alt, ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (hsurj : ∀ σ ∈ Alt, ∃ x ∈ X, ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) :
    IsPermModuleVia IsEvenVec s W X Alt := by
  refine ⟨hM.sadd, ?_, ?_, ?_, ?_⟩
  ·
    intro v w hv hw hsvw
    have hφeq : φ v = φ w := by rw [← hM.sf v hv, hsvw, hM.sf w hw]
    exact hM.perm.2.1 v w hv hw hφeq
  ·
    intro x
    constructor
    · intro hx
      obtain ⟨v, hv, rfl⟩ := (hM.hW x).mp hx
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hM.hW (s v)).mpr ⟨v, hv, rfl⟩
  ·
    intro x hx
    obtain ⟨σ, hσ, hσφ⟩ := hact x hx
    exact ⟨σ, hσ, fun v hv => sec122_act_W hM (hXW hx) (hXt x hx) hσφ v hv⟩
  ·
    intro σ hσ
    obtain ⟨x, hx, hxφ⟩ := hsurj σ hσ
    exact ⟨x, hx, fun v hv => sec122_act_W hM (hXW hx) (hXt x hx) hxφ v hv⟩

theorem sec122_natmods {t : G} {V B Y W X : Subgroup G} {φ s : (Fin 5 → ZMod 2) → G}
    (hM : Sec122Mod t V B Y W φ s) (hXB : X ≤ normalizer (B : Set G))
    (hXW : X ≤ normalizer (W : Set G)) (hXt : ∀ x ∈ X, x * t = t * x)
    (hact : ∀ x ∈ X, ∃ σ : Equiv.Perm (Fin 5),
      ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (hsurj : ∀ σ ∈ alternatingGroup (Fin 5), ∃ x ∈ X,
      ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))
    (hθ : (Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) ∧
        ∀ x ∈ X, ∃ σ ∈ alternatingGroup (Fin 5),
          ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) ∨
      (Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧
        ∀ σ : Equiv.Perm (Fin 5), ∃ x ∈ X,
          ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v))) :
    ∃ V1 V2 : Subgroup G, V1 ⊔ V2 = V ∧ V1 ⊓ V2 = ⊥ ∧
      ((Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))) ∧ IsNatModA5 V1 ⊥ X ∧ IsNatModA5 V2 ⊥ X) ∨
        (Nonempty (↥X ≃* Equiv.Perm (Fin 5)) ∧ IsNatModS5 V1 ⊥ X ∧ IsNatModS5 V2 ⊥ X)) := by
  have hsup : B ⊔ W = V := by
    refine le_antisymm (sup_le hM.BV hM.W_le_V) ?_
    intro v hv
    obtain ⟨w, hw, b, hb, rfl⟩ := hM.V_eq_mul v hv
    rw [sup_comm]
    exact Subgroup.mul_mem_sup hw hb
  have hinf : B ⊓ W = ⊥ := by rw [inf_comm]; exact hM.W_inf_B
  refine ⟨B, W, hsup, hinf, ?_⟩
  rcases hθ with ⟨hiso, hactA5⟩ | ⟨hiso, hactAll⟩
  ·
    left
    exact ⟨hiso,
      ⟨φ, isPermModuleMod_bot_of_via hXB (sec122_via_B hM hactA5 hsurj)⟩,
      ⟨s, isPermModuleMod_bot_of_via hXW (sec122_via_W hM hXW hXt hactA5 hsurj)⟩⟩
  ·
    right
    have hactTop : ∀ x ∈ X, ∃ σ ∈ (⊤ : Subgroup (Equiv.Perm (Fin 5))),
        ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) := by
      intro x hx
      obtain ⟨σ, hσ⟩ := hact x hx
      exact ⟨σ, Subgroup.mem_top σ, hσ⟩
    have hsurjTop : ∀ σ ∈ (⊤ : Subgroup (Equiv.Perm (Fin 5))), ∃ x ∈ X,
        ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v) :=
      fun σ _ => hactAll σ
    exact ⟨hiso,
      ⟨φ, isPermModuleMod_bot_of_via hXB (sec122_via_B hM hactTop hsurjTop)⟩,
      ⟨s, isPermModuleMod_bot_of_via hXW (sec122_via_W hM hXW hXt hactTop hsurjTop)⟩⟩

end CFSG.OddStandard.SmallF3.Omega
