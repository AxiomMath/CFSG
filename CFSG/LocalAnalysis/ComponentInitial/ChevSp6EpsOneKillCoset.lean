module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillAction

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

theorem conj_eq_inv_of_inv {G : Type*} [Group G] {t j : G} (ht2 : t * t = 1)
    (hj : (t * j) * (t * j) = 1) : t * j * t⁻¹ = j⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [htinv]
  calc t * j * t = (t * j) * (t * j) * j⁻¹ := by group
    _ = j⁻¹ := by rw [hj, one_mul]

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ}
  {z l₁ l₂ : G} (h : KillData u Jh E cV cE z l₁ l₂)
include h

variable {t : G} (ht : t ∈ normalizer (Jh : Set G)) (ht2 : t * t = 1)
include ht ht2

theorem actV_fix_of_inv {j : G} (hjJ : j ∈ Jh) (hj : (t * j) * (t * j) = 1) :
    h.actV t (cV j) = cV j := by
  rw [← h.cV_conj ht hjJ, conj_eq_inv_of_inv ht2 hj, h.cV_inv hjJ]

omit ht in
theorem diff_fix {j j' : G} (hjJ : j ∈ Jh) (hj'J : j' ∈ Jh) (hj : (t * j) * (t * j) = 1)
    (hj' : (t * j') * (t * j') = 1) (hcv : cV j' = cV j) :
    j'⁻¹ * j ∈ E ∧ t * (j'⁻¹ * j) * t⁻¹ = j'⁻¹ * j := by
  have he : j'⁻¹ * j ∈ E := h.mem_E_of_cV_eq hj'J hjJ hcv
  refine ⟨he, ?_⟩
  have e1 : t * (j'⁻¹ * j) * t⁻¹ = (t * j' * t⁻¹)⁻¹ * (t * j * t⁻¹) := by group
  rw [e1, conj_eq_inv_of_inv ht2 hj, conj_eq_inv_of_inv ht2 hj', inv_inv]
  set e := j'⁻¹ * j with hedef
  have hj_eq : j = j' * e := by rw [hedef]; group
  rw [hj_eq, mul_inv_rev, ← mul_assoc]
  have hc := h.central e⁻¹ (inv_mem he) j' hj'J
  rw [← hc, mul_assoc, mul_inv_cancel, mul_one, h.E_inv_eq he]

theorem beta_mem_of_mem {j₁ j₂ j₃ : G} (h₁J : j₁ ∈ Jh) (h₂J : j₂ ∈ Jh) (h₃J : j₃ ∈ Jh)
    (h₁ : (t * j₁) * (t * j₁) = 1) (h₂ : (t * j₂) * (t * j₂) = 1) (h₃ : (t * j₃) * (t * j₃) = 1)
    (hcv : cV j₃ = cV j₁ ^^^ cV j₂) :
    ∃ x, x < 512 ∧ h.actE t x ^^^ x = betaOf u (cV j₁) (cV j₂) := by
  have h12 := mul_mem h₁J h₂J
  have he : (j₁ * j₂)⁻¹ * j₃ ∈ E :=
    h.mem_E_of_cV_eq h12 h₃J (by rw [h.cV_mul _ h₁J _ h₂J, hcv])
  set e := (j₁ * j₂)⁻¹ * j₃ with hedef
  have hj3 : j₃ = j₁ * j₂ * e := by rw [hedef]; group
  set e' := t * e * t⁻¹ with he'def
  have he' : e' ∈ E := h.conj_mem_E ht he
  set c := j₁⁻¹ * j₂⁻¹ * j₁ * j₂ with hcdef
  have hc : c ∈ E := h.comm_mem_E h₁J h₂J
  have e1 : t * j₃ * t⁻¹ = j₁⁻¹ * j₂⁻¹ * e' := by
    rw [hj3, show t * (j₁ * j₂ * e) * t⁻¹ = (t * j₁ * t⁻¹) * (t * j₂ * t⁻¹) * (t * e * t⁻¹) by
      group, conj_eq_inv_of_inv ht2 h₁, conj_eq_inv_of_inv ht2 h₂]
  have e2 : t * j₃ * t⁻¹ = e * (j₂⁻¹ * j₁⁻¹) := by
    calc t * j₃ * t⁻¹ = j₃⁻¹ := conj_eq_inv_of_inv ht2 h₃
      _ = (j₁ * j₂ * e)⁻¹ := by rw [← hj3]
      _ = e⁻¹ * (j₂⁻¹ * j₁⁻¹) := by group
      _ = e * (j₂⁻¹ * j₁⁻¹) := by rw [h.E_inv_eq he]
  have e3 : j₁⁻¹ * j₂⁻¹ = c * (j₂⁻¹ * j₁⁻¹) := by rw [hcdef]; group
  have hk : c * e' = e := by
    have h4 : c * (j₂⁻¹ * j₁⁻¹) * e' = e * (j₂⁻¹ * j₁⁻¹) := by rw [← e3, ← e1, e2]
    have hm : j₂⁻¹ * j₁⁻¹ ∈ Jh := mul_mem (inv_mem h₂J) (inv_mem h₁J)
    have hcomm := h.central e' he' _ hm
    calc c * e' = c * (j₂⁻¹ * j₁⁻¹) * e' * (j₂⁻¹ * j₁⁻¹)⁻¹ := by
          rw [mul_assoc c, ← hcomm]; group
      _ = e := by rw [h4]; group
  refine ⟨cE e, h.cE_lt e he, ?_⟩
  rw [← h.cE_conj he, ← he'def, ← h.cE_comm h₁J h₂J, ← hcdef]
  have hce : c = e * e' := by
    calc c = c * e' * e' := by rw [mul_assoc, h.E_sq he', mul_one]
      _ = e * e' := by rw [hk]
  rw [hce, h.cE_mul e he e' he', Nat.xor_comm]

theorem card_inv_lt [Finite G] {v₀ w₀ : ℕ} (hv₀ : v₀ < 64) (hw₀ : w₀ < 64) (hfv : h.actV t v₀ = v₀)
    (hfw : h.actV t w₀ = w₀) (hβ : ∀ x, x < 512 → h.actE t x ^^^ x ≠ betaOf u v₀ w₀) :
    Nat.card {j : Jh // (t * j) * (t * j) = 1} <
      Nat.card {v : Fin 64 // h.actV t v = v} * Nat.card {e : Fin 512 // h.actE t e = e} := by
  classical
  let I := {j : Jh // (t * j) * (t * j) = 1}
  let ℓ : ℕ → G := fun v => if hv : ∃ j : I, cV (j : G) = v then ((Classical.choose hv : I) : G)
    else 1
  have hℓ : ∀ j : I, ℓ (cV (j : G)) ∈ Jh ∧ (t * ℓ (cV (j : G))) * (t * ℓ (cV (j : G))) = 1 ∧
      cV (ℓ (cV (j : G))) = cV (j : G) := by
    intro j
    have hv : ∃ j' : I, cV (j' : G) = cV (j : G) := ⟨j, rfl⟩
    simp only [ℓ, dite_eq_left hv]
    exact ⟨(Classical.choose hv).1.2, (Classical.choose hv).2, Classical.choose_spec hv⟩
  have hfix : ∀ j : I, (ℓ (cV (j : G)))⁻¹ * (j : G) ∈ E ∧
      t * ((ℓ (cV (j : G)))⁻¹ * (j : G)) * t⁻¹ = (ℓ (cV (j : G)))⁻¹ * (j : G) := fun j =>
    h.diff_fix ht2 j.1.2 (hℓ j).1 j.2 (hℓ j).2.1 (hℓ j).2.2
  let Φ : I → {v : Fin 64 // h.actV t v = v} × {e : Fin 512 // h.actE t e = e} := fun j =>
    (⟨⟨cV (j : G), h.cV_lt _ j.1.2⟩, h.actV_fix_of_inv ht ht2 j.1.2 j.2⟩,
      ⟨⟨cE ((ℓ (cV (j : G)))⁻¹ * (j : G)), h.cE_lt _ (hfix j).1⟩, by
        show h.actE t (cE _) = cE _
        rw [← h.cE_conj (hfix j).1, (hfix j).2]⟩)
  have hΦ : Function.Injective Φ := by
    intro j j' hjj
    have h1 : cV (j : G) = cV (j' : G) := congrArg (fun p => (p.1.1 : ℕ)) hjj
    have h2 : cE ((ℓ (cV (j : G)))⁻¹ * (j : G)) = cE ((ℓ (cV (j' : G)))⁻¹ * (j' : G)) :=
      congrArg (fun p => (p.2.1 : ℕ)) hjj
    rw [← h1] at h2
    have h3 := h.cE_injOn (hfix j).1 (by rw [h1]; exact (hfix j').1) h2
    exact Subtype.ext (Subtype.ext (mul_left_cancel h3))
  have hvw : v₀ ^^^ w₀ < 64 := Nat.xor_lt_two_pow (n := 6) hv₀ hw₀
  have hfvw : h.actV t (v₀ ^^^ w₀) = v₀ ^^^ w₀ := by rw [h.actV_xor ht hv₀ hw₀, hfv, hfw]
  have hmiss : ∃ v, v < 64 ∧ h.actV t v = v ∧ ∀ j : I, cV (j : G) ≠ v := by
    by_contra hall0
    have hall : ∀ v, v < 64 → h.actV t v = v → ∃ j : I, cV (j : G) = v := fun v hv hf => by
      by_contra hne
      exact hall0 ⟨v, hv, hf, fun j hj => hne ⟨j, hj⟩⟩
    obtain ⟨j₁, hj₁⟩ := hall v₀ hv₀ hfv
    obtain ⟨j₂, hj₂⟩ := hall w₀ hw₀ hfw
    obtain ⟨j₃, hj₃⟩ := hall _ hvw hfvw
    obtain ⟨x, hx, hxβ⟩ := h.beta_mem_of_mem ht ht2 j₁.1.2 j₂.1.2 j₃.1.2 j₁.2 j₂.2 j₃.2
      (by rw [hj₁, hj₂, hj₃])
    rw [hj₁, hj₂] at hxβ
    exact hβ x hx hxβ
  obtain ⟨v, hv, hfv', hnot⟩ := hmiss
  have hnsurj : ¬ Function.Surjective Φ := by
    intro hs
    have h0 : h.actE t 0 = 0 := by
      have := h.actE_xor ht (x := 0) (y := 0) (by norm_num) (by norm_num)
      rw [Nat.xor_self] at this
      exact xor_self_eq this
    obtain ⟨j, hj⟩ := hs (⟨⟨v, hv⟩, hfv'⟩, ⟨⟨0, by norm_num⟩, h0⟩)
    exact hnot j (congrArg (fun p => (p.1.1 : ℕ)) hj)
  have : Fintype I := Fintype.ofFinite _
  rw [← Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective Φ hΦ hnsurj

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
