
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillSylowBase

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowOffender

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ}
  {z l₁ l₂ : G} (h : KillData u Jh E cV cE z l₁ l₂)

include h

section S

variable [Finite G]

theorem card_lt_of_ea
    {A : Subgroup G} (hAS : A ≤ h.SG) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hsq : ∀ a ∈ A, a * a = 1) (hAJ : ¬ A ≤ Jh) : Nat.card A < 2 ^ (if u then 9 else 12) := by
  classical
  have hAX : A ≤ normalizer (Jh : Set G) := hAS.trans h.SG_le_X
  let A' := A.subgroupOf (normalizer (Jh : Set G))
  let Ab : Subgroup (Equiv.Perm (Fin 64)) := A'.map h.ρV
  have hmemAb : ∀ {σ}, σ ∈ Ab ↔ ∃ b ∈ A, ∃ hb : b ∈ normalizer (Jh : Set G), h.ρV ⟨b, hb⟩ = σ := by
    intro σ
    constructor
    · rintro ⟨⟨b, hb⟩, hbA, rfl⟩
      exact ⟨b, Subgroup.mem_subgroupOf.1 hbA, hb, rfl⟩
    · rintro ⟨b, hbA, hb, rfl⟩
      exact ⟨⟨b, hb⟩, Subgroup.mem_subgroupOf.2 hbA, rfl⟩
  have hAbG : Ab ≤ Gq u := by
    intro σ hσ
    obtain ⟨b, -, hb, rfl⟩ := hmemAb.1 hσ
    exact h.ρV_mem_Gq _
  have hAbc : ∀ σ ∈ Ab, ∀ τ ∈ Ab, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    obtain ⟨b, hbA, hb, rfl⟩ := hmemAb.1 hσ
    obtain ⟨c, hcA, hc, rfl⟩ := hmemAb.1 hτ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm b hbA c hcA)
  have hAbs : ∀ σ ∈ Ab, σ * σ = 1 := by
    intro σ hσ
    obtain ⟨b, hbA, hb, rfl⟩ := hmemAb.1 hσ
    rw [← map_mul, ← map_one h.ρV]
    congr 1
    exact Subtype.ext (hsq b hbA)
  have hAbne : Ab ≠ ⊥ := by
    intro hbot
    apply hAJ
    intro a ha
    have hK : a ∈ h.Kk := by
      refine ⟨⟨a, hAX ha⟩, MonoidHom.mem_ker.2 ?_, rfl⟩
      have : h.ρV ⟨a, hAX ha⟩ ∈ Ab := hmemAb.2 ⟨a, ha, hAX ha, rfl⟩
      rw [hbot] at this
      exact this
    exact (h.mem_Kk_iff_of_mem_SG (hAS ha)).1 hK
  have hbound := offender_bound hAbG hAbc hAbs hAbne
  have hcardA : Nat.card A = Nat.card (A ⊓ Jh : Subgroup G) * Nat.card Ab := by
    let f : A' →* Equiv.Perm (Fin 64) := h.ρV.comp A'.subtype
    have hrange : f.range = Ab := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hker : Nat.card f.ker = Nat.card (A ⊓ Jh : Subgroup G) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨((x : A') : G), Subgroup.mem_subgroupOf.1 (x : A').2,
            (h.mem_Kk_iff_of_mem_SG (hAS (Subgroup.mem_subgroupOf.1 (x : A').2))).1
              ⟨_, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2), rfl⟩⟩
          invFun := fun y => ⟨⟨⟨y, hAX y.2.1⟩, Subgroup.mem_subgroupOf.2 y.2.1⟩, by
            obtain ⟨⟨w, hw⟩, hwk, hwy⟩ := h.Jh_le_Kk y.2.2
            have : (⟨w, hw⟩ : normalizer (Jh : Set G)) = ⟨y, hAX y.2.1⟩ := Subtype.ext hwy
            rw [this] at hwk
            exact hwk⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv.symm,
      ← card_ker_mul_card_range f, hker, hrange]
  let ℓ : ℕ → G := fun v => if hv : ∃ x ∈ (A ⊓ Jh : Subgroup G), cV x = v then
    Classical.choose hv else 1
  have hℓ : ∀ x ∈ (A ⊓ Jh : Subgroup G), ℓ (cV x) ∈ (A ⊓ Jh : Subgroup G) ∧
      cV (ℓ (cV x)) = cV x := by
    intro x hx
    have hv : ∃ y ∈ (A ⊓ Jh : Subgroup G), cV y = cV x := ⟨x, hx, rfl⟩
    simp only [ℓ, dite_eq_left hv]
    exact Classical.choose_spec hv
  have hEmem : ∀ x ∈ (A ⊓ Jh : Subgroup G), (ℓ (cV x))⁻¹ * x ∈ E ∧ (ℓ (cV x))⁻¹ * x ∈ A :=
    fun x hx => ⟨h.mem_E_of_cV_eq (hℓ x hx).1.2 hx.2 (hℓ x hx).2,
      mul_mem (inv_mem (hℓ x hx).1.1) hx.1⟩
  let Φ : (A ⊓ Jh : Subgroup G) → {v : Fin 64 // qOf u v = 0 ∧ ∀ σ ∈ Ab, σ v = v} ×
      {e : Fin 512 // ∀ σ ∈ Ab, eAct u σ e = e} := fun x =>
    (⟨⟨cV x, h.cV_lt x x.2.2⟩, by
        refine ⟨?_, fun σ hσ => ?_⟩
        · show qOf u (cV x) = 0
          rw [← (h.sq x x.2.2).2, hsq x x.2.1, h.cE_one]
        · obtain ⟨b, hbA, hb, rfl⟩ := hmemAb.1 hσ
          apply Fin.ext
          rw [h.ρV_apply]
          show h.actV b (cV x) = cV x
          rw [← h.cV_conj hb x.2.2, hcomm b hbA x x.2.1, mul_inv_cancel_right]⟩,
      ⟨⟨cE ((ℓ (cV x))⁻¹ * x), h.cE_lt _ (hEmem x x.2).1⟩, fun σ hσ => by
        obtain ⟨b, hbA, hb, rfl⟩ := hmemAb.1 hσ
        rw [h.eAct_ρV]
        show h.actE b (cE ((ℓ (cV x))⁻¹ * x)) = cE ((ℓ (cV x))⁻¹ * x)
        rw [← h.cE_conj (hEmem x x.2).1, hcomm b hbA _ (hEmem x x.2).2, mul_inv_cancel_right]⟩)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have h1 : cV x = cV y := congrArg (fun p => (p.1.1 : ℕ)) hxy
    have h2 : cE ((ℓ (cV x))⁻¹ * x) = cE ((ℓ (cV y))⁻¹ * y) :=
      congrArg (fun p => (p.2.1 : ℕ)) hxy
    rw [← h1] at h2
    have h3 := h.cE_injOn (hEmem x x.2).1 (by rw [h1]; exact (hEmem y y.2).1) h2
    exact Subtype.ext (mul_left_cancel h3)
  have hle := Nat.card_le_card_of_injective Φ hΦ
  rw [Nat.card_prod] at hle
  rw [hcardA]
  calc Nat.card (A ⊓ Jh : Subgroup G) * Nat.card Ab
      ≤ Nat.card {v : Fin 64 // qOf u v = 0 ∧ ∀ σ ∈ Ab, σ v = v} *
          Nat.card {e : Fin 512 // ∀ σ ∈ Ab, eAct u σ e = e} * Nat.card Ab :=
        Nat.mul_le_mul_right _ hle
    _ = Nat.card Ab * Nat.card {e : Fin 512 // ∀ σ ∈ Ab, eAct u σ e = e} *
          Nat.card {v : Fin 64 // qOf u v = 0 ∧ ∀ σ ∈ Ab, σ v = v} := by ring
    _ < 2 ^ (if u then 9 else 12) := hbound

end S

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
