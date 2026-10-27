module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {Γ : Type} [Group Γ]

@[expose] def A6CPairFacts (Γ : Type) [Group Γ] (P : Γ → Prop) (kc bound : ℕ) : Prop :=
  ∃ g0 n : Γ, g0 ^ 5 = 1 ∧ g0 ≠ 1 ∧ n * g0 * n⁻¹ = g0 ^ 2 ∧
    Nat.card (centralizer ({g0} : Set Γ)) = kc ∧
    ∀ a : Γ, P a → a * a = 1 → (a * g0) ^ 4 = 1 → (g0 * a * g0) ^ 5 = 1 →
      Nat.card (centralizer ({a, g0} : Set Γ)) ≤ bound ∧
        ∀ c ∈ centralizer ({a, g0} : Set Γ), c * c = 1

theorem a6c_card_centralizer_of_orderOf [Finite Γ] {P : Γ → Prop} {kc bound : ℕ}
    (hΓ : ¬ 25 ∣ Nat.card Γ) (F : A6CPairFacts Γ P kc bound) {ξ : Γ} (hξ : orderOf ξ = 5) :
    Nat.card (centralizer ({ξ} : Set Γ)) = kc := by
  unfold A6CPairFacts at F
  obtain ⟨g0, n, hg0, hg1, hn, hkc, _⟩ := F
  have hξ5 : ξ ^ 5 = 1 := by
    rw [← hξ]
    exact pow_orderOf_eq_one ξ
  have hξ1 : ξ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hξ
    omega
  rw [a6c_card_centralizer_eq hΓ hg0 hg1 hn hξ5 hξ1, hkc]

theorem a6c_centralizer_A6 [Finite Γ] {P : Γ → Prop} {kc bound : ℕ}
    (hP : ∀ a δ : Γ, P a → P (δ * a * δ⁻¹)) (hΓ : ¬ 25 ∣ Nat.card Γ)
    (F : A6CPairFacts Γ P kc bound) (A : Subgroup Γ) (e : A ≃* alternatingGroup (Fin 6))
    (hA : ∀ a ∈ A, a * a = 1 → a ≠ 1 → P a) :
    Nat.card (centralizer (A : Set Γ)) ≤ bound ∧ ∀ c ∈ centralizer (A : Set Γ), c * c = 1 := by
  unfold A6CPairFacts at F
  obtain ⟨g0, n, hg0, hg1, hn, _, hF⟩ := F
  obtain ⟨a, ha, x, hx, haa, ha1, hx5, hx1, hax4, hxax5⟩ := a6c_exists_std_pair e
  obtain ⟨δ, hδ⟩ := a6c_exists_conj_g0 hΓ hg0 hg1 hn hx5 hx1
  set a' : Γ := δ * a * δ⁻¹ with ha'def
  have hPa : P a := hA a ha haa ha1
  have hPa' : P a' := by simpa [ha'def] using hP a δ hPa
  have ha'a' : a' * a' = 1 := by
    have h : a' * a' = δ * (a * a) * δ⁻¹ := by rw [ha'def]; group
    rw [h, haa]; group
  have ha'g0 : (a' * g0) ^ 4 = 1 := by
    have h : a' * g0 = δ * (a * x) * δ⁻¹ := by rw [ha'def, ← hδ]; group
    rw [h, conj_pow, hax4]; group
  have hg0a'g0 : (g0 * a' * g0) ^ 5 = 1 := by
    have h : g0 * a' * g0 = δ * (x * a * x) * δ⁻¹ := by rw [ha'def, ← hδ]; group
    rw [h, conj_pow, hxax5]; group
  obtain ⟨hbound, hsquare⟩ := hF a' hPa' ha'a' ha'g0 hg0a'g0
  have hmem : ∀ c : Γ, c ∈ centralizer (A : Set Γ) →
      δ * c * δ⁻¹ ∈ centralizer ({a', g0} : Set Γ) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    have hca : a * c = c * a := (Subgroup.mem_centralizer_iff).mp hc a ha
    have hcx : x * c = c * x := (Subgroup.mem_centralizer_iff).mp hc x hx
    rcases hh with rfl | rfl
    · rw [ha'def]
      have e1 : δ * a * δ⁻¹ * (δ * c * δ⁻¹) = δ * (a * c) * δ⁻¹ := by group
      have e2 : δ * c * δ⁻¹ * (δ * a * δ⁻¹) = δ * (c * a) * δ⁻¹ := by group
      rw [e1, e2, hca]
    · rw [← hδ]
      have e1 : (δ * x * δ⁻¹) * (δ * c * δ⁻¹) = δ * (x * c) * δ⁻¹ := by group
      have e2 : δ * c * δ⁻¹ * (δ * x * δ⁻¹) = δ * (c * x) * δ⁻¹ := by group
      rw [e1, e2, hcx]
  constructor
  · refine le_trans ?_ hbound
    refine Nat.card_le_card_of_injective
      (fun c : centralizer (A : Set Γ) =>
        (⟨δ * (c : Γ) * δ⁻¹, hmem c c.2⟩ : centralizer ({a', g0} : Set Γ))) ?_
    intro c d hcd
    apply Subtype.ext
    have hval : δ * (c : Γ) * δ⁻¹ = δ * (d : Γ) * δ⁻¹ := congrArg Subtype.val hcd
    calc (c : Γ) = δ⁻¹ * (δ * (c : Γ) * δ⁻¹) * δ := by group
      _ = δ⁻¹ * (δ * (d : Γ) * δ⁻¹) * δ := by rw [hval]
      _ = (d : Γ) := by group
  · intro c hc
    have hs := hsquare (δ * c * δ⁻¹) (hmem c hc)
    calc c * c = δ⁻¹ * ((δ * c * δ⁻¹) * (δ * c * δ⁻¹)) * δ := by group
      _ = δ⁻¹ * 1 * δ := by rw [hs]
      _ = 1 := by group

end CFSG.OddStandard.SmallF3.Omega
