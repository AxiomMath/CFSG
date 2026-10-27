module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

theorem sz32_graph_core {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {T Z H : Subgroup G} {t : G}
    (hTel : IsElemAbelian p T) (hTcard : Nat.card T = p ^ 2) (hZT : Z ⊓ T ≠ ⊥)
    (hHT : H ≤ Subgroup.normalizer (T : Set G))
    (hmoves : ∀ s ∈ T, s ≠ 1 → ∃ h ∈ H, h * s * h⁻¹ ∉ Subgroup.zpowers s)
    (ht : t ∈ T) (ht1 : t ≠ 1) (hid : ∀ h ∈ H, h * t * h⁻¹ * t⁻¹ ∈ Z) : T ≤ Z := by
  by_contra hnot
  have hp : p.Prime := Fact.out
  haveI hTfin : Finite T :=
    Nat.finite_of_card_ne_zero (by rw [hTcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    have := hTel.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : T) ⟨b, hb⟩)
  have hconj : ∀ h ∈ H, ∀ s ∈ T, h * s * h⁻¹ ∈ T := fun h hh s hs =>
    (Subgroup.mem_normalizer_iff.1 (hHT hh) s).1 hs
  have hcases : ∀ A : Subgroup G, A ≤ T → A = ⊥ ∨ Nat.card A = p ∨ Nat.card A = p ^ 2 := by
    intro A hAT
    obtain ⟨i, hi, hAi⟩ := (Nat.dvd_prime_pow hp).1 (hTcard ▸ Subgroup.card_dvd_of_le hAT)
    interval_cases i
    · left
      exact Subgroup.card_eq_one.1 (by simpa using hAi)
    · right; left
      simpa using hAi
    · right; right
      exact hAi
  have hline : ∀ A : Subgroup G, A ≤ T → Nat.card A = p → ∀ s ∈ A, s ≠ 1 →
      A = Subgroup.zpowers s := by
    intro A hAT hAcard s hsA hs1
    have hord : orderOf s = p := orderOf_eq_prime (hTel.2 s (hAT hsA)) hs1
    haveI : Finite A :=
      Finite.of_injective (Subgroup.inclusion hAT) (Subgroup.inclusion_injective hAT)
    refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hsA) ?_).symm
    rw [Nat.card_zpowers, hord, hAcard]
  have hWT : Z ⊓ T ≤ T := inf_le_right
  have hWcard : Nat.card (Z ⊓ T : Subgroup G) = p := by
    rcases hcases _ hWT with h | h | h
    · exact absurd h hZT
    · exact h
    · exfalso
      apply hnot
      have hWeq : Z ⊓ T = T := Subgroup.eq_of_le_of_card_ge hWT (hTcard.trans h.symm).le
      intro x hx
      have hxW : x ∈ Z ⊓ T := by rw [hWeq]; exact hx
      exact (Subgroup.mem_inf.1 hxW).1
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G,
      ∀ s, s ∈ D ↔ s ∈ T ∧ ∀ h ∈ H, h * s * h⁻¹ * s⁻¹ ∈ Z ⊓ T := by
    refine ⟨{ carrier := {s | s ∈ T ∧ ∀ h ∈ H, h * s * h⁻¹ * s⁻¹ ∈ Z ⊓ T}
              one_mem' := ?one, mul_mem' := ?mul, inv_mem' := ?inv }, fun s => Iff.rfl⟩
    case one =>
      refine ⟨one_mem T, fun h _ => ?_⟩
      simpa using one_mem (Z ⊓ T)
    case mul =>
      rintro a b ⟨haT, ha⟩ ⟨hbT, hb⟩
      refine ⟨mul_mem haT hbT, fun h hh => ?_⟩
      have hx : h * b * h⁻¹ ∈ T := hconj h hh b hbT
      have e1 : a⁻¹ * (h * b * h⁻¹) = (h * b * h⁻¹) * a⁻¹ := hcomm _ (inv_mem haT) _ hx
      have e2 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := hcomm _ (inv_mem haT) _ (inv_mem hbT)
      have key : h * (a * b) * h⁻¹ * (a * b)⁻¹ =
          (h * a * h⁻¹ * a⁻¹) * (h * b * h⁻¹ * b⁻¹) := by
        calc h * (a * b) * h⁻¹ * (a * b)⁻¹
            = (h * a * h⁻¹) * (h * b * h⁻¹) * (b⁻¹ * a⁻¹) := by group
          _ = (h * a * h⁻¹) * (h * b * h⁻¹) * (a⁻¹ * b⁻¹) := by rw [e2]
          _ = (h * a * h⁻¹) * ((h * b * h⁻¹) * a⁻¹) * b⁻¹ := by group
          _ = (h * a * h⁻¹) * (a⁻¹ * (h * b * h⁻¹)) * b⁻¹ := by rw [e1]
          _ = (h * a * h⁻¹ * a⁻¹) * (h * b * h⁻¹ * b⁻¹) := by group
      rw [key]
      exact mul_mem (ha h hh) (hb h hh)
    case inv =>
      rintro a ⟨haT, ha⟩
      refine ⟨inv_mem haT, fun h hh => ?_⟩
      have hx : h * a⁻¹ * h⁻¹ ∈ T := hconj h hh a⁻¹ (inv_mem haT)
      have e : a * (h * a⁻¹ * h⁻¹) = (h * a⁻¹ * h⁻¹) * a := hcomm _ haT _ hx
      have key : h * a⁻¹ * h⁻¹ * a⁻¹⁻¹ = (h * a * h⁻¹ * a⁻¹)⁻¹ := by
        calc h * a⁻¹ * h⁻¹ * a⁻¹⁻¹ = (h * a⁻¹ * h⁻¹) * a := by group
          _ = a * (h * a⁻¹ * h⁻¹) := e.symm
          _ = (h * a * h⁻¹ * a⁻¹)⁻¹ := by group
      rw [key]
      exact inv_mem (ha h hh)
  have hDT : D ≤ T := fun s hs => ((hD s).1 hs).1
  have htD : t ∈ D := by
    exact (hD t).2 ⟨ht, fun h hh =>
      Subgroup.mem_inf.2 ⟨hid h hh, mul_mem (hconj h hh t ht) (inv_mem ht)⟩⟩
  have hconjD : ∀ h' ∈ H, h' * t * h'⁻¹ ∈ D := by
    intro h' hh'
    refine (hD _).2 ⟨hconj h' hh' t ht, fun h hh => ?_⟩
    have h1 := ((hD t).1 htD).2 (h * h') (mul_mem hh hh')
    have h2 := ((hD t).1 htD).2 h' hh'
    have key : h * (h' * t * h'⁻¹) * h⁻¹ * (h' * t * h'⁻¹)⁻¹ =
        ((h * h') * t * (h * h')⁻¹ * t⁻¹) * (h' * t * h'⁻¹ * t⁻¹)⁻¹ := by group
    rw [key]
    exact mul_mem h1 (inv_mem h2)
  obtain ⟨E, hE⟩ : ∃ E : Subgroup G,
      E = Subgroup.closure {s | ∃ h ∈ H, s = h * t * h⁻¹} := ⟨_, rfl⟩
  have hED : E ≤ D := by
    rw [hE, Subgroup.closure_le]
    rintro s ⟨h, hh, rfl⟩
    exact hconjD h hh
  have htE : t ∈ E := by
    rw [hE]
    exact Subgroup.subset_closure ⟨1, one_mem H, by simp⟩
  have hEinv : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E := by
    intro h hh e he
    rw [hE] at he ⊢
    induction he using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨h₁, hh₁, rfl⟩ := hx
        exact Subgroup.subset_closure ⟨h * h₁, mul_mem hh hh₁, by group⟩
    | one => simpa using one_mem _
    | mul x y _ _ hx hy =>
        have key : h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) := by group
        rw [key]
        exact mul_mem hx hy
    | inv x _ hx =>
        have key : h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ := by group
        rw [key]
        exact inv_mem hx
  have hET : E ≤ T := hED.trans hDT
  have hEeq : E = T := by
    rcases hcases E hET with h | h | h
    · exfalso
      rw [h] at htE
      exact ht1 (Subgroup.mem_bot.1 htE)
    · exfalso
      have hEline : E = Subgroup.zpowers t := hline E hET h t htE ht1
      obtain ⟨h', hh', hnm⟩ := hmoves t ht ht1
      apply hnm
      rw [← hEline]
      exact hEinv h' hh' t htE
    · exact Subgroup.eq_of_le_of_card_ge hET (hTcard.trans h.symm).le
  have hTD : T ≤ D := hEeq ▸ hED
  obtain ⟨⟨s, hsW⟩, hs1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZT
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have hsT : s ∈ T := (Subgroup.mem_inf.1 hsW).2
  have hWeq : Z ⊓ T = Subgroup.zpowers s := hline _ hWT hWcard s hsW hs1
  obtain ⟨h, hh, hnm⟩ := hmoves s hsT hs1
  apply hnm
  rw [← hWeq]
  have hc := ((hD s).1 (hTD hsT)).2 h hh
  have key : h * s * h⁻¹ = (h * s * h⁻¹ * s⁻¹) * s := by group
  rw [key]
  exact mul_mem hc hsW

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
