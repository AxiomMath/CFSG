module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open

variable {G : Type} [Group G]

structure IsE27InvConfig (V W₁ W₂ W₃ : Subgroup G) (t₁ t₂ t₃ : G) : Prop where
  card₁ : Nat.card W₁ = 3
  card₂ : Nat.card W₂ = 3
  card₃ : Nat.card W₃ = 3
  join : V = W₁ ⊔ W₂ ⊔ W₃
  elem : IsElemAbelian 3 V
  card : Nat.card V = 27
  inv₁ : ∀ w ∈ W₁, t₁ * w * t₁⁻¹ = w⁻¹
  inv₂ : ∀ w ∈ W₂, t₂ * w * t₂⁻¹ = w⁻¹
  inv₃ : ∀ w ∈ W₃, t₃ * w * t₃⁻¹ = w⁻¹
  comm₁ : ∀ w ∈ W₂ ⊔ W₃, t₁ * w = w * t₁
  comm₂ : ∀ w ∈ W₁ ⊔ W₃, t₂ * w = w * t₂
  comm₃ : ∀ w ∈ W₁ ⊔ W₂, t₃ * w = w * t₃

private theorem IsE27InvConfig.commute_facts {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    (∀ a ∈ W₁, ∀ b ∈ W₂, Commute a b) ∧ (∀ a ∈ W₁, ∀ c ∈ W₃, Commute a c) ∧
      (∀ b ∈ W₂, ∀ c ∈ W₃, Commute b c) ∧
      (∀ a ∈ W₁ ⊔ W₂, ∀ c ∈ W₃, Commute a c) := by
  haveI : IsMulCommutative V := hc.elem.1
  have hW₁V : W₁ ≤ V := by
    rw [hc.join]
    exact le_sup_left.trans le_sup_left
  have hW₂V : W₂ ≤ V := by
    rw [hc.join]
    exact le_sup_right.trans le_sup_left
  have hW₃V : W₃ ≤ V := by
    rw [hc.join]
    exact le_sup_right
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, Commute a b := fun a ha b hb =>
    (commute_iff_eq a b).mpr (setLike_mul_comm ha hb)
  have h₁₂ : ∀ a ∈ W₁, ∀ b ∈ W₂, Commute a b :=
    fun a ha b hb => hcomm a (hW₁V ha) b (hW₂V hb)
  have h₁₃ : ∀ a ∈ W₁, ∀ c ∈ W₃, Commute a c :=
    fun a ha c hc₃ => hcomm a (hW₁V ha) c (hW₃V hc₃)
  have h₂₃ : ∀ b ∈ W₂, ∀ c ∈ W₃, Commute b c :=
    fun b hb c hc₃ => hcomm b (hW₂V hb) c (hW₃V hc₃)
  have hcent : W₃ ≤ Subgroup.centralizer ((W₁ ⊔ W₂ : Subgroup G) : Set G) :=
    CFSG.le_centralizer_sup_of_commute_both h₁₂
      (fun a ha b hb => (h₁₃ b hb a ha).symm) (fun a ha b hb => (h₂₃ b hb a ha).symm)
  have hcomm₃ : ∀ a ∈ W₁ ⊔ W₂, ∀ c ∈ W₃, Commute a c := by
    intro a ha c hc₃
    exact Subgroup.mem_centralizer_iff.mp (hcent hc₃) a ha
  exact ⟨h₁₂, h₁₃, h₂₃, hcomm₃⟩

private theorem IsE27InvConfig.exists_eq_mul_mul_of_mem
    {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) {v : G} (hv : v ∈ V) :
    ∃ w₁ ∈ W₁, ∃ w₂ ∈ W₂, ∃ w₃ ∈ W₃, v = w₁ * w₂ * w₃ := by
  have hcf := hc.commute_facts
  obtain ⟨y, hy, w₃, hw₃, hvw⟩ :=
    (CFSG.mem_sup_of_commute hcf.2.2.2).mp (hc.join ▸ hv)
  obtain ⟨w₁, hw₁, w₂, hw₂, hyw⟩ := (CFSG.mem_sup_of_commute hcf.1).mp hy
  exact ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, by rw [← hvw, ← hyw]⟩

private theorem le_of_conj_of_mem {D W : Subgroup G} {t v a r : G}
    (hcard : Nat.card W = 3) (ha : a ∈ W) (ha1 : a ≠ 1)
    (hv : v = a * r) (hinv : t * a * t⁻¹ = a⁻¹) (hcent : t * r * t⁻¹ = r)
    (hvD : v ∈ D) (htvD : t * v * t⁻¹ ∈ D) : W ≤ D := by
  have hconj : t * v * t⁻¹ = a⁻¹ * r := by
    rw [hv]
    calc t * (a * r) * t⁻¹ = (t * a * t⁻¹) * (t * r * t⁻¹) := by group
      _ = a⁻¹ * r := by rw [hinv, hcent]
  have hsq : a ^ 2 ∈ D := by
    have hkey : v * (t * v * t⁻¹)⁻¹ = a ^ 2 := by
      rw [hconj, hv, pow_two]
      group
    have hmem : v * (t * v * t⁻¹)⁻¹ ∈ D := D.mul_mem hvD (D.inv_mem htvD)
    rwa [hkey] at hmem
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd : orderOf a ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W ha
  rw [hcard] at hdvd
  have hne1 : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf a = 3 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hpow : a ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hord]
  have hzle : Subgroup.zpowers a ≤ W := Subgroup.zpowers_le.mpr ha
  have hcardz : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hWeq : W = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge hzle (by simp [hcard, hcardz])).symm
  have haD : a ∈ D := by
    have h := D.pow_mem hsq 2
    have heq : (a ^ 2) ^ 2 = a := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hpow, one_mul]
    rwa [heq] at h
  rw [hWeq]
  exact Subgroup.zpowers_le.mpr haD

theorem IsE27InvConfig.exists_le_of_invariant {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) {D : Subgroup G} (hDV : D ≤ V) (hD : D ≠ ⊥)
    (hDt : ∀ t ∈ ({t₁, t₂, t₃} : Set G), ∀ x ∈ D, t * x * t⁻¹ ∈ D) :
    W₁ ≤ D ∨ W₂ ≤ D ∨ W₃ ≤ D := by
  obtain ⟨h₁₂, h₁₃, h₂₃, hcomm₃⟩ := hc.commute_facts
  obtain ⟨v, hvD, hv1⟩ : ∃ v ∈ D, v ≠ 1 := by
    by_contra h
    refine hD ?_
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, w₃, hw₃, hv⟩ := hc.exists_eq_mul_mul_of_mem (hDV hvD)
  have hle₁ : w₁ ≠ 1 → W₁ ≤ D := by
    intro hw₁1
    have hr : t₁ * (w₂ * w₃) * t₁⁻¹ = w₂ * w₃ := by
      rw [hc.comm₁ _ (Subgroup.mul_mem_sup hw₂ hw₃)]; group
    exact le_of_conj_of_mem hc.card₁ hw₁ hw₁1 (by rw [hv]; group)
      (hc.inv₁ w₁ hw₁) hr hvD (hDt t₁ (by simp) v hvD)
  have hle₂ : w₂ ≠ 1 → W₂ ≤ D := by
    intro hw₂1
    have hv₂ : v = w₂ * (w₁ * w₃) := by
      rw [hv, (h₁₂ w₁ hw₁ w₂ hw₂).eq]; group
    have hr : t₂ * (w₁ * w₃) * t₂⁻¹ = w₁ * w₃ := by
      rw [hc.comm₂ _ (Subgroup.mul_mem_sup hw₁ hw₃)]; group
    exact le_of_conj_of_mem hc.card₂ hw₂ hw₂1 hv₂ (hc.inv₂ w₂ hw₂) hr hvD
      (hDt t₂ (by simp) v hvD)
  have hle₃ : w₃ ≠ 1 → W₃ ≤ D := by
    intro hw₃1
    have hv₃ : v = w₃ * (w₁ * w₂) := by
      rw [hv, mul_assoc, (h₂₃ w₂ hw₂ w₃ hw₃).eq, ← mul_assoc, (h₁₃ w₁ hw₁ w₃ hw₃).eq]
      group
    have hr : t₃ * (w₁ * w₂) * t₃⁻¹ = w₁ * w₂ := by
      rw [hc.comm₃ _ (Subgroup.mul_mem_sup hw₁ hw₂)]; group
    exact le_of_conj_of_mem hc.card₃ hw₃ hw₃1 hv₃ (hc.inv₃ w₃ hw₃) hr hvD
      (hDt t₃ (by simp) v hvD)
  by_cases h1 : w₁ = 1
  · by_cases h2 : w₂ = 1
    · exact Or.inr (Or.inr (hle₃ fun h3 => hv1 (by rw [hv, h1, h2, h3]; group)))
    · exact Or.inr (Or.inl (hle₂ h2))
  · exact Or.inl (hle₁ h1)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
