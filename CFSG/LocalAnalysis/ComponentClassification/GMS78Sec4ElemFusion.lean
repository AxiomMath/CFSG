module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4ElemDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Basic

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G]

namespace Sec4Elem

variable {L T U₁ : Subgroup G} {q : ℕ}

theorem conj_mem_A_of_mem_V (h313 : Lemma313 L T q)
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁)
    {u : G} (hu : u ∈ U₁) {g : G} (hv : g * u * g⁻¹ ∈ gmsV L T) : g * u * g⁻¹ ∈ gmsA L T := by
  by_contra hvA
  obtain ⟨Q, ⟨⟨x, rfl⟩, -⟩, hvQ, hv1⟩ := (h313.cover _ hv).mp hvA
  rw [mem_rightConjugate_iff] at hvQ
  have ht1 : x * (g * u * g⁻¹) * x⁻¹ ≠ 1 := by
    intro h1
    apply hv1
    calc g * u * g⁻¹ = x⁻¹ * (x * (g * u * g⁻¹) * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  apply hnf _ hvQ ht1 (x * g)⁻¹
  have : (x * g)⁻¹ * (x * (g * u * g⁻¹) * x⁻¹) * (x * g)⁻¹⁻¹ = u := by group
  rw [this]
  exact hu

theorem conj_mem_of_mem_W (hE : Sec4Elem L T U₁ q) (h313 : Lemma313 L T q)
    (hT₀ : IsElemAbelian 2 (T ⊓ centralizer (L : Set G)))
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁)
    {u : G} (hu : u ∈ U₁) {g : G} (hW : g * u * g⁻¹ ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G))) :
    g * u * g⁻¹ ∈ U₁ := by
  have hsq : g * u * g⁻¹ * (g * u * g⁻¹) = 1 := by
    calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hE.mul_self hu]; group
  rcases hE.mem_or_mem hT₀ hW hsq with h1 | h1
  · exact h1
  · exact hE.A_le (conj_mem_A_of_mem_V h313 hnf hu h1)

theorem rightConjugate_le_V (hE : Sec4Elem L T U₁ q) (hT₀ : IsElemAbelian 2 (T ⊓ centralizer
    (L : Set G))) (hT₀1 : T ⊓ centralizer (L : Set G) ≠ ⊥)
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁) {x : G}
    (hW : rightConjugate (T ⊓ centralizer (L : Set G)) x ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G))) :
    rightConjugate (T ⊓ centralizer (L : Set G)) x ≤ gmsV L T := by
  have h2 : ∀ y ∈ rightConjugate (T ⊓ centralizer (L : Set G)) x, y * y = 1 := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have h1 : x * y * x⁻¹ * (x * y * x⁻¹) = 1 := by rw [← sq]; exact hT₀.2 _ hy
    calc y * y = x⁻¹ * (x * y * x⁻¹ * (x * y * x⁻¹)) * x := by group
      _ = 1 := by rw [h1]; group
  rcases hE.le_or_le hT₀ hW h2 with hU | hV
  · exfalso
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT₀1
    have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
    apply hnf t ht ht1' x⁻¹
    apply hU
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using ht
  · exact hV

theorem normalizer_W_le (hE : Sec4Elem L T U₁ q) (h313 : Lemma313 L T q)
    (hT₀ : IsElemAbelian 2 (T ⊓ centralizer (L : Set G))) (hT₀1 : T ⊓ centralizer (L : Set G) ≠ ⊥)
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁) :
    normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G) ≤
      normalizer (gmsV L T : Set G) := by
  set W := U₁ ⊔ (T ⊓ centralizer (L : Set G)) with hWdef
  have hout : ∀ n ∈ normalizer (W : Set G), ∀ v ∈ gmsV L T, v ∉ gmsA L T →
      n * v * n⁻¹ ∈ gmsV L T := by
    intro n hn v hv hvA
    obtain ⟨Q, ⟨⟨x, rfl⟩, hQV⟩, hvQ, -⟩ := (h313.cover v hv).mp hvA
    have hQ' : rightConjugate (T ⊓ centralizer (L : Set G)) (x * n⁻¹) ≤ W := by
      rw [← rightConjugate_mul]
      calc rightConjugate (rightConjugate (T ⊓ centralizer (L : Set G)) x) n⁻¹
          ≤ rightConjugate W n⁻¹ := map_mono (hQV.trans hE.V_le)
        _ = W := (rightConjugate_eq_self_iff _ _).mpr (inv_mem hn)
    have h1 := rightConjugate_le_V hE hT₀ hT₀1 hnf hQ'
    apply h1
    rw [mem_rightConjugate_iff]
    rw [mem_rightConjugate_iff] at hvQ
    have : x * n⁻¹ * (n * v * n⁻¹) * (x * n⁻¹)⁻¹ = x * v * x⁻¹ := by group
    rw [this]
    exact hvQ
  have hconj : ∀ n ∈ normalizer (W : Set G), ∀ v ∈ gmsV L T, n * v * n⁻¹ ∈ gmsV L T := by
    intro n hn v hv
    by_cases hvA : v ∉ gmsA L T
    · exact hout n hn v hv hvA
    push Not at hvA
    obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hT₀1
    have ht1' : t ≠ 1 := fun h1 => ht1 (Subtype.ext h1)
    have hbot := h313.inf_gmsA_eq_bot Sec3.mem_delta_T₀
    have htA : t ∉ gmsA L T := fun htA => by
      have : t ∈ (T ⊓ centralizer (L : Set G)) ⊓ gmsA L T := mem_inf.mpr ⟨ht, htA⟩
      rw [hbot, mem_bot] at this
      exact ht1' this
    have hvtA : v * t ∉ gmsA L T := fun h' => htA (by simpa using mul_mem (inv_mem hvA) h')
    have h1 := hout n hn (v * t) (mul_mem hv (mem_sup_right ht)) hvtA
    have h2 := hout n hn t (mem_sup_right ht) htA
    have : n * v * n⁻¹ = n * (v * t) * n⁻¹ * (n * t * n⁻¹)⁻¹ := by group
    rw [this]
    exact mul_mem h1 (inv_mem h2)
  intro n hn
  exact mem_normalizer_of_conj_mem (hconj n hn)
    (fun v hv => by simpa using hconj n⁻¹ (inv_mem hn) v hv)

theorem mem_of_mem_normalizer_W [Finite G] (hE : Sec4Elem L T U₁ q) (h313 : Lemma313 L T q)
    (hT₀ : IsElemAbelian 2 (T ⊓ centralizer (L : Set G))) (hT₀1 : T ⊓ centralizer (L : Set G) ≠ ⊥)
    (hnf : ∀ t ∈ T ⊓ centralizer (L : Set G), t ≠ 1 → ∀ g : G, g * t * g⁻¹ ∉ U₁)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hS₀S : U₁ ⊔ T ≤ S) {n : G} (hnS : n ∈ S)
    (hnW : n ∈ normalizer ((U₁ ⊔ (T ⊓ centralizer (L : Set G)) : Subgroup G) : Set G)) :
    n ∈ U₁ ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnV := normalizer_W_le hE h313 hT₀ hT₀1 hnf hnW
  have hP : IsPGroup 2 ((U₁ ⊔ T) ⊔ zpowers n : Subgroup G) :=
    hS.to_le (sup_le hS₀S (zpowers_le.mpr hnS))
  have heq := hE.sylow.eq_of_le le_sup_left (sup_le hE.sylow.le (zpowers_le.mpr hnV)) hP
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

end Sec4Elem

end CFSG.ComponentClassification.GMS78
