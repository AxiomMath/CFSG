module

public import CFSG.FeitThompson.Local.PLengthOneNormalSeries

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem natCard_prod_subgroup {N : Type*} [Group N] (H : Subgroup X) (K : Subgroup N) :
    Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (H.prodEquiv K).toEquiv, Nat.card_prod]

omit [Finite X] in
theorem index_inf_dvd_mul_index {H K : Subgroup X} [H.Normal] :
    (H ⊓ K).index ∣ H.index * K.index := by
  rw [← Subgroup.relIndex_mul_index (inf_le_right : H ⊓ K ≤ K), Subgroup.inf_relIndex_right]
  exact mul_dvd_mul_right (Subgroup.relIndex_dvd_index_of_normal _ _) _

variable [Fact p.Prime]

theorem hasPLengthLeOne_of_ker_inf_eq_bot {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂]
    (q₁ : X →* Y₁) (q₂ : X →* Y₂) (hq : q₁.ker ⊓ q₂.ker = ⊥)
    {E₁ T₁ : Subgroup Y₁} {E₂ T₂ : Subgroup Y₂} [E₁.Normal] [T₁.Normal] [E₂.Normal] [T₂.Normal]
    (hET₁ : E₁ ≤ T₁) (hET₂ : E₂ ≤ T₂)
    (hE₁card : ¬ p ∣ Nat.card E₁) (hE₂card : ¬ p ∣ Nat.card E₂)
    {n₁ n₂ : ℕ} (hn₁ : Nat.card (↥T₁ ⧸ E₁.subgroupOf T₁) = p ^ n₁)
    (hn₂ : Nat.card (↥T₂ ⧸ E₂.subgroupOf T₂) = p ^ n₂)
    (hT₁idx : ¬ p ∣ (T₁.comap q₁).index) (hT₂idx : ¬ p ∣ (T₂.comap q₂).index) :
    HasPLengthLeOne p X := by
  have hp : p.Prime := Fact.out
  set A : Subgroup X := E₁.comap q₁ ⊓ E₂.comap q₂ with hA
  set B : Subgroup X := T₁.comap q₁ ⊓ T₂.comap q₂ with hB
  set f : X →* (Y₁ ⧸ E₁) × (Y₂ ⧸ E₂) :=
    ((QuotientGroup.mk' E₁).comp q₁).prod ((QuotientGroup.mk' E₂).comp q₂) with hf
  have hkerf : f.ker = A := by
    rw [hf, MonoidHom.ker_prod, ← MonoidHom.comap_ker, ← MonoidHom.comap_ker,
      QuotientGroup.ker_mk', QuotientGroup.ker_mk', hA]
  set φ : X →* Y₁ × Y₂ := q₁.prod q₂ with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφ, MonoidHom.ker_prod, hq]
  have hAB : A ≤ B := inf_le_inf (Subgroup.comap_mono hET₁) (Subgroup.comap_mono hET₂)
  refine hasPLengthLeOne_iff_exists_normal.2 ⟨A, B, inferInstance, inferInstance, hAB, ?_, ?_, ?_⟩
  ·
    have hmap : A.map φ ≤ E₁.prod E₂ := by
      rw [Subgroup.map_le_iff_le_comap]
      exact fun x hx => ⟨hx.1, hx.2⟩
    have hcard : Nat.card A ∣ Nat.card E₁ * Nat.card E₂ := by
      rw [← natCard_prod_subgroup, ← Subgroup.card_map_of_injective (K := A) hφinj]
      exact Subgroup.card_dvd_of_le hmap
    exact fun hdvd => (hp.dvd_mul.1 (hdvd.trans hcard)).elim hE₁card hE₂card
  ·
    have hmap : B.map f ≤
        (T₁.map (QuotientGroup.mk' E₁)).prod (T₂.map (QuotientGroup.mk' E₂)) := by
      rw [Subgroup.map_le_iff_le_comap]
      exact fun x hx => ⟨Subgroup.mem_map_of_mem _ hx.1, Subgroup.mem_map_of_mem _ hx.2⟩
    have hc₁ : Nat.card (T₁.map (QuotientGroup.mk' E₁)) = p ^ n₁ := by
      rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← natCard_quotient_subgroupOf, hn₁]
    have hc₂ : Nat.card (T₂.map (QuotientGroup.mk' E₂)) = p ^ n₂ := by
      rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← natCard_quotient_subgroupOf, hn₂]
    have hdvd : Nat.card (↥B ⧸ A.subgroupOf B) ∣ p ^ (n₁ + n₂) := by
      rw [natCard_quotient_subgroupOf, ← hkerf, Subgroup.relIndex_ker, pow_add, ← hc₁, ← hc₂,
        ← natCard_prod_subgroup]
      exact Subgroup.card_dvd_of_le hmap
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact ⟨k, hk⟩
  ·
    intro hdvd
    exact (hp.dvd_mul.1 (hdvd.trans index_inf_dvd_mul_index)).elim hT₁idx hT₂idx

theorem hasPLengthLeOne_of_inf_eq_bot {D₁ D₂ : Subgroup X} [D₁.Normal] [D₂.Normal]
    (hD : D₁ ⊓ D₂ = ⊥) (h₁ : HasPLengthLeOne p (X ⧸ D₁)) (h₂ : HasPLengthLeOne p (X ⧸ D₂)) :
    HasPLengthLeOne p X := by
  obtain ⟨E₁, T₁, hE₁, hT₁, hET₁, hE₁card, ⟨n₁, hn₁⟩, hT₁idx⟩ :=
    hasPLengthLeOne_iff_exists_normal.1 h₁
  obtain ⟨E₂, T₂, hE₂, hT₂, hET₂, hE₂card, ⟨n₂, hn₂⟩, hT₂idx⟩ :=
    hasPLengthLeOne_iff_exists_normal.1 h₂
  have := hE₁; have := hE₂; have := hT₁; have := hT₂
  refine hasPLengthLeOne_of_ker_inf_eq_bot (QuotientGroup.mk' D₁) (QuotientGroup.mk' D₂) ?_
    hET₁ hET₂ hE₁card hE₂card hn₁ hn₂ ?_ ?_
  · rwa [QuotientGroup.ker_mk', QuotientGroup.ker_mk']
  · rwa [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · rwa [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem not_dvd_index_pComplPCore_of_inf_eq_bot {D₁ D₂ : Subgroup X} [D₁.Normal] [D₂.Normal]
    (hD : D₁ ⊓ D₂ = ⊥) (h₁ : ¬ p ∣ (pComplPCore p (X ⧸ D₁)).index)
    (h₂ : ¬ p ∣ (pComplPCore p (X ⧸ D₂)).index) :
    ¬ p ∣ (pComplPCore p X).index :=
  hasPLengthLeOne_iff_not_dvd_index_pComplPCore.1 (hasPLengthLeOne_of_inf_eq_bot hD
    (hasPLengthLeOne_iff_not_dvd_index_pComplPCore.2 h₁)
    (hasPLengthLeOne_iff_not_dvd_index_pComplPCore.2 h₂))

end

end CFSG.FeitThompson
