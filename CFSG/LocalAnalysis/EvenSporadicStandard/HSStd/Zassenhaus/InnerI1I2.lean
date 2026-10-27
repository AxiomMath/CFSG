module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFusionAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2HS

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem hsInner_I1_I2
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsSporadic L .HS) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) :
    ∃ E : Subgroup G, E ≤ L ∧ z ∈ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
      (∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
        φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L)) ∧
      (∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e) ∧
      (∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), m * t * m⁻¹ = t * e) ∧
      ∃ W : Subgroup G, W = I2.Opp2 (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) ∧
        W ≤ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G) ∧
        (∀ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), ∀ w ∈ W, m * w * m⁻¹ ∈ W) ∧
        E ≤ W ∧ t ∉ W ∧ IsElemAbelian 2 W ∧ Nat.card W = 256 ∧
        Nat.card (normalizer ((zpowers t ⊔ E : Subgroup G) : Set G)) = 16 * 23040 ∧
        centralizer ((zpowers t ⊔ E : Subgroup G) : Set G) = zpowers t ⊔ E := by
  obtain ⟨E, hEL, hzE, hEab, hE16, hφ, htr, hfus⟩ := hsInnerFusion_at hL htL ht2 hin hf
  have hEconj : ∀ e ∈ E, e ≠ 1 → ∃ k ∈ L, k * z * k⁻¹ = e := fun e he he1 =>
    let ⟨a, ha, h⟩ := htr e he he1; ⟨a, ha.2, h⟩
  obtain ⟨W, hWN, hWn, hEW, htW, hWab, hW, hN, hC, hWO⟩ :=
    I2.hsInner_I2 hL htL ht2 hin hf hEL hzE hEab hE16 hEconj hfus
  exact ⟨E, hEL, hzE, hEab, hE16, hφ, htr, hfus, W, hWO, hWN, hWn, hEW, htW, hWab, hW, hN, hC⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
