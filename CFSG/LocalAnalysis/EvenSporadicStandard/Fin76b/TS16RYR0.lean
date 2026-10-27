module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RHarada

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open Pointwise

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_sigma' {A : Subgroup G} {σ : G} (hσ2 : σ * σ = 1)
    (hσA : ∀ a ∈ A, σ * a * σ⁻¹ ∈ A) {x : G} (hx : x ∈ A ⊔ zpowers σ) :
    ∃ a ∈ A, x = a ∨ x = a * σ := by
  have hσi : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  have hnorm : σ ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    refine ⟨fun ha => hσA a ha, fun ha => ?_⟩
    have h1 := hσA _ ha
    have h2 : σ * (σ * a * σ⁻¹) * σ⁻¹ = a := by
      calc σ * (σ * a * σ⁻¹) * σ⁻¹ = (σ * σ) * a * (σ⁻¹ * σ⁻¹) := by group
        _ = a := by rw [hσ2, hσi, hσ2]; group
    rwa [h2] at h1
  have hle : zpowers σ ≤ normalizer (A : Set G) := zpowers_le.2 hnorm
  have h := Subgroup.coe_mul_of_right_le_normalizer_left A (zpowers σ) hle
  have hx' : x ∈ ((A : Set G) * (zpowers σ : Set G)) := by
    rw [← h]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  rcases mem_zpowers_sq_eq_one hσ2 hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

theorem sq_comm_sup {S E F : Subgroup G} (hSE : S ≤ centralizer (E : Set G))
    (hS2 : ∀ d ∈ S, d * d ∈ F) (hE2 : ∀ c ∈ E, c * c ∈ F)
    (hSc : ∀ d ∈ S, ∀ d' ∈ S, d * d' * d⁻¹ * d'⁻¹ ∈ F)
    (hEc : ∀ c ∈ E, ∀ c' ∈ E, c * c' * c⁻¹ * c'⁻¹ ∈ F) :
    (∀ r ∈ S ⊔ E, r * r ∈ F) ∧
      ∀ r ∈ S ⊔ E, ∀ r' ∈ S ⊔ E, r * r' * r⁻¹ * r'⁻¹ ∈ F := by
  have hES : E ≤ centralizer (S : Set G) := Subgroup.le_centralizer_iff.2 hSE
  have hmul : ∀ (d : G) (c : G), d ∈ S → c ∈ E → d * c = c * d := fun d c hd hc =>
    (mem_centralizer_iff.1 (hSE hd) c hc).symm
  have key : ∀ (d c d' c' : G), d ∈ S → c ∈ E → d' ∈ S → c' ∈ E →
      (d * c) * (d' * c') * (d * c)⁻¹ * (d' * c')⁻¹ =
        (d * d' * d⁻¹ * d'⁻¹) * (c * c' * c⁻¹ * c'⁻¹) := by
    intro d c d' c' hd hc hd' hc'
    have h1 : (mulHom S E hSE) (⟨d, hd⟩, ⟨c, hc⟩) = d * c := rfl
    have h2 : (mulHom S E hSE) (⟨d', hd'⟩, ⟨c', hc'⟩) = d' * c' := rfl
    have h3 : (mulHom S E hSE) ((⟨d, hd⟩ * ⟨d', hd'⟩ * ⟨d, hd⟩⁻¹ * ⟨d', hd'⟩⁻¹ : ↥S),
        (⟨c, hc⟩ * ⟨c', hc'⟩ * ⟨c, hc⟩⁻¹ * ⟨c', hc'⟩⁻¹ : ↥E)) =
        (d * d' * d⁻¹ * d'⁻¹) * (c * c' * c⁻¹ * c'⁻¹) := rfl
    rw [← h1, ← h2, ← h3, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  constructor
  · intro r hr
    obtain ⟨d, hd, c, hc, rfl⟩ := exists_mul_of_mem_sup_comm' hES hr
    have : d * c * (d * c) = (d * d) * (c * c) := by
      calc d * c * (d * c) = d * (c * d) * c := by group
        _ = d * (d * c) * c := by rw [← hmul d c hd hc]
        _ = (d * d) * (c * c) := by group
    rw [this]
    exact mul_mem (hS2 d hd) (hE2 c hc)
  · intro r hr r' hr'
    obtain ⟨d, hd, c, hc, rfl⟩ := exists_mul_of_mem_sup_comm' hES hr
    obtain ⟨d', hd', c', hc', rfl⟩ := exists_mul_of_mem_sup_comm' hES hr'
    rw [key d c d' c' hd hc hd' hc']
    exact mul_mem (hSc d hd d' hd') (hEc c hc c' hc')

theorem card_closure_pair [Finite G] {a b : G} (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    Nat.card ↥(closure ({a, b} : Set G)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : closure ({a, b} : Set G) = zpowers a ⊔ zpowers b := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact mem_sup_left (mem_zpowers _)
      · exact mem_sup_right (mem_zpowers _)
    · refine sup_le (zpowers_le.2 (subset_closure (by simp))) (zpowers_le.2 (subset_closure (by simp)))
  have hzK : zpowers a ≤ centralizer ((zpowers b : Subgroup G) : Set G) := by
    rw [zpowers_le]
    refine mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute b a from hab.symm) k)).eq
  have hdisj : ∀ x ∈ zpowers a, x ∈ zpowers b → x = 1 := by
    intro x hx hxb
    rcases mem_zpowers_sq_eq_one ha2 hx with h | h
    · exact h
    · exfalso
      rcases mem_zpowers_sq_eq_one hb2 hxb with h' | h'
      · exact ha1 (h ▸ h')
      · exact hne (h ▸ h')
  have hcard : ∀ {x : G}, x * x = 1 → x ≠ 1 → Nat.card ↥(zpowers x) = 2 := by
    intro x hx2 hx1
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  rw [hsup, card_sup_commuting hzK hdisj, hcard ha2 ha1, hcard hb2 hb1]

end CFSG.EvenSporadicStandard.Fin76b
