module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Mod
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6Lift

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit

open Subgroup CFSG.Fischer
open scoped MatrixGroups

variable {G : Type*} [Group G] (D Y : Subgroup G) [(Y.subgroupOf D).Normal]

theorem actQuot_comm_mk (u : normDY D Y) (x : D) :
    ∃ h : (u : G) * (x : G) * (u : G)⁻¹ * (x : G)⁻¹ ∈ D,
      actQuot D Y u (QuotientGroup.mk x) * (QuotientGroup.mk x)⁻¹ =
        QuotientGroup.mk ⟨(u : G) * (x : G) * (u : G)⁻¹ * (x : G)⁻¹, h⟩ := by
  obtain ⟨h1, h2⟩ := actQuot_mk D Y u x
  have h3 : (u : G) * (x : G) * (u : G)⁻¹ * (x : G)⁻¹ ∈ D :=
    D.mul_mem h1 (D.inv_mem x.2)
  refine ⟨h3, ?_⟩
  rw [h2, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  rfl

theorem quadG [Finite G] (hYD : Y ≤ D) (hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ Y)
    (hDsq : ∀ x ∈ D, x * x ∈ Y) (hDcard : Nat.card D = 2 ^ 16) (hYcard : Nat.card Y = 2 ^ 8)
    {Γ₁ Γ₂ U₁ U₂ : Subgroup G} (hΓ₁ : Γ₁ ≤ normDY D Y) (hΓ₂ : Γ₂ ≤ normDY D Y)
    (e₁ : ↥Γ₁ ≃* SL(2, F4)) (e₂ : ↥Γ₂ ≃* SL(2, F4))
    (hcomm : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a) (hU₁ : U₁ ≤ Γ₁) (hU₂ : U₂ ≤ Γ₂)
    (hlow₁ : ∀ (g : G) (hg : g ∈ U₁),
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1)
    (hlow₂ : ∀ (g : G) (hg : g ∈ U₂),
      (e₂ ⟨g, hU₂ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e₂ ⟨g, hU₂ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧
      (e₂ ⟨g, hU₂ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1)
    (hnt₁ : ∃ (g : G) (hg : g ∈ U₁), e₁ ⟨g, hU₁ hg⟩ ≠ 1)
    (hnt₂ : ∃ (g : G) (hg : g ∈ U₂), e₂ ⟨g, hU₂ hg⟩ ≠ 1)
    (c1 : Nat.card (liftFixG D Y Γ₁) = 2 ^ 12) (c2 : Nat.card (liftFixG D Y Γ₂) = 2 ^ 12)
    (c3 : liftFixG D Y Γ₁ ⊔ liftFixG D Y Γ₂ = D) (c4 : liftFixG D Y Γ₁ ⊓ liftFixG D Y Γ₂ = Y)
    (hplus : Nat.card (liftFixG D Y (U₁ ⊔ U₂)) = 2 ^ 12) :
    (∀ u ∈ U₁, ∀ x ∈ D, u * x * u⁻¹ * x⁻¹ ∈ liftFixG D Y (U₁ ⊔ U₂)) ∧
      (∀ u ∈ U₂, ∀ x ∈ D, u * x * u⁻¹ * x⁻¹ ∈ liftFixG D Y (U₁ ⊔ U₂)) ∧
      (∀ c ∈ liftFixG D Y (U₁ ⊔ U₂), ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₂, ∃ x₁ ∈ D, ∃ x₂ ∈ D, ∃ y ∈ Y,
        c = (u₁ * x₁ * u₁⁻¹ * x₁⁻¹) * (u₂ * x₂ * u₂⁻¹ * x₂⁻¹) * y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN₁ : U₁ ≤ normDY D Y := hU₁.trans hΓ₁
  have hN₂ : U₂ ≤ normDY D Y := hU₂.trans hΓ₂
  have hYpos : 0 < Nat.card Y := by rw [hYcard]; norm_num
  have hV : Nat.card (D ⧸ Y.subgroupOf D) = 2 ^ 8 := by
    have h : 2 ^ 16 = Nat.card (D ⧸ Y.subgroupOf D) * 2 ^ 8 := by
      rw [← hDcard, ← hYcard]
      exact card_D_eq D Y hYD
    have h' : Nat.card (D ⧸ Y.subgroupOf D) * 2 ^ 8 = 2 ^ 8 * 2 ^ 8 := by
      rw [← h]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  have hcommV : ∀ a b : D ⧸ Y.subgroupOf D, a * b = b * a := quot_comm D Y hDcomm
  have hsqV : ∀ a : D ⧸ Y.subgroupOf D, a * a = 1 := quot_mul_self D Y hDsq
  have hcommΓ' : ∀ a ∈ Γ₁.subgroupOf (normDY D Y), ∀ b ∈ Γ₂.subgroupOf (normDY D Y),
      a * b = b * a := fun a ha b hb =>
    Subtype.ext (hcomm (a : G) (Subgroup.mem_subgroupOf.1 ha) (b : G)
      (Subgroup.mem_subgroupOf.1 hb))
  have hU₁' : U₁.subgroupOf (normDY D Y) ≤ Γ₁.subgroupOf (normDY D Y) :=
    Subgroup.subgroupOf_mono _ hU₁
  have hU₂' : U₂.subgroupOf (normDY D Y) ≤ Γ₂.subgroupOf (normDY D Y) :=
    Subgroup.subgroupOf_mono _ hU₂
  set e₁' : ↥(Γ₁.subgroupOf (normDY D Y)) ≃* SL(2, F4) :=
    (Subgroup.subgroupOfEquivOfLe hΓ₁).trans e₁ with he₁'
  set e₂' : ↥(Γ₂.subgroupOf (normDY D Y)) ≃* SL(2, F4) :=
    (Subgroup.subgroupOfEquivOfLe hΓ₂).trans e₂ with he₂'
  have hcard1 : Nat.card (fixSub (actQuot D Y) (Γ₁.subgroupOf (normDY D Y))) = 2 ^ 4 := by
    have h1 : Nat.card (liftFix D Y (Γ₁.subgroupOf (normDY D Y))) = 2 ^ 12 := c1
    rw [card_liftFix D Y hYD, hYcard] at h1
    have h2 : 2 ^ 8 * Nat.card (fixSub (actQuot D Y) (Γ₁.subgroupOf (normDY D Y))) =
        2 ^ 8 * 2 ^ 4 := by rw [h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hcard2 : Nat.card (fixSub (actQuot D Y) (Γ₂.subgroupOf (normDY D Y))) = 2 ^ 4 := by
    have h1 : Nat.card (liftFix D Y (Γ₂.subgroupOf (normDY D Y))) = 2 ^ 12 := c2
    rw [card_liftFix D Y hYD, hYcard] at h1
    have h2 : 2 ^ 8 * Nat.card (fixSub (actQuot D Y) (Γ₂.subgroupOf (normDY D Y))) =
        2 ^ 8 * 2 ^ 4 := by rw [h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hinf : fixSub (actQuot D Y) (Γ₁.subgroupOf (normDY D Y)) ⊓
      fixSub (actQuot D Y) (Γ₂.subgroupOf (normDY D Y)) = ⊥ := by
    rw [← fixSub_sup]
    have hl : liftFix D Y (Γ₁.subgroupOf (normDY D Y) ⊔ Γ₂.subgroupOf (normDY D Y)) = Y := by
      rw [← liftFix_inf]
      exact c4
    have h1 := card_liftFix D Y hYD (Γ₁.subgroupOf (normDY D Y) ⊔ Γ₂.subgroupOf (normDY D Y))
    rw [hl] at h1
    have h2 : Nat.card Y * Nat.card (fixSub (actQuot D Y)
        (Γ₁.subgroupOf (normDY D Y) ⊔ Γ₂.subgroupOf (normDY D Y))) = Nat.card Y * 1 := by
      rw [← h1, mul_one]
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_of_mul_eq_mul_left hYpos h2)
  have hnormV : ∀ A B : Subgroup (D ⧸ Y.subgroupOf D), A ≤ normalizer (B : Set _) :=
    fun A B a _ => mem_normalizer_iff.2 fun h => by
      rw [hcommV a h, mul_assoc, mul_inv_cancel, mul_one]
  have hsup : fixSub (actQuot D Y) (Γ₁.subgroupOf (normDY D Y)) ⊔
      fixSub (actQuot D Y) (Γ₂.subgroupOf (normDY D Y)) = ⊤ := by
    have h1 := PGrp.card_sup_mul_card_inf (hnormV
      (fixSub (actQuot D Y) (Γ₁.subgroupOf (normDY D Y)))
      (fixSub (actQuot D Y) (Γ₂.subgroupOf (normDY D Y))))
    rw [hinf, Subgroup.card_bot, mul_one, hcard1, hcard2] at h1
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [h1, hV]
    norm_num
  have hplus' : Nat.card (fixSub (actQuot D Y)
      (U₁.subgroupOf (normDY D Y) ⊔ U₂.subgroupOf (normDY D Y))) = 2 ^ 4 := by
    have h1 : Nat.card (liftFix D Y ((U₁ ⊔ U₂).subgroupOf (normDY D Y))) = 2 ^ 12 := hplus
    rw [Subgroup.subgroupOf_sup hN₁ hN₂] at h1
    rw [card_liftFix D Y hYD, hYcard] at h1
    have h2 : 2 ^ 8 * Nat.card (fixSub (actQuot D Y)
        (U₁.subgroupOf (normDY D Y) ⊔ U₂.subgroupOf (normDY D Y))) = 2 ^ 8 * 2 ^ 4 := by
      rw [h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  obtain ⟨hI₁, hI₂, hII⟩ := quad_gen_of_split (actQuot D Y) hcommV hsqV e₁' e₂' hcommΓ' hU₁' hU₂'
    (fun g hg => hlow₁ (g : G) (Subgroup.mem_subgroupOf.1 hg))
    (fun g hg => hlow₂ (g : G) (Subgroup.mem_subgroupOf.1 hg))
    (by
      obtain ⟨g, hg, hne⟩ := hnt₁
      exact ⟨⟨g, hN₁ hg⟩, hg, hne⟩)
    (by
      obtain ⟨g, hg, hne⟩ := hnt₂
      exact ⟨⟨g, hN₂ hg⟩, hg, hne⟩)
    hcard1 hcard2 hsup hinf hplus'
  have hS : liftFixG D Y (U₁ ⊔ U₂) =
      liftFix D Y (U₁.subgroupOf (normDY D Y) ⊔ U₂.subgroupOf (normDY D Y)) := by
    show liftFix D Y ((U₁ ⊔ U₂).subgroupOf (normDY D Y)) = _
    rw [Subgroup.subgroupOf_sup hN₁ hN₂]
  refine ⟨fun u hu x hx => ?_, fun u hu x hx => ?_, fun c hc => ?_⟩
  · have hu' : (⟨u, hN₁ hu⟩ : normDY D Y) ∈ U₁.subgroupOf (normDY D Y) := hu
    have key := hI₁ ⟨u, hN₁ hu⟩ hu' (QuotientGroup.mk ⟨x, hx⟩)
    obtain ⟨hz, hzeq⟩ := actQuot_comm_mk D Y ⟨u, hN₁ hu⟩ ⟨x, hx⟩
    rw [hzeq] at key
    rw [hS]
    exact ⟨⟨u * x * u⁻¹ * x⁻¹, hz⟩, key, rfl⟩
  · have hu' : (⟨u, hN₂ hu⟩ : normDY D Y) ∈ U₂.subgroupOf (normDY D Y) := hu
    have key := hI₂ ⟨u, hN₂ hu⟩ hu' (QuotientGroup.mk ⟨x, hx⟩)
    obtain ⟨hz, hzeq⟩ := actQuot_comm_mk D Y ⟨u, hN₂ hu⟩ ⟨x, hx⟩
    rw [hzeq] at key
    rw [hS]
    exact ⟨⟨u * x * u⁻¹ * x⁻¹, hz⟩, key, rfl⟩
  · rw [hS] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    obtain ⟨u₁, hu₁, u₂, hu₂, v₁, v₂, hcv⟩ := hII (QuotientGroup.mk c') hc'
    obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective v₁
    obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective v₂
    obtain ⟨h1, h1eq⟩ := actQuot_comm_mk D Y u₁ x₁
    obtain ⟨h2, h2eq⟩ := actQuot_comm_mk D Y u₂ x₂
    rw [h1eq, h2eq, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hcv
    have hy : (c' : G)⁻¹ * ((u₁ : G) * (x₁ : G) * (u₁ : G)⁻¹ * (x₁ : G)⁻¹ *
        ((u₂ : G) * (x₂ : G) * (u₂ : G)⁻¹ * (x₂ : G)⁻¹)) ∈ Y := hcv
    refine ⟨(u₁ : G), hu₁, (u₂ : G), hu₂, (x₁ : G), x₁.2, (x₂ : G), x₂.2,
      ((c' : G)⁻¹ * ((u₁ : G) * (x₁ : G) * (u₁ : G)⁻¹ * (x₁ : G)⁻¹ *
        ((u₂ : G) * (x₂ : G) * (u₂ : G)⁻¹ * (x₂ : G)⁻¹)))⁻¹, Y.inv_mem hy, ?_⟩
    simp [mul_assoc]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModSplit
