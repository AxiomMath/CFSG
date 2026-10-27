module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCharBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwo

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem card_le_of_comm_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {B : Subgroup G}
    (hB : B ≤ szT₁ L T) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : Nat.card B ≤ (2 ^ f) ^ 2 := by
  obtain ⟨E, _, _, _, σ, -, -, hF, u, v, hc, hA⟩ := h.exists_rootCoords_of_card_sylow hS2
  obtain ⟨-, hA₁, -⟩ := h.facts_of_card_sylow hS2
  have := hc.card_le_of_comm hA hB hBc
  rwa [hA₁, hF, ← sq] at this

theorem exists_comm_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {y : G}
    (hy : y ∈ szT₁ L T) :
    ∃ B : Subgroup G, B ≤ szT₁ L T ∧ (∀ x ∈ B, ∀ z ∈ B, x * z = z * x) ∧ y ∈ B ∧
      szA₁ (szT₁ L T) ≤ B ∧ Nat.card B = (2 ^ f) ^ 2 := by
  obtain ⟨E, _, _, _, σ, -, -, hF, u, v, hc, hA⟩ := h.exists_rootCoords_of_card_sylow hS2
  obtain ⟨-, hA₁, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨B, hBT, hBc, hyB, hAB, hBcard⟩ := hc.exists_comm_of_mem (szA₁_le _) hA hy
  exact ⟨B, hBT, hBc, hyB, hAB, by rw [hBcard, hA₁, hF, ← sq]⟩

theorem le_u3R₁_of_u3R2 {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    R₂ ≤ u3R₁ L T t ⊓ centralizer (szT₁ L T : Set G) := by
  intro r hr
  have hconjA : ∀ g ∈ R₂, ∀ x ∈ szA L T t, g⁻¹ * x * g ∈ szA L T t := by
    intro g hg x hx
    have hle : szA L T t ≤ (szA L T t).comap (MulAut.conj g⁻¹).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
      · rw [mem_comap]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        have hag := hR.comm a (hR.le ha) g hg
        rw [show g⁻¹ * a * g = a by rw [mul_assoc, hag, inv_mul_cancel_left]]
        exact mem_sup_left ha
      · rw [mem_comap]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        have h1 := hR.rho_mem _ (inv_mem hg)
        rw [inv_inv] at h1
        have e : g⁻¹ * t * g = (g⁻¹ * t * g * t) * t := by
          rw [mul_assoc (g⁻¹ * t * g) t t, ← sq, hR.t_sq, mul_one]
        rw [e]
        exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers t))
    have := hle hx
    rw [mem_comap] at this
    simpa using this
  refine ⟨⟨?_, mem_centralizer_iff.mpr fun a ha => hR.comm a (hR.le ha) r hr,
    hR.le_normalizer_T₁ hr, fun y hy => ?_⟩, hR.le_centralizer_T₁ hr⟩
  · exact mem_normalizer_of_forall_inv_mul_mul_mem fun x hx => hconjA r hr x hx
  · rw [show r * y * r⁻¹ = y by rw [← hR.commT₁ y hy r hr, mul_inv_cancel_right], inv_mul_cancel]
    exact one_mem _

theorem char_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    (szT₁ L T ⊔ R₂) ⊓ centralizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) = R₂ ∧
      (∀ B : Subgroup G, B ≤ szR (szT₁ L T) R₂ t → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
        Nat.card B ≤ (2 ^ f) ^ 3 ∧ ((2 ^ f) ^ 3 ≤ Nat.card B → B ≤ szT₁ L T ⊔ R₂)) ∧
      (∀ x ∈ szT₁ L T ⊔ R₂, ∃ B : Subgroup G, B ≤ szT₁ L T ⊔ R₂ ∧
        (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ x ∈ B ∧ Nat.card B = (2 ^ f) ^ 3) ∧
      normalizer (szR (szT₁ L T) R₂ t : Set G) ≤
        normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) ⊓ normalizer (R₂ : Set G) := by
  obtain ⟨-, hA₁, -⟩ := h.facts_of_card_sylow hS2
  have hab := fun B hB hBc => h.card_le_of_comm_of_card_sylow hS2 (B := B) hB hBc
  have hex := fun y (hy : y ∈ szT₁ L T) => h.exists_comm_of_card_sylow hS2 hy
  exact ⟨hR.center_sup_eq, fun B hB hBc => hR.card_le_of_comm hab hA₁ h.two_le hB hBc,
    fun x hx => hR.exists_comm_of_mem_sup hex hA₁ hx, hR.normalizer_le hab hex hA₁ h.two_le⟩

theorem charInput_of_le_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hT : T ≤ szT₁ L T ⊔ zpowers t) {B : Subgroup G}
    (hB : B ≤ T ⊔ R₂) (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hcard : (2 ^ f) ^ 3 ≤ Nat.card B) :
    B ≤ szT₁ L T ⊔ R₂ := by
  have hle : T ⊔ R₂ ≤ szR (szT₁ L T) R₂ t :=
    sup_le (hT.trans (sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))))
      (le_szR_mid _ _ _)
  exact ((h.char_of_card_sylow hS2 hR).2.1 B (hB.trans hle) hBc).2 hcard

section Certificates

theorem u3R2_canonical_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    szT₁ L T ⊔ R₂ ⊔ zpowers t = u3R₁ L T t ∧ szA L T t ⊓ R₂ = szA₁ (szT₁ L T) ∧
      u3R₁ L T t ⊓ centralizer (szT₁ L T : Set G) = R₂ ⊔ zpowers t ∧
      normalizer (szA L T t : Set G) ≤
        normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer (szA L T t : Set G) ≤ normalizer (R₂ : Set G) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (T ⊔ R₂) (normalizer (szA L T t : Set G)) := by
  obtain ⟨R₂', -, h1, h2, h3, huniq, h5, h6, h7⟩ := h.exists_u3R2_canonical_of_card_sylow hS2
  have heq : R₂ = R₂' := huniq R₂ hR.comm (le_u3R₁_of_u3R2 hR) hR.card
  subst heq
  exact ⟨h1, h2, h3, h5, h6, h7⟩

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
