module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Layer

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem u3U_lambda_facts_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b) :
    (∀ v ∈ u3U L T R₂ t E, ∀ x ∈ szT₁ L T ⊔ R₂, x⁻¹ * (v * x * v⁻¹) ∈ R₂) ∧
      (∀ v ∈ u3U L T R₂ t E, v * t * v⁻¹ * t⁻¹ ∈ szT₁ L T ⊔ R₂) ∧
      (∀ v ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G),
        ∀ w ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), v * w * v⁻¹ * w⁻¹ ∈ szT₁ L T ⊔ R₂) ∧
      (∀ v ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G), v ^ 2 ∈ szT₁ L T ⊔ R₂) := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  set U := u3U L T R₂ t E with hU
  set H := szT₁ L T ⊔ R₂ with hH
  have hUY := u3U_le_normalizer L T R₂ t E
  have hUR₂ : U ≤ normalizer (R₂ : Set G) := fun y hy => (mem_inf.mp (hNR₁ (hUY hy))).2
  have hUH : U ≤ normalizer (H : Set G) := fun y hy => (mem_inf.mp (hNR₁ (hUY hy))).1
  have htriv : ∀ v ∈ U, ∀ x ∈ H, x⁻¹ * (v * x * v⁻¹) ∈ R₂ := by
    intro v hv x hx
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hx
    have h1 := h.conj_mem_of_mem_u3U_of_card_sylow hS2 hR hc hΩ hEn hEreg hv hw
    have hvr : v * r * v⁻¹ ∈ R₂ := (mem_normalizer_iff.mp (hUR₂ hv) r).mp hr
    have e : (w * r)⁻¹ * (v * (w * r) * v⁻¹) = r⁻¹ * (w⁻¹ * (v * w * v⁻¹)) * (v * r * v⁻¹) := by
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hr) h1) hvr
  have hcH : ∀ v ∈ U, v * t * v⁻¹ * t⁻¹ ∈ H := by
    intro v hv
    obtain ⟨w, hw, r, hr, hwr⟩ := h.exists_mul_of_mem_normalizer_szR_of_card_sylow hS2 hR (hUY hv)
    rw [hwr, mul_inv_cancel_right]
    exact mul_mem (mem_sup_left hw) (mem_sup_right hr)
  have hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ * b⁻¹ ∈ R₂ := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ szA₁ (szT₁ L T) := by
      rw [h.szA₁_eq_commutator_sup_of_card_sylow hS2 hR]
      exact commutator_mem_commutator ha hb
    rw [commutatorElement_def] at h1
    exact hR.le h1
  have hHsq : ∀ a ∈ H, a ^ 2 ∈ R₂ := by
    intro a ha
    obtain ⟨-, -, -, hsq, -⟩ := h.facts_of_card_sylow hS2
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp ha
    have hwr : Commute w r := hR.commT₁ w hw r hr
    rw [hwr.mul_pow]
    exact mul_mem (hR.le (hsq w hw)) (hR.le (hR.sq_mem r hr))
  have hNorm : (R₂.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hR.T₁_le_normalizer Subgroup.le_normalizer)
  have hQcomm : ∀ p q : H ⧸ R₂.subgroupOf H, p * q = q * p := by
    intro p q
    induction p using QuotientGroup.induction_on with | H a => ?_
    induction q using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    have h1 := hHcomm _ (inv_mem b.2) _ (inv_mem a.2)
    have e : (((a * b)⁻¹ * (b * a) : H) : G) = (b : G)⁻¹ * (a : G)⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rw [e]
    exact h1
  let ψ : U →* H ⧸ R₂.subgroupOf H := MonoidHom.mk'
    (fun v => ((⟨(v : G) * t * (v : G)⁻¹ * t⁻¹, hcH v v.2⟩ : H) : H ⧸ R₂.subgroupOf H))
    (fun a b => by
      have hb := hcH b b.2
      have ha := hcH a a.2
      have hab : (a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G)⁻¹ ∈ H :=
        (mem_normalizer_iff.mp (hUH a.2) _).mp hb
      have e : (⟨((a * b : U) : G) * t * ((a * b : U) : G)⁻¹ * t⁻¹, hcH _ (a * b).2⟩ : H) =
          ⟨(a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G)⁻¹, hab⟩ *
            ⟨(a : G) * t * (a : G)⁻¹ * t⁻¹, ha⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group
      rw [e, QuotientGroup.mk_mul]
      have e2 : ((⟨(a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G)⁻¹, hab⟩ : H) :
          H ⧸ R₂.subgroupOf H) = ((⟨(b : G) * t * (b : G)⁻¹ * t⁻¹, hb⟩ : H) : _) := by
        rw [QuotientGroup.eq, mem_subgroupOf]
        have h1 := htriv a a.2 _ hb
        have h2 := inv_mem h1
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] using h2
      rw [e2, hQcomm])
  have hψ1 : ∀ v : U, ψ v = 1 → (v : G) * t * (v : G)⁻¹ * t⁻¹ ∈ R₂ := by
    intro v hv
    have h1 := (QuotientGroup.eq_one_iff _).mp hv
    exact mem_subgroupOf.mp h1
  have hker : ∀ x ∈ U ⊓ centralizer (R₂ : Set G), x * t * x⁻¹ * t⁻¹ ∈ R₂ → x ∈ H := by
    intro x hx hxc
    refine h.mem_sup_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hx ?_
    have e : t * x * t⁻¹ * x⁻¹ = (x * t * x⁻¹ * t⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hxc
  refine ⟨htriv, hcH, fun v hv w hw => hker _ (mul_mem (mul_mem (mul_mem hv hw) (inv_mem hv))
    (inv_mem hw)) ?_, fun v hv => hker _ (pow_mem hv 2) ?_⟩
  · have h1 : ψ (⟨v, (mem_inf.mp hv).1⟩ * ⟨w, (mem_inf.mp hw).1⟩ * (⟨v, (mem_inf.mp hv).1⟩ : U)⁻¹ *
        (⟨w, (mem_inf.mp hw).1⟩ : U)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hQcomm (ψ _) (ψ _)]
      group
    exact hψ1 _ h1
  · have h1 : ψ (⟨v, (mem_inf.mp hv).1⟩ ^ 2) = 1 := by
      rw [map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [mem_subgroupOf]
      exact hHsq _ (hcH v (mem_inf.mp hv).1)
    exact hψ1 _ h1

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
