module

public import CFSG.Goldschmidt75.Quotient
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Goldschmidt.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

@[expose] def ThmAFor (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (S₁ S₂ : Subgroup G), S₁ ≤ T → S₂ ≤ T →
    fusionStronglyClosed (S₁ : Set G) T → fusionStronglyClosed (S₂ : Set G) T →
    S₁ ≤ centralizer (S₂ : Set G) → S₁ ⊓ S₂ = ⊥ →
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤ goldschmidtOddCore G

structure MinCE (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (S₁ S₂ : Subgroup G) : Prop where
  le₁ : S₁ ≤ T
  le₂ : S₂ ≤ T
  sc₁ : fusionStronglyClosed (S₁ : Set G) T
  sc₂ : fusionStronglyClosed (S₂ : Set G) T
  comm : S₁ ≤ centralizer (S₂ : Set G)
  disj : S₁ ⊓ S₂ = ⊥
  ihG : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → ThmAFor H
  ihS : ∀ (T' : Sylow 2 G) (R₁ R₂ : Subgroup G), R₁ ≤ T' → R₂ ≤ T' →
    fusionStronglyClosed (R₁ : Set G) T' → fusionStronglyClosed (R₂ : Set G) T' →
    R₁ ≤ centralizer (R₂ : Set G) → R₁ ⊓ R₂ = ⊥ →
    Nat.card R₁ * Nat.card R₂ < Nat.card S₁ * Nat.card S₂ →
    ⁅normalClosure (R₁ : Set G), normalClosure (R₂ : Set G)⁆ ≤ goldschmidtOddCore G
  fail : ¬ ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤ goldschmidtOddCore G

variable {G : Type} [Group G] [Finite G]

theorem MinCE.symm {T : Sylow 2 G} {S₁ S₂ : Subgroup G} (h : MinCE G T S₁ S₂) :
    MinCE G T S₂ S₁ where
  le₁ := h.le₂
  le₂ := h.le₁
  sc₁ := h.sc₂
  sc₂ := h.sc₁
  comm := le_centralizer_iff.mp h.comm
  disj := by rw [inf_comm]; exact h.disj
  ihG := h.ihG
  ihS := fun T' R₁ R₂ h₁ h₂ hc₁ hc₂ hc hd hlt => by
    rw [commutator_comm]
    exact h.ihS T' R₂ R₁ h₂ h₁ hc₂ hc₁ (le_centralizer_iff.mp hc) (by rw [inf_comm]; exact hd)
      (by rw [mul_comm (Nat.card R₂), mul_comm (Nat.card S₁)]; exact hlt)
  fail := by rw [commutator_comm]; exact h.fail

theorem thmA_in {H : Subgroup G} (hH : ThmAFor H) (TH : Sylow 2 H) {R₁ R₂ : Subgroup G}
    (h₁ : R₁.subgroupOf H ≤ TH) (h₂ : R₂.subgroupOf H ≤ TH)
    (hc₁ : fusionStronglyClosed ((R₁.subgroupOf H : Subgroup H) : Set H) TH)
    (hc₂ : fusionStronglyClosed ((R₂.subgroupOf H : Subgroup H) : Set H) TH)
    (hc : R₁ ≤ centralizer (R₂ : Set G)) (hd : R₁ ⊓ R₂ = ⊥) :
    ⁅normalClosureIn H R₁, normalClosureIn H R₂⁆ ≤ oddCoreOf H := by
  have hcH : R₁.subgroupOf H ≤ centralizer ((R₂.subgroupOf H : Subgroup H) : Set H) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp (hc (mem_subgroupOf.mp hx)) y
      (mem_subgroupOf.mp hy))
  have hdH : R₁.subgroupOf H ⊓ R₂.subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ R₁ ⊓ R₂ := ⟨mem_subgroupOf.mp hx.1, mem_subgroupOf.mp hx.2⟩
    rw [hd, mem_bot] at hx'
    exact (mem_bot).mpr (Subtype.ext hx')
  have h := Subgroup.map_mono (f := H.subtype) (hH TH _ _ h₁ h₂ hc₁ hc₂ hcH hdH)
  rwa [Subgroup.map_commutator] at h

theorem thmA_quotient {N : Subgroup G} [N.Normal] (hN : ThmAFor (G ⧸ N)) (T : Sylow 2 G)
    {S₁ S₂ : Subgroup G} (h₁ : S₁ ≤ T) (h₂ : S₂ ≤ T) (hc₁ : fusionStronglyClosed (S₁ : Set G) T)
    (hc₂ : fusionStronglyClosed (S₂ : Set G) T) (hc : S₁ ≤ centralizer (S₂ : Set G))
    (hd : ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, s₂⁻¹ * s₁ ∈ N → s₁ ∈ N) :
    ⁅normalClosure (S₁ : Set G), normalClosure (S₂ : Set G)⁆ ≤
      (goldschmidtOddCore (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  have hsurj := QuotientGroup.mk'_surjective N
  have hcbar : S₁.map (QuotientGroup.mk' N) ≤
      centralizer ((S₂.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp (hc ha) b hb]
  have hdbar : S₁.map (QuotientGroup.mk' N) ⊓ S₂.map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
    rw [mem_bot]
    exact (QuotientGroup.eq_one_iff a).mpr (hd a ha b hb (QuotientGroup.eq.mp hba))
  have h := hN (sylowMap N T) _ _ (by rw [coe_sylowMap]; exact Subgroup.map_mono h₁)
    (by rw [coe_sylowMap]; exact Subgroup.map_mono h₂) (stronglyClosed_map N T h₁ hc₁)
    (stronglyClosed_map N T h₂ hc₂) hcbar hdbar
  rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator, Subgroup.map_normalClosure _ _ hsurj,
    Subgroup.map_normalClosure _ _ hsurj]
  simpa only [Subgroup.coe_map] using h

end CFSG.Goldschmidt75
