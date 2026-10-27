module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthD4Centralizer
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv)

variable {p f : ℕ} [Fact p.Prime]

section Predicates

variable {KY : Type} [Group KY]

@[expose] def D4Centralizer (Z : Subgroup KY) (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ c ∈ 𝓕, ∀ l₁ ∈ 𝓕, ∀ l₂ ∈ 𝓕, ∀ l₃ ∈ 𝓕, ModelAdj Z c l₁ → ModelAdj Z c l₂ → ModelAdj Z c l₃ →
    l₁ ≠ l₂ → l₁ ≠ l₃ → l₂ ≠ l₃ → Commutes l₁ l₂ → Commutes l₁ l₃ → Commutes l₂ l₃ →
    ∀ S ∈ 𝓕, ∀ S' ∈ 𝓕, S ≠ S' → Commutes S c → Commutes S l₁ → Commutes S l₂ →
      Commutes S l₃ → Commutes S' c → Commutes S' l₁ → Commutes S' l₂ → Commutes S' l₃ →
      ModelIndist Z 𝓕 S S'

@[expose] def D4Empty (Z : Subgroup KY) (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ c ∈ 𝓕, ∀ l₁ ∈ 𝓕, ∀ l₂ ∈ 𝓕, ∀ l₃ ∈ 𝓕, ModelAdj Z c l₁ → ModelAdj Z c l₂ → ModelAdj Z c l₃ →
    l₁ ≠ l₂ → l₁ ≠ l₃ → l₂ ≠ l₃ → Commutes l₁ l₂ → Commutes l₁ l₃ → Commutes l₂ l₃ →
    ∀ S ∈ 𝓕, ¬ (Commutes S c ∧ Commutes S l₁ ∧ Commutes S l₂ ∧ Commutes S l₃)

end Predicates

section Quot

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

namespace CentralQuot

theorem d4Centralizer (h : CentralQuot π 𝓕 𝓕' Z') (hG : D4Centralizer Z' 𝓕') :
    D4Centralizer (Subgroup.center KY) 𝓕 := by
  intro c hc l₁ h₁ l₂ h₂ l₃ h₃ a₁ a₂ a₃ n12 n13 n23 k12 k13 k23 S hS S' hS' hne cS c1 c2 c3 cS'
    c1' c2' c3'
  refine h.modelIndist hS hS' hne ?_
  refine hG (c.map π) (h.map_mem c hc) (l₁.map π) (h.map_mem l₁ h₁) (l₂.map π)
    (h.map_mem l₂ h₂) (l₃.map π) (h.map_mem l₃ h₃) (h.modelAdj hc h₁ a₁) (h.modelAdj hc h₂ a₂)
    (h.modelAdj hc h₃ a₃) (fun e => n12 (h.map_inj h₁ h₂ e)) (fun e => n13 (h.map_inj h₁ h₃ e))
    (fun e => n23 (h.map_inj h₂ h₃ e)) ((h.commutes_iff h₁).mpr k12) ((h.commutes_iff h₁).mpr k13)
    ((h.commutes_iff h₂).mpr k23) (S.map π) (h.map_mem S hS) (S'.map π) (h.map_mem S' hS')
    (fun e => hne (h.map_inj hS hS' e)) ((h.commutes_iff hS).mpr cS) ((h.commutes_iff hS).mpr c1)
    ((h.commutes_iff hS).mpr c2) ((h.commutes_iff hS).mpr c3) ((h.commutes_iff hS').mpr cS')
    ((h.commutes_iff hS').mpr c1') ((h.commutes_iff hS').mpr c2') ((h.commutes_iff hS').mpr c3')

theorem d4Empty (h : CentralQuot π 𝓕 𝓕' Z') (hG : D4Empty Z' 𝓕') :
    D4Empty (Subgroup.center KY) 𝓕 := by
  intro c hc l₁ h₁ l₂ h₂ l₃ h₃ a₁ a₂ a₃ n12 n13 n23 k12 k13 k23 S hS ⟨cS, c1, c2, c3⟩
  exact hG (c.map π) (h.map_mem c hc) (l₁.map π) (h.map_mem l₁ h₁) (l₂.map π)
    (h.map_mem l₂ h₂) (l₃.map π) (h.map_mem l₃ h₃) (h.modelAdj hc h₁ a₁) (h.modelAdj hc h₂ a₂)
    (h.modelAdj hc h₃ a₃) (fun e => n12 (h.map_inj h₁ h₂ e)) (fun e => n13 (h.map_inj h₁ h₃ e))
    (fun e => n23 (h.map_inj h₂ h₃ e)) ((h.commutes_iff h₁).mpr k12) ((h.commutes_iff h₁).mpr k13)
    ((h.commutes_iff h₂).mpr k23) (S.map π) (h.map_mem S hS)
    ⟨(h.commutes_iff hS).mpr cS, (h.commutes_iff hS).mpr c1, (h.commutes_iff hS).mpr c2,
      (h.commutes_iff hS).mpr c3⟩

end CentralQuot

end Quot

section Plus

variable {m : ℕ}

theorem d4Centralizer_model (hp2 : p ≠ 2) (hm : 5 ≤ m) (hm6 : m ≤ 6) (hq : 5 ≤ p ^ f) :
    D4Centralizer (scalars (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f))
      (fundSet (quadPlus m (GaloisField p f))) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hd := finrank_plus p f m
  exact orth_d4_centralizer hodd (nondegenerate_polarBilin_quadPlus m (GaloisField p f))
    (by omega) (by omega)

theorem d4Empty_model (hp2 : p ≠ 2) (hm : m = 5) (hq : 5 ≤ p ^ f) :
    D4Empty (scalars (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f))
      (fundSet (quadPlus m (GaloisField p f))) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hd := finrank_plus p f m
  exact orth_d4_centralizer_empty hodd (nondegenerate_polarBilin_quadPlus m (GaloisField p f))
    (by omega) (by omega)

theorem d4Centralizer_plusDatum (hp2 : p ≠ 2) (hm : 5 ≤ m) (hm6 : m ≤ 6) (hm3 : 3 ≤ m)
    (hq : 5 ≤ p ^ f) :
    D4Centralizer (Subgroup.center (spinGroup (quadPlus m (GaloisField p f))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) :=
  (centralQuot_plus hp2 (by omega) hm3 hq).d4Centralizer (d4Centralizer_model hp2 hm hm6 hq)

theorem d4Empty_plusDatum (hp2 : p ≠ 2) (hm : m = 5) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    D4Empty (Subgroup.center (spinGroup (quadPlus m (GaloisField p f))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) :=
  (centralQuot_plus hp2 (by omega) hm3 hq).d4Empty (d4Empty_model hp2 hm hq)

theorem d4Centralizer_plus (hp2 : p ≠ 2) (hm : 5 ≤ m) (hm6 : m ≤ 6) (hq : 5 ≤ p ^ f) :
    D4Centralizer (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact d4Centralizer_plusDatum hp2 hm hm6 (by omega) hq

theorem d4Empty_plus (hp2 : p ≠ 2) (hm : m = 5) (hq : 5 ≤ p ^ f) :
    D4Empty (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact d4Empty_plusDatum hp2 hm (by omega) hq

end Plus

end CFSG.ClassicalInvolution.RouteD.Gaps
