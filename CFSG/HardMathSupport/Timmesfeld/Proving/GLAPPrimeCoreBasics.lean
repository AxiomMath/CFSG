module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G]

theorem GLAPPrimeCoreOf_le {p : ℕ} (C : Subgroup G) : GLAPPrimeCoreOf p C ≤ C :=
  Subgroup.map_subtype_le _

theorem GLAPPrimeCoreOf_conj_mem {p : ℕ} {C : Subgroup G} :
    ∀ g ∈ C, ∀ x ∈ GLAPPrimeCoreOf p C, g * x * g⁻¹ ∈ GLAPPrimeCoreOf p C := by
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : ↥C) * y * (⟨g, hg⟩ : ↥C)⁻¹,
    (GLAPPrimeCore.normal p ↥C).conj_mem y hy _, ?_⟩
  simp

theorem coprime_card_GLAPPrimeCoreOf [Finite G] {p : ℕ} (hp : p.Prime) (C : Subgroup G) :
    Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p C)) := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective Subtype.val_injective]
  exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp ↥C

theorem le_GLAPPrimeCoreOf_of_normal {p : ℕ} {C S : Subgroup G} (hSC : S ≤ C)
    (hS : ∀ g ∈ C, ∀ x ∈ S, g * x * g⁻¹ ∈ S) (hcop : Nat.Coprime p (Nat.card S)) :
    S ≤ GLAPPrimeCoreOf p C := by
  have hnormal : (S.subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hS (g : G) g.2 (x : G) hx
  have hle : S.subgroupOf C ≤ GLAPPrimeCore p C := by
    refine le_sSup (show S.subgroupOf C ∈ {N : Subgroup C | N.Normal ∧
      Nat.Coprime p (Nat.card N)} from ⟨hnormal, ?_⟩)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
    exact hcop
  intro x hx
  refine Subgroup.mem_map.2 ⟨⟨x, hSC hx⟩, hle ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.2 hx

end CFSG.HardMathSupport.Timmesfeld.Proving

end
