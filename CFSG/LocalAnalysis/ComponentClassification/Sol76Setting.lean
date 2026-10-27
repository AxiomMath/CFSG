module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInputs

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Thm13At (G : Type*) [Group G] : Prop :=
  ∀ N : Subgroup G, IsKBalanced N → solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G)

@[expose] def Thm13Below (G : Type*) [Group G] : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → Thm13At H

variable {G : Type*} [Group G]

@[expose] def kStarComponents (N : Subgroup G) : Set (Subgroup G) :=
  {J | IsTwoComponentIn J N ∧ J ∈ solomonKStar G}

@[expose] def kStarKernel (N : Subgroup G) : Subgroup G :=
  N ⊓ coreActionKernel (solomonKStarOf N)

@[expose] noncomputable def kStarMeasure [Finite G] (N : Subgroup G) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex ((kStarComponents N).ncard,
    toLex (CFSG.pRank 2 ↥(kStarKernel N), (Nat.card ↥(kStarKernel N)).factorization 2))

@[expose] def IsSolomonChoice [Finite G] (N : Subgroup G) : Prop :=
  IsKBalanced N ∧ ¬ solomonKStarOf N ≤ solomonKStarOf (⊤ : Subgroup G) ∧
    ∀ N' : Subgroup G, IsKBalanced N' → ¬ solomonKStarOf N' ≤ solomonKStarOf (⊤ : Subgroup G) →
      kStarMeasure N' ≤ kStarMeasure N

theorem exists_isSolomonChoice [Finite G] (h : ¬ Thm13At G) :
    ∃ N : Subgroup G, IsSolomonChoice N := by
  classical
  simp only [Thm13At, not_forall] at h
  obtain ⟨N₀, hN₀, hv₀⟩ := h
  let P := {N : Subgroup G // IsKBalanced N ∧ ¬ solomonKStarOf N ≤ solomonKStarOf ⊤}
  have : Nonempty P := ⟨⟨N₀, hN₀, hv₀⟩⟩
  obtain ⟨⟨N, hN, hv⟩, hmax⟩ := Finite.exists_max (fun p : P => kStarMeasure p.1)
  exact ⟨N, hN, hv, fun N' hN' hv' => hmax ⟨N', hN', hv'⟩⟩

theorem solomonThm13Input_of_noChoice
    (h : ∀ (G : Type) [Group G] [Finite G], Thm13Below G → ∀ N : Subgroup G, ¬ IsSolomonChoice N) :
    SolomonThm13Input := by
  suffices key : ∀ m : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = m → Thm13At G by
    intro G _ _ N hN
    exact key _ G rfl N hN
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro G _ _ hm
    by_contra hG
    obtain ⟨N, hN⟩ := exists_isSolomonChoice hG
    exact h G (fun H _ _ hH => ih _ (hm ▸ hH) H rfl) N hN

end CFSG.ComponentClassification.Sol76
