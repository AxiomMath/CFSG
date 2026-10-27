module

public import CFSG.GH74.BNPair.Prop302

public noncomputable section

namespace CFSG.GH74.GLS.SP

universe u

open CFSG.GH74.BNPair
open scoped Pointwise

open Classical in
structure PreRankTwoSystem (X : Type*) [Group X] (n : ℕ) where
  B : Subgroup X
  N : Subgroup X
  [normal : (cartan B N).Normal]
  w₁ : WeylGroup B N
  w₂ : WeylGroup B N
  U : Subgroup X
  root : ℤ → Subgroup X
  isTits : IsTitsSystem B N {w₁, w₂}
  w₁_ne_w₂ : w₁ ≠ w₂
  isSplit : IsSplit B N U
  isSaturated : IsSaturated B N
  card_weyl : Nat.card (WeylGroup B N) = 2 * n
  three_le : 3 ≤ n
  roots : IsRootGroupSystem B N w₁ w₂ U n root

attribute [instance] PreRankTwoSystem.normal

namespace PreRankTwoSystem

variable {X : Type*} [Group X] {n : ℕ}

@[expose] def toSystem (D : PreRankTwoSystem X n) (h : FaithfulOnBuilding D.B D.N D.w₁ D.w₂) :
    RankTwoSystem X n where
  B := D.B
  N := D.N
  w₁ := D.w₁
  w₂ := D.w₂
  U := D.U
  root := D.root
  isTits := D.isTits
  w₁_ne_w₂ := D.w₁_ne_w₂
  isSplit := D.isSplit
  isSaturated := D.isSaturated
  faithful := h
  card_weyl := D.card_weyl
  three_le := D.three_le
  roots := D.roots

theorem parabolic_w₁_ne_top {X : Type u} [Group X] {n : ℕ} (D : PreRankTwoSystem X n) :
    parabolic D.B D.N {D.w₁} ≠ ⊤ := by
  classical
  have h := prop30_2.{u} X D.B D.N {D.w₁, D.w₂} D.isTits
  intro htop
  have h1 : parabolic D.B D.N (({D.w₁, D.w₂} : Finset (WeylGroup D.B D.N)) : Set _) ≤
      parabolic D.B D.N (({D.w₁} : Finset (WeylGroup D.B D.N)) : Set _) := by
    rw [h.parabolic_univ, Finset.coe_singleton, htop]
  rw [h.parabolic_le_iff _ _ (Finset.Subset.refl _) (by simp)] at h1
  exact D.w₁_ne_w₂ (by simpa using (Finset.mem_singleton.1 (h1 (by simp))).symm)

theorem faithful_of_isSimpleGroup {X : Type u} [Group X] [IsSimpleGroup X] {n : ℕ}
    (D : PreRankTwoSystem X n) : FaithfulOnBuilding D.B D.N D.w₁ D.w₂ := by
  intro g hg
  have hmem : g ∈ Subgroup.normalCore (parabolic D.B D.N {D.w₁}) := by
    intro x
    have hv := hg _ (Or.inl ⟨x, rfl⟩ : _ ∈ rankTwoVertices D.B D.N D.w₁ D.w₂)
    have hx : x * g ∈ ((parabolic D.B D.N {D.w₁} : Subgroup X) : Set X) * {x} * {g} :=
      Set.mem_mul.2 ⟨x, Set.mem_mul.2 ⟨1, (parabolic D.B D.N {D.w₁}).one_mem, x, rfl, one_mul x⟩,
        g, rfl, rfl⟩
    rw [hv] at hx
    obtain ⟨p, hp, y, hy, hpy⟩ := Set.mem_mul.1 hx
    rw [Set.mem_singleton_iff] at hy
    rw [hy] at hpy
    have : x * g * x⁻¹ = p := by rw [← hpy]; group
    rw [this]
    exact hp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.normalCore (parabolic D.B D.N {D.w₁})) with h | h
  · rw [h] at hmem
    exact Subgroup.mem_bot.1 hmem
  · exact absurd (top_le_iff.1 (h ▸ Subgroup.normalCore_le _)) D.parabolic_w₁_ne_top

@[expose] def toSystemOfSimple {X : Type u} [Group X] [IsSimpleGroup X] {n : ℕ}
    (D : PreRankTwoSystem X n) : RankTwoSystem X n :=
  D.toSystem D.faithful_of_isSimpleGroup

end PreRankTwoSystem

end CFSG.GH74.GLS.SP
