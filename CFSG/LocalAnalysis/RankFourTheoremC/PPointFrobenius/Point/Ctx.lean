module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Ctx

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

structure PtPoint (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop where
  p5 : 5 ≤ p
  loc : CFSG.AGLEmbedding.D1Local p P M
  point : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x
  conf : ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → 2 ≤ CFSG.Open.pRank p (H ⊓ M) → H ≤ M
  abel : IsMulCommutative (P : Subgroup G)

@[expose] def PtWeak (p : ℕ) (P : Sylow p G) (x : G) : Prop :=
  ∀ g : G, CFSG.Open.GLBConj g (zpowers x) ≤ (P : Subgroup G) →
    CFSG.Open.GLBConj g (zpowers x) = zpowers x

structure PtLocal (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop extends
    PtPoint p P M x where
  weak : PtWeak p P x

structure PtStruct (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop where
  layer : ∃ (_ : Fact p.Prime) (n : ℕ), 2 ≤ n ∧ Nonempty (layerOf x ≃* PSL(2, GaloisField p n))
  not_le : ¬ layerOf x ≤ M
  cyclic : ∀ S : Subgroup G, S ≤ centralizer ((zpowers x : Subgroup G) : Set G) ⊓
    centralizer ((layerOf x : Subgroup G) : Set G) → IsPGroup p S → IsCyclic S

@[expose] def PtNorm (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop :=
  ∀ P₁ : Subgroup G, P₁ ≤ (P : Subgroup G) → Nat.card P₁ = p → P₁ ≠ zpowers x →
    normalizer (P₁ : Set G) ≤ M

structure PtConclusion (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x : G) : Prop extends
    PtStruct p P M x where
  norm : PtNorm p P M x

theorem ysPPointCentralizers_of_local
    (h : ∀ (G : Type) [Group G] [Finite G], FrobGlobal G → ∀ (p : ℕ) (P : Sylow p G)
      (M : Subgroup G) (x : G), PtLocal p P M x → PtConclusion p P M x) :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointCentralizers := by
  intro G _ _ hs hnab hk hc hr hpre hd1 hfc p P M x hp5 hloc hpt hconf hab hwc
  have hcon := h G ⟨hs, hnab, hk, hc, hr, hpre, hd1, hfc⟩ p P M x
    ⟨⟨hp5, hloc, hpt, hconf, hab⟩, hwc⟩
  exact ⟨⟨hcon.layer, hcon.not_le, hcon.cyclic⟩, hcon.norm⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
