module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches
public import CFSG.LocalAnalysis.EvenSmallLie.Children

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint

theorem SeitzSetting.standardSetting {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : SeitzSetting G L) : CFSG.EvenSmallLie.StandardSetting G L := by
  obtain ⟨hsimple, hnonab, hK, hL, hcore, hcyc, -⟩ := h
  exact ⟨hsimple, hnonab, hK, hL, hcore, hcyc⟩

theorem SeitzSetting.center_eq_bot {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : SeitzSetting G L) : Subgroup.center L = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, hZ⟩ := h
  exact hZ

theorem SeitzSetting.not_exception {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : SeitzSetting G L) : ¬ Recognition.Exact.EvenStandardException L := by
  obtain ⟨-, -, -, -, -, -, -, hexc, hZ⟩ := h
  exact fun hE =>
    hexc (exactEvenStandardException_of_mulEquiv (quotientCenterMulEquiv hZ).symm hE)

@[expose] def SeitzExclusion (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L → ¬ P L

@[expose] def HighPSL (X : Type) [Group X] : Prop :=
  ∃ n f : ℕ, 4 ≤ n ∧ (n, f) ≠ (4, 1) ∧ LieModel X .PSL n 2 f

@[expose] def HighPSU (X : Type) [Group X] : Prop :=
  ∃ n f : ℕ, 6 ≤ n ∧ (n, f) ≠ (6, 1) ∧ LieModel X .PSU n 2 f

@[expose] def HighPSp (X : Type) [Group X] : Prop :=
  ∃ n f : ℕ, 3 ≤ n ∧ (n, f) ≠ (3, 1) ∧ LieModel X .PSp n 2 f

@[expose] def HighPOmegaPlus (X : Type) [Group X] : Prop :=
  ∃ n f : ℕ, 4 ≤ n ∧ (n, f) ≠ (4, 1) ∧ LieModel X .POmegaPlus n 2 f

@[expose] def HighPOmegaMinus (X : Type) [Group X] : Prop :=
  ∃ n f : ℕ, 4 ≤ n ∧ (n, f) ≠ (4, 1) ∧ LieModel X .POmegaMinus n 2 f

@[expose] def HighExceptional (t : Assembly.LowTwoRank.StatedLieTag) (X : Type) [Group X] :
    Prop :=
  ∃ f : ℕ, LieModel X t 0 2 f

@[expose] def RankOneL2 (X : Type) [Group X] : Prop := ∃ f : ℕ, 3 ≤ f ∧ LieModel X .PSL 2 2 f

@[expose] def RankOneU3 (X : Type) [Group X] : Prop := ∃ f : ℕ, 2 ≤ f ∧ LieModel X .PSU 3 2 f

@[expose] def RankOneSz (X : Type) [Group X] : Prop := ∃ f : ℕ, LieModel X .twistedB2 0 2 f

theorem seitzHighRankExclusion_of_families (hL : SeitzExclusion HighPSL)
    (hU : SeitzExclusion HighPSU) (hS : SeitzExclusion HighPSp)
    (hOp : SeitzExclusion HighPOmegaPlus) (hOm : SeitzExclusion HighPOmegaMinus)
    (hF4 : SeitzExclusion (HighExceptional .F4)) (hE6 : SeitzExclusion (HighExceptional .E6))
    (hE7 : SeitzExclusion (HighExceptional .E7)) (hE8 : SeitzExclusion (HighExceptional .E8))
    (h2E6 : SeitzExclusion (HighExceptional .twistedE6)) : SeitzHighRankExclusion := by
  rintro G _ _ L hset ⟨t, n, f, hm, h⟩
  rcases h with ⟨rfl, hn, hnf⟩ | ⟨rfl, hn, hnf⟩ | ⟨rfl, hn, hnf⟩ | ⟨rfl | rfl, hn, hnf⟩ |
    ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩
  · exact hL G L hset ⟨n, f, hn, hnf, hm⟩
  · exact hU G L hset ⟨n, f, hn, hnf, hm⟩
  · exact hS G L hset ⟨n, f, hn, hnf, hm⟩
  · exact hOp G L hset ⟨n, f, hn, hnf, hm⟩
  · exact hOm G L hset ⟨n, f, hn, hnf, hm⟩
  · exact hF4 G L hset ⟨f, hm⟩
  · exact hE6 G L hset ⟨f, hm⟩
  · exact hE7 G L hset ⟨f, hm⟩
  · exact hE8 G L hset ⟨f, hm⟩
  · exact h2E6 G L hset ⟨f, hm⟩

theorem seitzRankOneExclusion_of_families (hL : SeitzExclusion RankOneL2)
    (hU : SeitzExclusion RankOneU3) (hSz : SeitzExclusion RankOneSz) :
    SeitzRankOneExclusion := by
  rintro G _ _ L hset (h | h | h)
  · exact hL G L hset h
  · exact hU G L hset h
  · exact hSz G L hset h

@[expose] def tagOf : Assembly.LowTwoRank.StatedLieTag → Blueprint.Chevalley.Tag
  | .G2 => .G2
  | .F4 => .F4
  | .E6 => .E6
  | .E7 => .E7
  | _ => .E8

theorem exists_mulEquiv_adjointQuotient_of_lieModel {X : Type} [Group X]
    {t : Assembly.LowTwoRank.StatedLieTag} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    {f : ℕ} (h : LieModel X t 0 2 f) :
    1 ≤ f ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (X ≃* AdjointQuotient (tagOf t) K) := by
  rcases h with ⟨hcl, -⟩ | ⟨-, -, ⟨-, hf, -⟩, hm⟩ | ⟨-, hrt, -⟩ | ⟨-, hsz, -⟩
  · rcases ht with rfl | rfl | rfl | rfl <;> simp [classicalTags] at hcl
  · rcases ht with rfl | rfl | rfl | rfl <;> exact ⟨hf, hm⟩
  · rcases ht with rfl | rfl | rfl | rfl <;> simp [reeTitsTags] at hrt
  · rcases ht with rfl | rfl | rfl | rfl <;> cases hsz

end CFSG.SeitzReduction
