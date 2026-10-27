module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6E8TwoGroup

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Case64E8G : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L : Subgroup G), Sec3SettingLB G t L →
    Asc82Hyp62 G → ∀ (y : G) (X Y T : Subgroup G), orderOf y = 2 → InC X → InFStar X →
      IsL29 X → IsComponentIn Y (centralizer ({y} : Set G)) → X ≤ Y → InCStar Y → InFStar Y →
      IsOmega6Minus Y → IsSylow2Of T (centralizer (X : Set G)) → y ∈ T →
      CFSG.Open.IsElemAbelian 2 (T ⊓ centralizer ({y} : Set G)) →
      Nat.card ↥(T ⊓ centralizer ({y} : Set G)) = 8 →
      Nat.card ↥(T ⊓ centralizer (Y : Set G)) = 2 → T ⊓ centralizer ({y} : Set G) ≠ T →
      CFSG.GH74.sectionalTwoRank T ≤ 3 ∨
        ∃ r : G, r ∈ T ⊓ centralizer ({y} : Set G) ∧ r ∉ Subgroup.zpowers y ∧
          8 < Nat.card ↥(T ⊓ centralizer ({r} : Set G)) ∧
          ∃ K : Subgroup G, K ≤ T ⊓ centralizer ({r} : Set G) ∧ y ∈ K ∧ r ∈ K ∧
            K.relIndex (T ⊓ centralizer ({r} : Set G)) = 2 ∧
            Nat.card ↥(K ⊓ (T ⊓ centralizer ({y} : Set G))) = 4

theorem asc82Case64E8_of_G (h : Asc82Case64E8G) : Asc82Case64E8 := by
  intro G _ _ t L hset hyp y X Y T hy hXC hXF hX29 hYc hXY hYC hYF hY6 hT hyT hab h8 h2 hne
  rcases h G t L hset hyp y X Y T hy hXC hXF hX29 hYc hXY hYC hYF hY6 hT hyT hab h8 h2 hne with
    hrank | ⟨r, hrR, hry, hC8, K, hK, hyK, hrK, hKi, hKR⟩
  · exact hrank
  · exact (m6e8_two_group hT.2.1 hab h8 hrR hry hC8 hK hyK hrK hKi hKR).2

end CFSG.OddStandard.SmallF3.Omega
