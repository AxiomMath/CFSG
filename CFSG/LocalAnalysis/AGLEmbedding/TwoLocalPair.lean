module

public import CFSG.LocalAnalysis.AGLEmbedding.Escape
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

structure TwoLocalPair {G : Type*} [Group G] (M H : Subgroup G) : Prop where
  maxTwoLocal_M : GLBIsMaxTwoLocal M
  maxTwoLocal_H : GLBIsMaxTwoLocal H
  not_le : ¬ H ≤ M
  twoCore_le : pCoreOf 2 H ≤ M

structure TwoLocalPhaseThree {G : Type*} [Group G] (M H : Subgroup G) : Prop
    extends TwoLocalPair M H where
  charTwo_M : CFSG.QuasithinUnique.CharTwo M
  twoCore_inf : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H

theorem D1Escape.toTwoLocalPair {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1Escape p P M H R) : TwoLocalPair M H :=
  ⟨h.maxTwoLocal_M, h.maxTwoLocal_H, h.not_le, h.twoCore_le⟩

namespace TwoLocalPair

variable {G : Type*} [Group G] {M H : Subgroup G}

theorem inf_lt_left (h : TwoLocalPair M H) : H ⊓ M < H :=
  lt_of_le_of_ne inf_le_left fun heq => h.not_le (inf_eq_left.mp heq)

theorem inf_lt_right (h : TwoLocalPair M H) : H ⊓ M < M := by
  refine lt_of_le_of_ne inf_le_right fun heq => h.not_le ?_
  have hMH : M ≤ H := heq ▸ inf_le_left
  exact (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 hMH).le

theorem cgsIn_eq (h : TwoLocalPair M H) :
    CFSG.Quasithin.cgsIn M (pCoreOf 2 H) = M ⊓ H :=
  maxTwoLocal_cgsIn_eq_inf h.maxTwoLocal_H M

theorem normalizer_twoCore_H (h : TwoLocalPair M H) :
    Subgroup.normalizer (pCoreOf 2 H : Set G) = H :=
  (maxTwoLocal_eq_normalizer_pCoreOf H h.maxTwoLocal_H).symm

theorem normalizer_twoCore_M (h : TwoLocalPair M H) :
    Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
  (maxTwoLocal_eq_normalizer_pCoreOf M h.maxTwoLocal_M).symm

theorem twoCore_M_ne (h : TwoLocalPair M H) : pCoreOf 2 M ≠ pCoreOf 2 H := by
  intro heq
  apply h.not_le
  have hMH : M ≤ H := by
    rw [← h.normalizer_twoCore_H, ← heq]
    exact localGroup_le_normalizer_pCoreOf 2 M
  exact (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 hMH).le

theorem inf_eq_inf_normalizer_twoCore_M (h : TwoLocalPair M H) :
    H ⊓ M = H ⊓ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
  rw [h.normalizer_twoCore_M]

theorem twoCore_H_ne_bot (h : TwoLocalPair M H) : pCoreOf 2 H ≠ ⊥ :=
  twoLocal_pCoreOf_ne_bot H h.maxTwoLocal_H.1

theorem not_le_normalizer_of_le_normalizer (h : TwoLocalPair M H) {C : Subgroup G}
    (hC1 : C ≠ ⊥) (hC2 : IsPGroup 2 C) (hHC : H ≤ Subgroup.normalizer (C : Set G)) :
    ¬ M ≤ Subgroup.normalizer (C : Set G) := by
  rw [maxTwoLocal_normalizer_eq_of_le_normalizer h.maxTwoLocal_H hC1 hC2 hHC]
  exact fun hMH => h.not_le (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 hMH).le

theorem not_le_normalizer_of_char (h : TwoLocalPair M H) {C : Subgroup G}
    (hCS : C ≤ pCoreOf 2 H) (hC1 : C ≠ ⊥) (hchar : (C.subgroupOf (pCoreOf 2 H)).Characteristic) :
    ¬ M ≤ Subgroup.normalizer (C : Set G) :=
  h.not_le_normalizer_of_le_normalizer hC1
    ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).to_le hCS)
    (le_normalizer_of_characteristic_pCoreOf hCS hchar)

theorem ne_of_le_normalizer (h : TwoLocalPair M H) {C D : Subgroup G} (hC1 : C ≠ ⊥)
    (hC2 : IsPGroup 2 C) (hHC : H ≤ Subgroup.normalizer (C : Set G))
    (hMD : M ≤ Subgroup.normalizer (D : Set G)) : C ≠ D := by
  rintro rfl
  exact h.not_le_normalizer_of_le_normalizer hC1 hC2 hHC hMD

theorem ne_of_char (h : TwoLocalPair M H) {C D : Subgroup G} (hCS : C ≤ pCoreOf 2 H)
    (hC1 : C ≠ ⊥) (hCchar : (C.subgroupOf (pCoreOf 2 H)).Characteristic)
    (hDQ : D ≤ pCoreOf 2 M) (hDchar : (D.subgroupOf (pCoreOf 2 M)).Characteristic) : C ≠ D := by
  rintro rfl
  exact h.not_le_normalizer_of_char hCS hC1 hCchar
    (le_normalizer_of_characteristic_pCoreOf hDQ hDchar)

end TwoLocalPair

end CFSG.AGLEmbedding
