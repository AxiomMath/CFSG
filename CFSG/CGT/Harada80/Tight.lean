module

public import CFSG.CGT.Harada80.Setting
public import CFSG.CGT.Hall82.Tight

public section

namespace CFSG.CGT.Harada80.Setting

open CFSG CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ} (S : Setting G M J m)
include S

theorem eight_le_card_blockU : 8 ≤ Nat.card ↥(blockU J) := by
  have h := Nat.card_le_card_of_surjective _ S.beta_surjective
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
    ZMod.card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  have hm : 2 ≤ m := by rcases S.m_eq with h | h <;> omega
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ (m + (m + 2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ _ := h

theorem inCatalog_or_tight
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hSTT : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight) :
    CFSG.Assembly.InCatalog G ∨ Subgroup.centralizer (J : Set G) = ⊥ ∨
      (pCoreOf 2 (Subgroup.centralizer (J : Set G)) ≠ ⊥ ∧
        (∀ P : Subgroup G, IsPGroup 2 P → P ≤ Subgroup.centralizer (J : Set G) →
          P ≤ pCoreOf 2 (Subgroup.centralizer (J : Set G))) ∧
        ((IsCyclic ↥(pCoreOf 2 (Subgroup.centralizer (J : Set G))) ∧
            Nat.card ↥(pCoreOf 2 (Subgroup.centralizer (J : Set G))) = 4) ∨
          IsElemAbelian 2 (pCoreOf 2 (Subgroup.centralizer (J : Set G)))) ∧
        ∃ g : G, CFSG.CGT.Timmesfeld75.conjSubgroup g
            (pCoreOf 2 (Subgroup.centralizer (J : Set G))) ≤ M ∧
          CFSG.CGT.Timmesfeld75.conjSubgroup g
            (pCoreOf 2 (Subgroup.centralizer (J : Set G))) ≠
            pCoreOf 2 (Subgroup.centralizer (J : Set G))) :=
  CFSG.CGT.Hall82.inCatalog_or_tight hNode hSTT S.simple S.nonab S.kProper S.charTwo S.maxLocal
    S.normalizer_eq S.uniq S.elemU S.eight_le_card_blockU

end CFSG.CGT.Harada80.Setting
