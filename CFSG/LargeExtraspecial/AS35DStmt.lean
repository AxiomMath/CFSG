module

public import CFSG.LargeExtraspecial.AS35CSplit
public import CFSG.LargeExtraspecial.S14W4LocB3
public import CFSG.LargeExtraspecial.S14W4LocLeaf

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

@[expose] def zGen : Subgroup G := closure {g : G | IsConj S.z g}

theorem z_mem_zGen : S.z ∈ S.zGen := subset_closure (IsConj.refl S.z)

theorem conj_mem_zGen (g : G) : g * S.z * g⁻¹ ∈ S.zGen :=
  subset_closure (isConj_iff.mpr ⟨g, rfl⟩)

variable [Finite G]

@[expose] def AschTwoAlt : Prop :=
  (∀ l₁ ∈ S.zGen, ∀ l₂ ∈ S.zGen,
      orderOf (l₁ * S.z * l₁⁻¹ * (l₂ * S.z * l₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) ∨
    (S.width = 4 ∧ Nonempty (S.zGen ≃* CFSG.Blueprint.NativeSporadic.Co2))

@[expose] def AschTwo : Prop :=
  IsSimpleGroup S.zGen ∧ centralizer (S.zGen : Set G) = ⊥ ∧ S.AschTwoAlt

@[expose] def AschConcl : Prop :=
  S.z ∈ center G ∨ S.AschTwo ∨ (∃ t ∈ S.QG, orderOf t = 2 ∧ ¬ S.ZInOTwo t) ∨
    ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z

end Setting

namespace S14

@[expose] def AschbacherMainStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), 2 ≤ S.width → S.AschConcl

theorem aschbacherHypCore_of_main (h : AschbacherMainStmt) :
    AschbacherHypCore := by
  intro G _ _ _ S hn hP hW hA g₁ g₂
  have htop : S.zGen = ⊤ := S.closure_conj_eq_top
  rcases h G S (by omega) with h1 | ⟨-, -, h3 | ⟨hw, ⟨e⟩⟩⟩ | ⟨t, htQ, ht2, ht⟩ | ⟨g, hgQ, hgne⟩
  · rw [S.center_eq_bot, mem_bot] at h1
    exact (S.z_ne_one h1).elim
  · exact h3 g₁ (htop ▸ mem_top _) g₂ (htop ▸ mem_top _)
  · exfalso
    rcases hP with h5 | hP
    · omega
    · have hQ : Nat.card S.Q = 2 ^ 9 := by rw [S.card_Q_eq, hw]
      have h1 := W4Loc.factorization_card_le_of hQ hP.card_le
      have e' : G ≃* CFSG.Blueprint.NativeSporadic.Co2 :=
        ((Subgroup.topEquiv (G := G)).symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e
      rw [Nat.card_congr e'.toEquiv, factorization_card_Co2] at h1
      omega
  · refine (ht (hA t htQ ?_)).elim
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  · exact (hgne (hW g hgQ)).elim

end S14

end CFSG.LargeExtraspecial
