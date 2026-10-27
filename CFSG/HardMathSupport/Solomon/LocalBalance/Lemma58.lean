module

public import CFSG.LocalAnalysis.GL83PartI.I_33
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def InputBZeroMaxS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B →
      ∃ D : Subgroup G, IsEkIn 3 2 B D ∧ ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≠ ⊥ ∧
        S ≤ GLADelta 3 D ∧ B ≤ Subgroup.normalizer (S : Set G) ∧ ⁅S, B⁆ = S

variable {G : Type} [Group G] [Finite G]

theorem exists_hyperplane_commutator_ne {B S : Subgroup G} (hB : IsElemAbelian 3 B)
    (hBcard : Nat.card B = 3 ^ 4) (hS2 : IsPGroup 2 S) (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hne : ⁅S, B⁆ ≠ ⊥) :
    ∃ E : Subgroup G, IsEkIn 3 3 B E ∧ ⁅S ⊓ Subgroup.centralizer (E : Set G), B⁆ ≠ ⊥ := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hBne : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBcard
    norm_num at hBcard
  have hgen := GL83.le_iSup_hyperplane hp3 (by norm_num) hBne hB hS2 hBS
  by_contra hcon
  push Not at hcon
  have hle : S ≤ Subgroup.centralizer (B : Set G) := by
    refine hgen.trans (iSup₂_le fun A hA => ?_)
    have hAB : A ≤ B := hA.1
    have hcard : Nat.card A = 3 ^ 3 :=
      CFSG.LocalAnalysis.GLTheoremB.card_eq_of_index_eq hp3 hAB hA.2 hBcard
    have h0 := hcon A ⟨hAB, isElemAbelian_mono hB hAB, hcard⟩
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
    exact h0
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hle

theorem commutator_double_of_two_three {B C : Subgroup G} (hB : IsElemAbelian 3 B)
    (hC2 : IsPGroup 2 C) (hBC : B ≤ Subgroup.normalizer (C : Set G)) :
    ⁅⁅C, B⁆, B⁆ = ⁅C, B⁆ := by
  obtain ⟨n, hn⟩ := hC2.exists_card_eq
  obtain ⟨m, hm⟩ := (GL83.isPGroup_of_isElemAbelian hB).exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card C) := by
    rw [hn, hm]
    exact Nat.Coprime.pow _ _ (by norm_num)
  have : Group.IsNilpotent C := hC2.isNilpotent
  exact GL83.commutator_double_eq_self B C hBC hcop inferInstance

end CFSG.HardMathSupport.Solomon.LocalBalance
