module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open CFSG.QuasithinUnique.Setup.X6

section Covers

variable (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime]

theorem largeRee_named_covers
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.QuasithinUnique.IsSylowTwoOf
        ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) ⊤ ∧
      (∀ A : Subgroup ↥(F4.reeGamma K a),
        Subgroup.normalizer (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :
            Subgroup _) : Set _) ⋖ A ↔
          A = (F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a) ∨
            A = (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) ∧
      (F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a) ≠ ⊤ ∧
      (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a) ≠ ⊤ ∧
      (F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a) ⊔
          (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a) = ⊤ ∧
      (Subgroup.normalizer (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :
            Subgroup _) : Set _)).relIndex
          ((F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a)) =
        Nat.card K + 1 ∧
      (Subgroup.normalizer (((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a) :
            Subgroup _) : Set _)).relIndex
          ((F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) =
        Nat.card K ^ 2 + 1 := by
  classical
  have : Finite (ModGL F4.tag K) := finite_modGL
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem F4.tag).length
  have hUC : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := reeFixedPosUnipotent_le_reeGamma
  obtain ⟨PU, hPU⟩ := (large_Ree_Sylow_opposition F4 a K w₀ hw₀).1
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (F4.reeFixedPosUnipotent K a)
      (F4.reeGamma K a) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hBnorm : F4.reeGamma K a ⊓
      Subgroup.normalizer (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) =
        F4.reeFixedBorel K a :=
    reeGamma_inf_normalizer_reeFixedPosUnipotent
  obtain ⟨hmin, hne, -⟩ := large_Ree_minimal_Borel_intersections a K w₀ hw₀
  have hP₀Γ : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hP₁Γ : F4.reeLocalParabolic K a ⟨1, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hcov : ∀ A : Subgroup (ModGL F4.tag K), A ≤ F4.reeGamma K a →
      (F4.reeFixedBorel K a ⋖ A ↔ A = F4.reeLocalParabolic K a ⟨0, by decide⟩ ∨
        A = F4.reeLocalParabolic K a ⟨1, by decide⟩) := by
    intro A hA
    rw [covBy_iff_minimal_of_le hA]
    exact hmin A
  have hcov₀ : F4.reeFixedBorel K a ⋖ F4.reeLocalParabolic K a ⟨0, by decide⟩ :=
    (hcov _ hP₀Γ).2 (Or.inl rfl)
  have hcov₁ : F4.reeFixedBorel K a ⋖ F4.reeLocalParabolic K a ⟨1, by decide⟩ :=
    (hcov _ hP₁Γ).2 (Or.inr rfl)
  have hP₀ne : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≠ F4.reeGamma K a := fun h =>
    hcov₀.2 hcov₁.lt (lt_of_le_of_ne (hP₁Γ.trans_eq h.symm) hne.symm)
  have hP₁ne : F4.reeLocalParabolic K a ⟨1, by decide⟩ ≠ F4.reeGamma K a := fun h =>
    hcov₁.2 hcov₀.lt (lt_of_le_of_ne (hP₀Γ.trans_eq h.symm) hne)
  have hgen : F4.reeLocalParabolic K a ⟨0, by decide⟩ ⊔ F4.reeLocalParabolic K a ⟨1, by decide⟩ =
      F4.reeGamma K a := by
    refine le_antisymm (sup_le hP₀Γ hP₁Γ) ?_
    have h := (large_Ree_simple_pair_generation a K hK).le
    exact h.trans (sup_le_sup (large_Ree_local_block_Sylow_action F4 a K ⟨0, by decide⟩).1
      (large_Ree_local_block_Sylow_action F4 a K ⟨1, by decide⟩).1)
  have hrel : ∀ j : Fin F4.fixedOrbitCount, (F4.reeFixedBorel K a).relIndex
      (F4.reeLocalParabolic K a j) = Nat.card (F4.reeFixedOrbitUnipotent K a j) + 1 := by
    intro j
    rw [← ncard_image_coset_eq_relIndex]
    exact (large_Ree_local_block_Sylow_action F4 a K j).2.2.2.2.1
  have hi₀ : (F4.reeFixedBorel K a).relIndex (F4.reeLocalParabolic K a ⟨0, by decide⟩) =
      Nat.card K + 1 := by
    rw [hrel, card_reeFixedOrbitUnipotent_zero hK]
  have hi₁ : (F4.reeFixedBorel K a).relIndex (F4.reeLocalParabolic K a ⟨1, by decide⟩) =
      Nat.card K ^ 2 + 1 := by
    rw [hrel, card_reeFixedOrbitUnipotent_one hK]
  obtain ⟨hc, hn₁, hn₂, hg, hnorm⟩ := ambient_covers_data hUsyl.1 hBnorm hcov hP₀Γ hP₁Γ hP₀ne
    hP₁ne hgen
  refine ⟨isSylowTwoOf_subgroupOf_top hUsyl, hc, hn₁, hn₂, hg, ?_, ?_⟩
  · rw [hnorm, Subgroup.relIndex_subgroupOf hP₀Γ]; exact hi₀
  · rw [hnorm, Subgroup.relIndex_subgroupOf hP₁Γ]; exact hi₁

end Covers

section Pair

variable (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime]

theorem hasParabolicPair_of_facts
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    (h₀ : ParabolicFacts (F4.reeLocalParabolic K a ⟨0, by decide⟩)
      (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩))
    (h₁ : ParabolicFacts (F4.reeLocalParabolic K a ⟨1, by decide⟩)
      (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩)) :
    HasParabolicPair ↥(F4.reeGamma K a)
      ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) := by
  obtain ⟨-, hcov, hn₀, hn₁, hgen, hi₀, hi₁⟩ := largeRee_named_covers a K hK
  have hq : 2 ≤ Nat.card K := by
    rw [hK]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne : Nat.card K + 1 ≠ Nat.card K ^ 2 + 1 := by
    intro h
    have h1 : Nat.card K = Nat.card K ^ 2 := Nat.add_right_cancel h
    nlinarith
  have hinv := D4.invariant_of_unequal_covers hcov (by rw [hi₀, hi₁]; exact hne)
  have hP₀Γ : F4.reeLocalParabolic K a ⟨0, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hP₁Γ : F4.reeLocalParabolic K a ⟨1, by decide⟩ ≤ F4.reeGamma K a := inf_le_left
  have hQ₀Γ : F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩ ≤ F4.reeGamma K a :=
    inf_le_right
  have hQ₁Γ : F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩ ≤ F4.reeGamma K a :=
    inf_le_right
  refine ⟨(F4.reeLocalParabolic K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a),
    (F4.reeLocalParabolic K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a), hn₀, hn₁, hgen, hinv,
    ⟨(F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩).subgroupOf (F4.reeGamma K a), ?_⟩,
    ⟨(F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a), ?_⟩⟩
  · refine ParabolicFacts.of_map (F4.reeGamma K a).subtype (F4.reeGamma K a).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀Γ, Subgroup.map_subgroupOf_eq_of_le hQ₀Γ]
    exact h₀
  · refine ParabolicFacts.of_map (F4.reeGamma K a).subtype (F4.reeGamma K a).subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁Γ, Subgroup.map_subgroupOf_eq_of_le hQ₁Γ]
    exact h₁

end Pair

@[expose] def LargeReeParabolicFacts :
    Prop :=
  ∀ (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime],
    1 ≤ a → Nat.card K = 2 ^ (2 * a + 1) →
      ParabolicFacts (F4.reeLocalParabolic K a ⟨0, by decide⟩)
        (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩) ∧
      ParabolicFacts (F4.reeLocalParabolic K a ⟨1, by decide⟩)
        (F4.reeFixedOrbitComplementUnipotent K a ⟨1, by decide⟩)

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.QuasithinUnique.Setup.X6

theorem pairsFor_2F4_of_facts
    (H : F4.LargeReeParabolicFacts) : PairsFor Type2F4 := by
  intro G _ _ L R _ hty _ hRN hS
  obtain ⟨f, -, -, hmod⟩ := hty
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ := exists_mulEquiv_largeRee_model hmod
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨h₀, h₁⟩ := H a K ha hK'
  exact pairConclusion_of_hasParabolicPair e (F4.largeRee_named_covers a K hK').1
    (F4.hasParabolicPair_of_facts a K hK' ha h₀ h₁) hRN hS

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
