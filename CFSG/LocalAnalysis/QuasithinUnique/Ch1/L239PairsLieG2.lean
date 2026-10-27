module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem parabolics_proper_generate
    :
    parabolicSubgroup Tag.G2 K {i0} ≠ adjointGroup Tag.G2 K ∧
      parabolicSubgroup Tag.G2 K {i1} ≠ adjointGroup Tag.G2 K ∧
      parabolicSubgroup Tag.G2 K {i0} ⊔ parabolicSubgroup Tag.G2 K {i1} =
        adjointGroup Tag.G2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  set C := adjointGroup Tag.G2 K with hC
  obtain ⟨hcov, hinj, -⟩ := exceptional_ordinary_minimal_Borel_intersections Tag.G2 K
  have hcases : ∀ i : Fin Tag.G2.rank, i = i0 ∨ i = i1 := fin_two_cases
  have hcov' : ∀ A : Subgroup (ModGL Tag.G2 K), A ≤ C →
      (borelGroup Tag.G2 K ⋖ A ↔
        A = parabolicSubgroup Tag.G2 K {i0} ∨ A = parabolicSubgroup Tag.G2 K {i1}) := by
    intro A hA
    rw [hcov A hA]
    constructor
    · rintro ⟨i, rfl⟩
      rcases hcases i with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (h | h)
      · exact ⟨_, h⟩
      · exact ⟨_, h⟩
  set P₀ := parabolicSubgroup Tag.G2 K {i0} with hP₀
  set P₁ := parabolicSubgroup Tag.G2 K {i1} with hP₁
  have hP₀C : P₀ ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hP₁C : P₁ ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hne : P₀ ≠ P₁ := fun h => by
    have := @hinj i0 i1 h
    exact absurd this (by decide)
  have hcov₀ : borelGroup Tag.G2 K ⋖ P₀ := (hcov' P₀ hP₀C).2 (Or.inl rfl)
  have hcov₁ : borelGroup Tag.G2 K ⋖ P₁ := (hcov' P₁ hP₁C).2 (Or.inr rfl)
  have hP₀ne : P₀ ≠ C := fun h =>
    hcov₀.2 hcov₁.lt (lt_of_le_of_ne (hP₁C.trans_eq h.symm) hne.symm)
  have hP₁ne : P₁ ≠ C := fun h => hcov₁.2 hcov₀.lt (lt_of_le_of_ne (hP₀C.trans_eq h.symm) hne)
  have hgen : P₀ ⊔ P₁ = C := by
    refine le_antisymm (sup_le hP₀C hP₁C) ?_
    rw [hC, ← (standard_parabolic_cells Tag.G2 K).2.2.2.2.2.1]
    refine sup_le (le_sup_of_le_left (borelGroup_le_parabolicSubgroup _))
      ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨j, -, rfl⟩
    rcases hcases j with rfl | rfl
    · exact Subgroup.mem_sup_left (weylElt_mem_parabolicSubgroup (Set.mem_singleton _))
    · exact Subgroup.mem_sup_right (weylElt_mem_parabolicSubgroup (Set.mem_singleton _))
  exact ⟨hP₀ne, hP₁ne, hgen⟩

theorem hasParabolicPair
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    HasParabolicPair ↥(adjointGroup Tag.G2 K)
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨h0ne, h1ne, hgen⟩ := parabolics_proper_generate (K := K)
  set C := adjointGroup Tag.G2 K with hC
  have hP₀C : parabolicSubgroup Tag.G2 K {i0} ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hP₁C : parabolicSubgroup Tag.G2 K {i1} ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hQ₀C : parabolicRadical Tag.G2 K {i0} ≤ C :=
    ((parabolicRadical_le_posUnipotent {i0}).trans (posUnipotent_le_parabolicSubgroup {i0})).trans hP₀C
  have hQ₁C : parabolicRadical Tag.G2 K {i1} ≤ C :=
    ((parabolicRadical_le_posUnipotent {i1}).trans (posUnipotent_le_parabolicSubgroup {i1})).trans hP₁C
  refine ⟨(parabolicSubgroup Tag.G2 K {i0}).subgroupOf C,
    (parabolicSubgroup Tag.G2 K {i1}).subgroupOf C, ?_, ?_, ?_, ?_,
    ⟨(parabolicRadical Tag.G2 K {i0}).subgroupOf C, ?_⟩,
    ⟨(parabolicRadical Tag.G2 K {i1}).subgroupOf C, ?_⟩⟩
  · intro h
    exact h0ne (le_antisymm hP₀C (Subgroup.subgroupOf_eq_top.1 h))
  · intro h
    exact h1ne (le_antisymm hP₁C (Subgroup.subgroupOf_eq_top.1 h))
  · apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hP₀C,
      Subgroup.map_subgroupOf_eq_of_le hP₁C, hgen, Subgroup.map_top, Subgroup.range_subtype]
  · intro α hα
    exact ⟨G2_invariant_parabolic hK4 hα i0, G2_invariant_parabolic hK4 hα i1⟩
  · refine ParabolicFacts.of_map C.subtype C.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀C, Subgroup.map_subgroupOf_eq_of_le hQ₀C]
    exact parabolicFacts_zero hK hf
  · refine ParabolicFacts.of_map C.subtype C.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁C, Subgroup.map_subgroupOf_eq_of_le hQ₁C]
    exact parabolicFacts_one hK hf

end CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6

theorem pairsFor_G2
    : PairsFor TypeG2 := by
  intro G _ _ L R _ hty _ hRN hS
  obtain ⟨f, hf, hmod⟩ := hty
  obtain ⟨hf2, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) ⊤ :=
    isSylowTwoOf_subgroupOf_top (isSylowTwoOf_iff_isSylowOf.2
      (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1)
  exact pairConclusion_of_hasParabolicPair e hU₀ (G2.hasParabolicPair hK hf2) hRN hS

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
