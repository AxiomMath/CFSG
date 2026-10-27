module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieEngine
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2

public section

namespace CFSG.QuasithinUnique.B113Lie.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239.Lie
open CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem overgroup_le_parabolic
    (A : Subgroup (ModGL Tag.G2 K))
    (hUA : posUnipotent Tag.G2 K ≤ A) (hAC : A ≤ adjointGroup Tag.G2 K)
    (hAne : A ≠ adjointGroup Tag.G2 K) :
    A ≤ parabolicSubgroup Tag.G2 K {i0} ∨ A ≤ parabolicSubgroup Tag.G2 K {i1} := by
  obtain ⟨J, hJ, hAJ, -⟩ :=
    (chevalley_positive_root_overgroup_parabolic_containment hAC hUA).2.2 hAne
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra h
    exact hJ (Set.eq_univ_of_forall fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  rcases fin_two_cases i with rfl | rfl
  · right
    refine hAJ.trans (parabolicSubgroup_le_parabolicSubgroup_iff.2 fun j hj => ?_)
    rcases fin_two_cases j with rfl | rfl
    · exact absurd hj hi
    · exact Set.mem_singleton _
  · left
    refine hAJ.trans (parabolicSubgroup_le_parabolicSubgroup_iff.2 fun j hj => ?_)
    rcases fin_two_cases j with rfl | rfl
    · exact Set.mem_singleton _
    · exact absurd hj hi

theorem parabolicData
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    ParabolicData ↥(adjointGroup Tag.G2 K)
      ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K))
      {(parabolicSubgroup Tag.G2 K {i0}).subgroupOf (adjointGroup Tag.G2 K),
        (parabolicSubgroup Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K)} := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨h0ne, h1ne, hgen⟩ := parabolics_proper_generate (K := K)
  set C := adjointGroup Tag.G2 K with hC
  have hP₀C : parabolicSubgroup Tag.G2 K {i0} ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hP₁C : parabolicSubgroup Tag.G2 K {i1} ≤ C := parabolicSubgroup_le_adjointGroup _ _ _
  have hQ₀C : parabolicRadical Tag.G2 K {i0} ≤ C :=
    ((parabolicRadical_le_posUnipotent {i0}).trans
      (posUnipotent_le_parabolicSubgroup {i0})).trans hP₀C
  have hQ₁C : parabolicRadical Tag.G2 K {i1} ≤ C :=
    ((parabolicRadical_le_posUnipotent {i1}).trans
      (posUnipotent_le_parabolicSubgroup {i1})).trans hP₁C
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (posUnipotent Tag.G2 K) C :=
    isSylowTwoOf_iff_isSylowOf.2 (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1
  refine ParabolicData.of_ambient_pair hUsyl (posUnipotent_le_parabolicSubgroup {i0})
    (posUnipotent_le_parabolicSubgroup {i1}) hP₀C hP₁C h0ne h1ne hgen
    (fun A hUA hAC hAne => overgroup_le_parabolic A hUA hAC hAne) ?_ ?_
    (fun α hα => ⟨G2_invariant_parabolic hK4 hα i0, G2_invariant_parabolic hK4 hα i1⟩)
  · refine (ParabolicFacts.of_map (Q := (parabolicRadical Tag.G2 K {i0}).subgroupOf C)
      C.subtype C.subtype_injective ?_).charTwo
    rw [Subgroup.map_subgroupOf_eq_of_le hP₀C, Subgroup.map_subgroupOf_eq_of_le hQ₀C]
    exact parabolicFacts_zero hK hf
  · refine (ParabolicFacts.of_map (Q := (parabolicRadical Tag.G2 K {i1}).subgroupOf C)
      C.subtype C.subtype_injective ?_).charTwo
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁C, Subgroup.map_subgroupOf_eq_of_le hQ₁C]
    exact parabolicFacts_one hK hf

end CFSG.QuasithinUnique.B113Lie.G2

namespace CFSG.QuasithinUnique.B113Lie

open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X6

theorem g2_sylowFacts
    {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : ChevalleyExceptionalModel S .G2 2 f) {T : Subgroup S} (hT : IsSylowTwoOf T ⊤) :
    SylowFacts S T := by
  obtain ⟨hf, K, hF, hFin, hcp, hK, ⟨e⟩⟩ := exists_mulEquiv_G2_model h
  have : Finite (CFSG.Blueprint.Chevalley.ModGL CFSG.Blueprint.Chevalley.Tag.G2 K) :=
    CFSG.LieType.Chevalley.finite_modGL
  exact SylowFacts.of_mulEquiv_isSylow e (G2.parabolicData hK hf).sylowFacts hT

end CFSG.QuasithinUnique.B113Lie
