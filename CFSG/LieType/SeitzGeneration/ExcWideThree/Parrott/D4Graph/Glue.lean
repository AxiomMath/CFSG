module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.G2Pair
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.EvenClass

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.Fischer CFSG.RankThree.PartTwo.Sec19
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)


theorem closure_fixUnion_of_pairGenAt {K : Type} [Field K] [Finite K]
    {E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} (hE : CFSG.IsElementaryAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hout : ¬ E ≤ innerAut (adjointGroup Tag.D4 K))
    (hG : ∀ α ∈ E, α ∉ innerAut (adjointGroup Tag.D4 K) →
      D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1)
    (hP : ∀ β ∈ E, β ∉ innerAut (adjointGroup Tag.D4 K) → PairGenAt β) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  classical
  haveI : CFSG.IsElementaryAbelian 3 ↥E := hE
  have hZ : Subgroup.center ↥(adjointGroup Tag.D4 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgc : g ∈ Subgroup.center ↥(adjointGroup Tag.D4 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => φ y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g = g * (g⁻¹ * y * g) := by group
        _ = g * y := by
          have h2 : g * y * g⁻¹ = y := this
          have h3 : g⁻¹ * y * g = y := by
            calc g⁻¹ * y * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [h2]
              _ = y := by group
          rw [h3]
    rw [hZ] at hgc
    exact hgc
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E, β ∉ innerAut (adjointGroup Tag.D4 K) := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have hβ1 : β ≠ 1 := fun h' => hβout (h' ▸ one_mem _)
  obtain ⟨g, a, σ, ε, hε, hσ3, ⟨hε0, hσ1⟩, hβeq⟩ := hG β hβE hβout
  subst hσ1
  have hβNF : HasNF β ε 1 := ⟨g, a, hβeq⟩
  obtain ⟨ι, hιE, hι1, hιin⟩ := exists_inner_ne_one_of_graph hc hG hβE (by omega) hβNF
  obtain ⟨x, rfl⟩ := hιin
  have hι3 : MulAut.conj x ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian _ hιE
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hι3, map_one])
  have hx1 : x ≠ 1 := fun h' => hι1 (by rw [h', map_one])
  have hβx : β x = x := by
    have h1 := elemAb_comm hE _ hβE _ hιE
    have h2 : β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply]
    apply hinj
    rw [← h2, h1, mul_inv_cancel_right]
  have hpair := hP β hβE hβout x hx3 hx1 hβx
  rw [eq_top_iff]
  rw [eq_top_iff] at hpair
  refine hpair.trans (Subgroup.closure_le _ |>.2 ?_)
  rintro w (hw | hw)
  · refine Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hιE hι1 ?_)
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hw
    show x * w * x⁻¹ = w
    rw [← h1, mul_inv_cancel_right]
  · exact Subgroup.subset_closure (fixedSubgroup_subset_fixUnion hβE hβ1 hw)

theorem four_le_card_of_five_le_char {K : Type} [Field K] [Finite K] (h : 5 ≤ ringChar K) :
    4 ≤ Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hpr, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hn]
  calc 4 ≤ ringChar K := by omega
    _ = ringChar K ^ 1 := (pow_one _).symm
    _ ≤ ringChar K ^ (n : ℕ) := Nat.pow_le_pow_right hpr.pos n.pos

theorem four_le_card_of_char_two {K : Type} [Field K] [Finite K] (h : ringChar K = 2)
    (h2 : Nat.card K ≠ 2) : 4 ≤ Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hn, h] at h2 ⊢
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra hlt
    have : (n : ℕ) = 1 := by have := n.pos; omega
    rw [this, pow_one] at h2
    exact h2 rfl
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2

theorem pairGenAt_of_type {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) (hA : D4GraphA2PairGen) {α : MulAut ↥(adjointGroup Tag.D4 K)}
    (hα : IsG2Type α ∨ IsA2Type α) : PairGenAt α := by
  rcases hα with hG2 | ⟨ψ, B, hB3, hB1, h⟩
  · exact pairGenAt_of_isG2Type hK3 hK4 hG2
  · exact pairGenAt_of_conj_eq ψ (hA K hK3 hK4 B hB3 hB1) h

theorem d4GraphPairGen_of (hC : D4GraphClassOdd) (hA : D4GraphA2PairGen) : D4GraphPairGen := by
  intro K _ _ hK5 α hα3 hαT
  have hK3 : ringChar K ≠ 3 := by omega
  exact pairGenAt_of_type hK3 (four_le_card_of_five_le_char hK5) hA (hC K hK5 α hα3 hαT)

theorem d4ThreeGraphPlanesEven_of (hA : D4GraphA2PairGen)
    (h2 : D4GraphPlanesTwo) : D4ThreeGraphPlanesEven := by
  have hC := isG2Type_or_isA2Type_of_charTwo
  intro K _ _ hK2 E hE hc hout hG
  by_cases hcard : Nat.card K = 2
  · exact h2 K hcard E hE hc hout hG
  have hK4 := four_le_card_of_char_two hK2 hcard
  have hK3 : ringChar K ≠ 3 := by omega
  refine closure_fixUnion_of_pairGenAt hE hc hout hG fun β hβE hβout => ?_
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβE
  exact pairGenAt_of_type hK3 hK4 hA (hC K hK2 β hβ3 (hG β hβE hβout))

theorem d4ThreeGraphPlanesEven_of_open (hA : D4GraphA2PairGen) (h2 : D4GraphPlanesTwo) :
    D4ThreeGraphPlanesEven :=
  d4ThreeGraphPlanesEven_of hA h2

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
