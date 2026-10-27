module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo.SL2Two
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Defs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.G2Pair
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.EvenClass

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer


theorem closure_quadSet_of_pair {G : Type*} [Group G] {x : G} {β : MulAut G}
    (h : Subgroup.closure ((Subgroup.centralizer ({x} : Set G) : Set G) ∪
      (fixedSubgroup β : Set G)) = ⊤) :
    Subgroup.closure (quadSet x β) = ⊤ := by
  rw [eq_top_iff, ← h]
  refine Subgroup.closure_mono ?_
  rintro g (hg | hg)
  · exact Or.inl (Or.inl (Or.inl hg))
  · exact Or.inl (Or.inl (Or.inr hg))

variable {K : Type} [Field K] [Finite K]

theorem gammaP_vu_eq (hK : Nat.card K = 2) :
    gammaP K (vSL 1 * uSL 1) =
      MulAut.conj (sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1 * uSL 1)) * gammaP K (uSL 1 * vSL 1) *
        (MulAut.conj (sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1 * uSL 1)))⁻¹ := by
  rw [conj_gammaP, conj_w_uv hK]

theorem ringChar_eq_two_of_card_two (hK : Nat.card K = 2) : ringChar K = 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  exact (FiniteField.even_card_iff_char_two (F := K)).2 (by rw [hc])

theorem closure_quadSet_of_isA2 (hK : Nat.card K = 2) (hA2 : QuadGenTwoA2)
    {x : ↥(adjointGroup Tag.D4 K)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {β : MulAut ↥(adjointGroup Tag.D4 K)} (hβx : β x = x) (ψ : MulAut ↥(adjointGroup Tag.D4 K))
    {B : SL2 K} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1)
    (hψ : ψ * β * ψ⁻¹ = gammaP K B ∨ ψ * β * ψ⁻¹ = (gammaP K B)⁻¹) :
    Subgroup.closure (quadSet x β) = ⊤ := by
  have hfix' : (ψ * β * ψ⁻¹) (ψ x) = ψ x := mem_fixedSubgroup_conj ψ β hβx
  have hfix : gammaP K B (ψ x) = ψ x := by
    rcases hψ with h | h
    · rwa [h] at hfix'
    · rw [h] at hfix'
      have := congrArg (gammaP K B) hfix'
      rwa [MulAut.apply_inv_self, eq_comm] at this
  have hquad : quadSet (ψ x) (ψ * β * ψ⁻¹) = quadSet (ψ x) (gammaP K B) := by
    rcases hψ with h | h
    · rw [h]
    · rw [h, quadSet_inv hfix]
  have hx'3 : (ψ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have hx'1 : ψ x ≠ 1 := fun h => hx1 (by rw [← MulAut.inv_apply_self _ ψ x, h, map_one])
  refine closure_quadSet_eq_top_of_conj ψ ?_
  rw [hquad]
  rcases sl2_eq_uv_or_vu hK B hB3 hB1 with rfl | rfl
  · exact hA2 K hK (ψ x) hx'3 hx'1 hfix
  · set n := sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1 * uSL 1)
    rw [gammaP_vu_eq hK] at hfix ⊢
    refine closure_quadSet_eq_top_of_conj (MulAut.conj n)⁻¹ ?_
    have e : (MulAut.conj n)⁻¹ * (MulAut.conj n * gammaP K (uSL 1 * vSL 1) * (MulAut.conj n)⁻¹) *
        (MulAut.conj n)⁻¹⁻¹ = gammaP K (uSL 1 * vSL 1) := by group
    rw [e]
    have hfix2 := mem_fixedSubgroup_conj (MulAut.conj n)⁻¹ _ hfix
    rw [e] at hfix2
    refine hA2 K hK _ (by rw [← map_pow, hx'3, map_one]) ?_ hfix2
    intro h
    exact hx'1 ((MulAut.conj n)⁻¹.injective (h.trans (map_one _).symm))

theorem d4GraphPlanesTwo_of (hG2 : PairGenTwoG2) (hA2 : QuadGenTwoA2) : D4GraphPlanesTwo := by
  intro K _ _ hK2 E hE hc hout hG
  classical
  haveI : CFSG.IsElementaryAbelian 3 ↥E := hE
  have hchar : ringChar K = 2 := ringChar_eq_two_of_card_two hK2
  have hinj := conj_injective_D4 (K := K)
  obtain ⟨β, hβE, hβout⟩ : ∃ β ∈ E, β ∉ innerAut (adjointGroup Tag.D4 K) := by
    by_contra hcon
    push Not at hcon
    exact hout hcon
  have hβ1 : β ≠ 1 := fun h' => hβout (h' ▸ one_mem _)
  obtain ⟨g, a, σ, ε, hε, hσ3, ⟨hε0, hσ1⟩, hβeq⟩ := hG β hβE hβout
  subst hσ1
  obtain ⟨ι, hιE, hι1, hιin⟩ :=
    exists_inner_ne_one_of_graph hc hG hβE (by omega) ⟨g, a, hβeq⟩
  obtain ⟨x, rfl⟩ := hιin
  have hι3 : MulAut.conj x ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian _ hιE
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hι3, map_one])
  have hx1 : x ≠ 1 := fun h' => hι1 (by rw [h', map_one])
  have hβx : β x = x := by
    have h1 := CFSG.RankThree.PartTwo.Sec19.elemAb_comm hE _ hβE _ hιE
    have h2 : β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
      ext y
      simp [MulAut.mul_apply, MulAut.conj_apply]
    apply hinj
    rw [← h2, h1, mul_inv_cancel_right]
  have hxβ1 : MulAut.conj x * β ≠ 1 := by
    intro h
    apply hβout
    refine ⟨x⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right h).symm
  have hxβ1' : (MulAut.conj x)⁻¹ * β ≠ 1 := by
    intro h
    apply hβout
    refine ⟨x, ?_⟩
    rw [eq_inv_of_mul_eq_one_right h, inv_inv]
  suffices h : Subgroup.closure (quadSet x β) = ⊤ by
    rw [eq_top_iff, ← h]
    exact Subgroup.closure_mono (quadSet_subset_fixUnion hιE hβE hι1 hβ1 hxβ1 hxβ1')
  have hβ3 : β ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβE
  rcases isG2Type_or_isA2Type_of_charTwo K hchar β hβ3
      ⟨g, a, 1, ε, hε, hσ3, ⟨hε0, rfl⟩, hβeq⟩ with ⟨ψ, h | h⟩ | ⟨ψ, B, hB3, hB1, hψ⟩
  · exact closure_quadSet_of_pair (pairGenAt_of_conj_eq ψ (hG2 K hK2) (Or.inl h) x hx3 hx1 hβx)
  · exact closure_quadSet_of_pair (pairGenAt_of_conj_eq ψ
      (pairGenAt_congr fixedSubgroup_d4Graph_two.symm (hG2 K hK2)) (Or.inl h) x hx3 hx1 hβx)
  · exact closure_quadSet_of_isA2 hK2 hA2 hx3 hx1 hβx ψ hB3 hB1 hψ

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.PlanesTwo
