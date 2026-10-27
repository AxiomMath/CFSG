module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairChain
public import CFSG.Sporadic.Co1Block.TwoBComp

public noncomputable section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Co1Pair

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier Subgroup
open scoped commutatorElement

theorem commutator_eq_top_of_simple {D : Type*} [Group D] [IsSimpleGroup D]
    (hna : ∃ x y : D, x * y ≠ y * x) : commutator D = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator D) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hna
    apply hxy
    have hmem : ⁅x, y⁆ ∈ commutator D := commutator_mem_commutator (mem_top x) (mem_top y)
    rw [h, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.1 hmem
  · exact h

theorem commutator_le_self' {G : Type*} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem perfect_of_map_eq {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (φ : G →* H)
    (K : Subgroup G) (D : Subgroup H) (hmap : K.map φ = D) (hD : ⁅D, D⁆ = D)
    (hle : Nat.card K ≤ Nat.card D) : ⁅K, K⁆ = K ∧ Nat.card K = Nat.card D := by
  have hge : Nat.card D ≤ Nat.card K := by
    rw [← hmap]
    exact Nat.card_le_card_of_surjective _ (φ.subgroupMap_surjective K)
  have hcomm : (⁅K, K⁆).map φ = D := by
    rw [Subgroup.map_commutator, hmap, hD]
  have hge2 : Nat.card D ≤ Nat.card ↥(⁅K, K⁆) := by
    rw [← hcomm]
    exact Nat.card_le_card_of_surjective _ (φ.subgroupMap_surjective ⁅K, K⁆)
  exact ⟨Subgroup.eq_of_le_of_card_ge (commutator_le_self' K) (hle.trans hge2),
    le_antisymm hle hge⟩

section


abbrev px : C₁ := d₂C twoBXY.1

abbrev py : C₁ := d₂C twoBXY.2

abbrev px' : C₁ := px * (px * py) ^ 13

abbrev K₁ : Subgroup C₁ := Subgroup.closure {px', py}

theorem triHom_px' : triHom px' = xBar := by
  have h : (xBar * yBar) ^ 13 = 1 := by
    rw [← orderOf_xyBar]
    exact pow_orderOf_eq_one _
  show triHom (px * (px * py) ^ 13) = xBar
  rw [map_mul, map_pow, map_mul, show triHom px = xBar from rfl, show triHom py = yBar from rfl, h,
    mul_one]

theorem map_K₁ : K₁.map triHom = twoBD := by
  rw [MonoidHom.map_closure, Set.image_pair, triHom_px']

theorem rep_px' : MRep cpX (ιC px') := by
  have hx : MRep twoBXYRows.1 (ιC px) := rep_d₂C _
  have hy : MRep twoBXYRows.2 (ιC py) := rep_d₂C _
  rw [map_mul, map_pow, map_mul]
  exact hx.mul ((hx.mul hy).pow 13)

theorem rep_py : MRep cpY (ιC py) := rep_d₂C _

end

section


theorem card_K₁_le : Nat.card K₁ ≤ Nat.card twoBD := by
  have h1 : K₁.map ιC = Subgroup.closure {ιC px', ιC py} := by
    rw [MonoidHom.map_closure, Set.image_pair]
  have h2 := cpChain_bound rep_px' rep_py
  rw [← h1, Subgroup.card_map_of_injective ιC_injective] at h2
  rw [card_twoBD]
  exact h2

theorem exists_perfect_K₁ : ∃ K : Subgroup C₁, ⁅K, K⁆ = K ∧ Nat.card K = 251596800 := by
  have : IsSimpleGroup ↥twoBD := isSimpleGroup_twoBD
  have hD : ⁅twoBD, twoBD⁆ = twoBD := by
    have hc : commutator ↥twoBD = ⊤ :=
      commutator_eq_top_of_simple (D := ↥twoBD) (hna := ⟨xD, yD, xD_yD_ne⟩)
    rw [← Subgroup.map_subtype_commutator, hc, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨hperf, hcard⟩ := perfect_of_map_eq triHom K₁ twoBD map_K₁ hD card_K₁_le
  exact ⟨K₁, hperf, by rw [hcard, card_twoBD]⟩

end

end CFSG.EvenSporadicStandard.Co1Pair
