module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166E6FourComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Iso

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std

section Certs


theorem exists_concl166S_adjointGroup_E6_four_of_concrete {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4)
    (hconcrete : ∃ (q : ℕ) (B' : Subgroup (adjointGroup Tag.E6 K))
      (x' : adjointGroup Tag.E6 K) (J : Subgroup (adjointGroup Tag.E6 K)),
      Concl166S (adjointGroup Tag.E6 K) 5 q B' x' J) :
    ∃ (q : ℕ) (B' : Subgroup (adjointGroup Tag.E6 F)) (x' : adjointGroup Tag.E6 F)
      (J : Subgroup (adjointGroup Tag.E6 F)),
      Concl166S (adjointGroup Tag.E6 F) 5 q B' x' J := by
  have hK : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card]; decide
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype F := Fintype.ofFinite F
  let eField : K ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hK.trans hF.symm)
  let eAdj : adjointGroup Tag.E6 K ≃* adjointGroup Tag.E6 F :=
    CFSG.TauCetiBridge.adjointGroupCongr (τ := Tag.E6) eField
  exact exists_concl166S_of_mulEquiv eAdj.symm hconcrete

theorem exists_concl166S_e6Four
    (hD4 : LayerData166At ⟨.D, 4, 2⟩) :
    ∃ (q : ℕ) (B' : Subgroup (adjointGroup Tag.E6 K)) (x' : adjointGroup Tag.E6 K)
      (J : Subgroup (adjointGroup Tag.E6 K)),
      Concl166S (adjointGroup Tag.E6 K) 5 q B' x' J := by
  have hcard : Nat.card K = 4 := by rw [Nat.card_eq_fintype_card]; decide
  have heven : evenRank (adjointGroup Tag.E6 K) = 5 :=
    evenRank_adjointGroup_E6_two hcard
  have hxq : e6FourX ^ 3 = 1 :=
    isElemAbelian_e6FourB.2 e6FourX e6FourX_mem_e6FourB
  have he : 4 ≤ evenRank (adjointGroup Tag.E6 K) := by rw [heven]; norm_num
  have hm2 : evenRank (adjointGroup Tag.E6 K) + 2 ≤ twoRank e6FourJ := by
    rw [heven]
    exact (by norm_num : 5 + 2 ≤ 12).trans e6FourJ_mult.2.2.1
  have hdvd : 5 * 3 ∣ Nat.card (e6FourJ ⧸ Subgroup.center e6FourJ) := dvd_e6FourJ
  have hqn : 3 ∣ 2 ^ (⟨.D, 4, 2⟩ : GLALabel).n - 1 := by norm_num
  have hrank : (⟨.D, 4, 2⟩ : GLALabel).rank = evenRank (adjointGroup Tag.E6 K) - 1 := by
    rw [heven]
  obtain ⟨B', hB'⟩ := exists_concl166S_of_layerData166At_of_comp
    (K := adjointGroup Tag.E6 K) (p := 5) (q := 3) (x := e6FourX) (J := e6FourJ)
    Nat.prime_three (by norm_num) hxq e6FourX_ne_one center_adjointGroup_eq_bot he
    e6FourJ_le_centralizer isQuasisimple_e6FourJ e6FourJ_comp ⟨.D, 4, 2⟩ hasLabel_e6FourJ
    (fun lab hlab => e6Four_JShape hlab) hm2 hdvd center_e6FourJ e6FourJ_mult.1.2
    hD4 hqn hrank
  exact ⟨3, B', e6FourX, e6FourJ, hB'⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F
