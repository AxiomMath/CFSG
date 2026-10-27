module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.TD4ResDefs
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocStd
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStdLocSyl
public import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenLevi

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDescTD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.RankTwoExceptional.D4
open CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc
open CFSG.Quasithin.H13.F431.D4q.StdLoc
open CFSG.RankThree.PartTwo.Census.Carrier

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

private theorem threeRankLeOne_orbitRankOneGroup (hσ3 : σ ^ 3 = 1)
    (a : Fin TwistTag.D4.foldedTag.rank) :
    ThreeRankLeOne ↥(orbitRankOneGroup TwistTag.D4 K σ.toRingHom a) := by
  haveI : CharP ↥(orbitField TwistTag.D4 K σ.toRingHom a) 2 := inferInstance
  exact ThreeRankLeOne.of_mulEquiv
    ((MulEquiv.subgroupCongr (orbitRankOneHom_range (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom) a)).symm.trans
      (MonoidHom.ofInjective (orbitRankOneHom_injective_D4 hσ3 a)).symm)
    threeRankLeOne_SL2

private theorem threeRankLeOne_d4Vr_sup_d4Mr (hσ : ∀ c, σ (σ (σ c)) = c) :
    ThreeRankLeOne ↥(d4Vr K σ ⊔ d4Mr K σ) :=
  ThreeRankLeOne.sup
    ((syl_isPGroup_U σ).to_le (graphFixedSimpleComplement_le ⟨0, by decide⟩))
    (orbitRankOneGroup_le_normalizer_d4 σ ⟨0, by decide⟩)
    (complement_inf_orbitRankOneGroup_d4 σ ⟨0, by decide⟩)
    (threeRankLeOne_orbitRankOneGroup σ (ringEquiv_cube_d4 σ hσ) ⟨0, by decide⟩)

theorem threeRankLeOne_centralizer_d4z (hσ : ∀ c, σ (σ (σ c)) = c) :
    ThreeRankLeOne ↥(Subgroup.centralizer ({zC σ} : Set (Cm σ))) :=
  ThreeRankLeOne.centralizer_of_le
    (H := d4C K σ) (X := d4Vr K σ ⊔ d4Mr K σ)
    (le_of_eq (centralizer_d4z_eq σ hσ))
    (threeRankLeOne_d4Vr_sup_d4Mr σ hσ)

theorem threeRankLeOne_centralizer_d4t (hσ : ∀ c, σ (σ (σ c)) = c) :
    ThreeRankLeOne ↥(Subgroup.centralizer ({tC σ hσ} : Set (Cm σ))) :=
  ThreeRankLeOne.centralizer_of_le
    (H := d4C K σ) (X := d4U0t K σ ⊔ d4Ma K σ)
    (le_of_eq (centralizer_d4t_eq σ hσ))
    (ThreeRankLeOne.sup
      ((syl_isPGroup_U σ).to_le (syl_U0t_le_U σ))
      (syl_Ma_le_normalizer σ)
      (disjoint_iff.mp (syl_disjoint σ))
      (threeRankLeOne_orbitRankOneGroup σ (ringEquiv_cube_d4 σ hσ) ⟨1, by decide⟩))

theorem threeRankLeOne_centralizer_of_orderOf_eq_two (hσ : ∀ c, σ (σ (σ c)) = c)
    {x : Cm σ} (hx : orderOf x = 2) :
    ThreeRankLeOne ↥(Subgroup.centralizer ({x} : Set (Cm σ))) := by
  rcases cls_d4 σ hσ x hx with h | h
  · exact ThreeRankLeOne.centralizer_of_isConj h.symm (threeRankLeOne_centralizer_d4z σ hσ)
  · exact ThreeRankLeOne.centralizer_of_isConj h.symm (threeRankLeOne_centralizer_d4t σ hσ)

theorem triD4InvCentRankOne_holds : TriD4InvCentRankOne := by
  intro n hn K _ _ hK σ hσ t ht E hE hc
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK'
  have hσ3 : ∀ c, σ (σ (σ c)) = c := by
    intro c
    have h1 : σ (σ (σ c)) = c ^ ((2 ^ n) * ((2 ^ n) * (2 ^ n))) := by
      rw [hσ (σ (σ c)), hσ (σ c), hσ c, ← pow_mul, ← pow_mul]
    have h2 : (2 ^ n) * ((2 ^ n) * (2 ^ n)) = Nat.card K := by
      rw [hK]
      ring
    rw [h1, h2, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hX : ThreeRankLeOne ↥(Subgroup.centralizer ({t} : Set (Cm σ))) :=
    threeRankLeOne_centralizer_of_orderOf_eq_two σ hσ3 ht
  refine D4Even.card_le_three_of_threeRankLeOne hX ?_ hE
  intro e he
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hc e he)

end CFSG.LocalAnalysis.GLTheoremA.HDescTD4
