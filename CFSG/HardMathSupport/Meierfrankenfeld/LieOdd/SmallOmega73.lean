module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Orth
public import CFSG.LieType.Steinberg.CentralExt.SpinSevenThree
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.Quasithin TauCeti CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

section Model


theorem exists_pomega_model_of_lie_B3_three {L : Type} [Group L] [Finite L]
    (hperf : Group.IsPerfect L) (hodd : Odd (Nat.card (Subgroup.center L))) {q : PrimePower}
    (hv : (LieTypeIndex.B 3 q).Valid) (hp2 : q.p ≠ 2) (h3 : q.card = 3)
    (e : L ⧸ Subgroup.center L ≃* (CFSGIndex.lie ⟨.B 3 q, hv⟩).Group) :
    Nat.card (Subgroup.center L) ∣ 3 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 3 ∧
        Nonempty (L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadOdd 3 K))) := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.B 3 q, hv⟩ : ValidLieTypeIndex)
  set K := ↥(ValidLieTypeIndex.fixedField ⟨.B 3 q, hv⟩)
  have hK : Nat.card K = q.p ^ q.exponent := by
    rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder, PrimePower.card_def]
  have hK3 : Nat.card K = 3 := by rw [hK, ← PrimePower.card_def, h3]
  let e' : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadOdd 3 K)) :=
    e.trans (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd 3 q hv
      hp2 le_rfl)
  obtain ⟨-, ⟨φ⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SpinOddClosed.pomegaOdd_three_three_hopfMultiplier
    hK3
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf e'
  have hM : Nat.card (CFSG.Open.griessHopfMultiplier
      (StatedProj (StatedOmega (StatedQuadOdd 3 K)))) = 2 * 3 := by
    rw [Nat.card_congr φ.toEquiv]
    exact card_multiplicative_zmod_prod 2 3
  rw [hM] at hdvd
  have hcop : Nat.Coprime (Nat.card (Subgroup.center L)) 2 :=
    Nat.coprime_two_right.2 hodd
  exact ⟨hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd), K, inferInstance, inferInstance,
    hK3, ⟨e'⟩⟩

end Model

theorem lt_of_omega73_of_center_bot {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hE : E ≠ ⊥) (hel : IsElemAbelian2 E)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (hcenter : Subgroup.center ↥L = ⊥)
    (θ : ↥L ≃* StatedProj (StatedOmega (StatedQuadOdd 3 K))) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK' : Nat.card K = 3 ^ 1 := by rw [hK]; norm_num
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (f := 1) (by
    rw [← Nat.card_eq_fintype_card]; exact hK')
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card Nat.prime_three (by norm_num) hK'
  have hord := card_sup_le_of_pomegaOdd hW hq.1 hirr hcenter hEN hel Nat.prime_three
    (by norm_num) le_rfl hK' (r := 3) le_rfl (n := 2 * 3 + 1) rfl θ
  have hdim := two_pow_le_card_of_pomega hW (p := 3) (by norm_num) (coe_quadOdd 3 K)
    (nondegenerate_polarBilin_quadOdd 3 K h2) (commutator_orthogonalGroup_quadOdd h2 le_rfl)
    (oddPair_orth (K := K) (i := (⟨0, by omega⟩ : Fin 3)) (j := ⟨1, by omega⟩)
      (by simp))
    (oddPair_orth (K := K) (i := (⟨0, by omega⟩ : Fin 3)) (j := ⟨2, by omega⟩)
      (by simp [Fin.ext_iff]))
    (oddPair_orth (K := K) (i := (⟨1, by omega⟩ : Fin 3)) (j := ⟨2, by omega⟩)
      (by simp [Fin.ext_iff])) θ
  rw [dim_exponent_eq hK', Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_unit, show 3 + (3 + 1) = 2 * 3 + 1 by ring] at hdim
  exact lt_of_pomega hW hq hirr hEN hE hel (by norm_num) le_rfl (by norm_num) hord hdim

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
