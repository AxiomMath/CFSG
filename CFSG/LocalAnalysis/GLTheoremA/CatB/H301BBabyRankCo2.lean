module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BTwoBLocal
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Twist
public import CFSG.Sporadic.Co2Smith.GlU62Ker
public import CFSG.RankThree.PartOne.F106.ThreeRankHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  Subgroup

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

private theorem factorization_three_mul {a c : ℕ} (hc : ¬ 3 ∣ c) :
    (3 ^ a * c).factorization 3 = a := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero 3)
  rw [Nat.factorization_mul (by positivity) hc0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hc, add_zero]

section Co2


theorem card_le_co2_three (E : Subgroup NativeSporadic.Co2) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 4 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite NativeSporadic.Co2 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hE.isPGroup
  have h5 : 3 ^ 5 ≤ Nat.card E := by
    rw [hk] at hlt ⊢
    exact Nat.pow_le_pow_right (by norm_num) ((Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt)
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_three hE.isPGroup h5
  have hF : IsElemAbelian 3 (T.map E.subtype) := hE.mono (map_subtype_le T)
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (show 3 ^ 6 ∣ Nat.card CFSG.Sporadic.Co2Smith.G0c by
      rw [CFSG.Sporadic.Co2Smith.card_G0c]; norm_num)
  have hQc : Nat.card (Q.map CFSG.Sporadic.Co2Smith.G0c.subtype) =
      3 ^ (Nat.card (⊤ : Subgroup NativeSporadic.Co2)).factorization 3 := by
    rw [card_map_of_injective CFSG.Sporadic.Co2Smith.G0c.subtype_injective, hQ, card_top,
      CFSG.Sporadic.Co2.card_Co2, show (42305421312000 : ℕ) = 3 ^ 6 * 58032128000 by norm_num,
      factorization_three_mul (by norm_num)]
  obtain ⟨g, -, hg⟩ := H1017.exists_conj_into_of_card (H := (⊤ : Subgroup NativeSporadic.Co2))
    le_top hQc le_top hF.isPGroup
  have hle : (T.map E.subtype).map (MulAut.conj g).toMonoidHom ≤ CFSG.Sporadic.Co2Smith.G0c :=
    hg.trans (map_subtype_le Q)
  let e : CFSG.Sporadic.Co2Smith.SU6 ⧸ center CFSG.Sporadic.Co2Smith.SU6 ≃*
      CFSG.Sporadic.Co2Smith.G0c :=
    (QuotientGroup.quotientMulEquivOfEq CFSG.Sporadic.Co2Smith.ker_thetaK).symm.trans
      ((QuotientGroup.quotientKerEquivRange CFSG.Sporadic.Co2Smith.thetaK).trans
        (MulEquiv.subgroupCongr CFSG.Sporadic.Co2Smith.range_thetaK))
  have hmod := CFSG.LieType.Universal.Unitary.statedClassicalModel_center_quotient
    (F := CFSG.Fischer.F4) (p := 2) (f := 1) (n := 6)
    ⟨Nat.prime_two, le_rfl, by norm_num, by simp⟩ CFSG.Sporadic.Co2Smith.natCard_F4
  refine CFSG.RankThree.PartOne.F106.u6ThreeRank_holds _ hmod
    ((((T.map E.subtype).map (MulAut.conj g).toMonoidHom).subgroupOf
      CFSG.Sporadic.Co2Smith.G0c).map e.symm.toMonoidHom)
    (((hF.map _).subgroupOf _).map _).isElementaryAbelian ?_
  rw [card_map_of_injective e.symm.injective, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
    card_map_of_injective (MulAut.conj g).injective, card_map_of_injective E.subtype_injective, hT]

end Co2

section TwoB


theorem card_le_of_babyInv_one {t : NativeSporadic.B} (ht : BabyInv 1 t)
    (E : Subgroup NativeSporadic.B) (hEt : E ≤ centralizer ({t} : Set NativeSporadic.B))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 4 := by
  obtain ⟨g, hg⟩ := isConj_iff.1
    (CFSG.Monster.Existence.babyTableIII.2 1 t xB ht babyInv_one_xB)
  obtain ⟨F, hF, hker⟩ := exists_hom_centralizer_xB
  have hE' : E.map (MulAut.conj g).toMonoidHom ≤ centralizer ({xB} : Set NativeSporadic.B) := by
    have h := H1017.map_conj_le_centralizer_singleton g hEt
    rwa [hg] at h
  rw [← card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
  exact H1017.H1016M5.card_le_of_le_quot Nat.prime_three (by norm_num) (IsPGroup.of_card hker)
    card_le_co2_three (QuotientGroup.quotientKerEquivOfSurjective F hF) hE' (hE.map _)

end TwoB

end CFSG.LocalAnalysis.GLTheoremA.H301B
