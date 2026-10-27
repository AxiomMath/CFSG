module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3G2
import CFSG.RankThree.PartTwo.KFacts.K71G2
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof (g2ShortSL2 g2LongSL2 g2Short_commute_g2Long
  isQuasisimple_g2ShortSL2 isQuasisimple_sl2)
open CFSG.RankThree.PartTwo.KFacts (g2FieldHom g2_automorphism_normal_form)
open CFSG.LocalAnalysis.GLTheoremA.S267.P3 (mem_g2ShortSL2_iff_rootSL2 mem_g2LongSL2_iff_rootSL2
  coe_g2FieldHom_rootSL2 map_sl2_eq_self map_g2FieldHom_g2ShortSL2 exists_g2_involution)

section SL2

theorem eq_one_of_mem_center_sl2_of_pow {F : Type} [Field F] {p : ℕ} (hp2 : Odd p)
    {A : SL2 F} (hA : A ∈ Subgroup.center (SL2 F)) (hAp : A ^ p = 1) : A = 1 := by
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr2' : r ^ 2 = 1 := by simpa using hr2
  have hrp : r ^ p = 1 := by
    have h : (Matrix.scalar (Fin 2) r) ^ p = Matrix.scalar (Fin 2) 1 := by
      rw [hrA, ← Matrix.SpecialLinearGroup.coe_pow, hAp, Matrix.SpecialLinearGroup.coe_one,
        map_one]
    rw [← map_pow] at h
    exact Matrix.scalar_inj.1 h
  have hr : r = 1 := by
    have h := (pow_gcd_eq_one (a := r) (m := p) (n := 2)).2 ⟨hrp, hr2'⟩
    rwa [Nat.Coprime.gcd_eq_one hp2.coprime_two_right, pow_one] at h
  apply Subtype.ext
  rw [← hrA, hr, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem exists_orderOf_eq_sl2 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : p ∣ Nat.card F ^ 2 - 1) : ∃ A : SL2 F, orderOf A = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype (SL2 F) := Fintype.ofFinite _
  refine exists_prime_orderOf_dvd_card p ?_
  rw [← Nat.card_eq_fintype_card, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact Dvd.dvd.mul_left hpF _

theorem exists_not_commute_sl2 {F : Type} [Field F] {p : ℕ} (hp : p.Prime) (hp2 : Odd p)
    {A : SL2 F} (hA : orderOf A = p) : ∃ W : SL2 F, A * W ≠ W * A := by
  by_contra h
  push Not at h
  have hc : A ∈ Subgroup.center (SL2 F) := Subgroup.mem_center_iff.2 fun W => (h W).symm
  have h1 := eq_one_of_mem_center_sl2_of_pow hp2 hc (by rw [← hA]; exact pow_orderOf_eq_one A)
  rw [h1, orderOf_one] at hA
  exact hp.one_lt.ne hA

end SL2

section Model

variable {K : Type} [Field K]

theorem dvd_card_fixSubfield_sq_sub_one [Finite K] {p : ℕ} (hp : p.Prime) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hpK : p ∣ Nat.card K ^ 2 - 1) :
    p ∣ Nat.card (fixSubfield σ) ^ 2 - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_pow σ
  rw [hσ] at hc
  set n := Nat.card (fixSubfield σ) with hn
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  have hK1 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
  rw [← ZMod.natCast_eq_zero_iff] at hpK ⊢
  rw [Nat.cast_sub hK1, ← hc] at hpK
  rw [Nat.cast_sub hn1]
  push_cast at hpK ⊢
  rwa [← pow_mul, mul_comm, pow_mul, ZMod.pow_card] at hpK

noncomputable abbrev fixIncl (σ : K ≃+* K) : SL2 (fixSubfield σ) →* SL2 K :=
  Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype

theorem fixIncl_injective (σ : K ≃+* K) : Function.Injective (fixIncl σ) := fun A B h =>
  Subtype.ext (Matrix.ext fun i j =>
    Subtype.val_injective (congrFun (congrFun (congrArg Subtype.val h) i) j))

theorem map_fixIncl (σ : K ≃+* K) (A : SL2 (fixSubfield σ)) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (fixIncl σ A) = fixIncl σ A :=
  map_sl2_eq_self fun i j => (A i j).2

variable [Finite K]

end Model

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
