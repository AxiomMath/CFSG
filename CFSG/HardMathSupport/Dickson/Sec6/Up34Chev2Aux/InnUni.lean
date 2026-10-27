module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnUniCore
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnUniBlock
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.RankThree.PartOne.KC.UnitaryGoodModel
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.CatLeaf CFSG.HardMathSupport.Dickson.Sec6.I923

namespace Up34Chev2

section Model

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem noL34Layer_primeFormConjHom_two (hO : LieOrderFormulasInput)
    (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (A : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c) :
    NoL34Layer (primeFormConjHom h (idGram K n) A) := by
  have hq : 2 ≤ ℓ ^ f := by
    have := Nat.one_lt_pow (by have := h.one_le; omega : f ≠ 0) h.prime.one_lt
    omega
  have hH := primaryData_toLin' h A.2 Nat.prime_three (by omega) hA
  exact noL34Layer_of_primaryData_two hq A rfl hH
    (fun a ha => not_isLThreeFour_specialBlock_two hO hℓ hH a ha)

theorem not_up34Pumpup_primeFormConjHom (hO : LieOrderFormulasInput)
    (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hn : 4 ≤ n) (A : primeFormUnitary h (idGram K n)) :
    ¬ Up34Pumpup (primeFormP h (idGram K n)) (primeFormConjHom h (idGram K n) A) := by
  intro hpump
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun hh => by omega
  have h1 : primeFormConjHom h (idGram K n) (A ^ 3) = 1 := by rw [map_pow]; exact hpump.1
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne (by omega) hne (A ^ 3)).1 h1
  exact ((up34Pumpup_iff _).1 hpump).2.2 (noL34Layer_primeFormConjHom_two hO h hℓ A (c := c)
    (by rw [← Subgroup.coe_pow]; exact hc))

theorem not_up34Pumpup_conj_psu (hO : LieOrderFormulasInput)
    (h : UnitaryFieldData ℓ f K) (hℓ : ℓ = 2) (hn : 4 ≤ n) (y : primeFormP h (idGram K n)) :
    ¬ Up34Pumpup (primeFormP h (idGram K n)) (MulAut.conj y) := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  have : MulAut.conj (s : primeFormP h (idGram K n)) =
      primeFormConjHom h (idGram K n) ⟨(s : GL (Fin n) K), s.2.1⟩ := by
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MulAut.conj_apply, primeFormConjHom_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    rfl
  rw [this]
  exact not_up34Pumpup_primeFormConjHom hO h hℓ hn _

end Model

section Closed


theorem up34C2Inn_TwAHigh_holds : Up34Chev2Inn FamTwAHigh := by
  intro S _ _ hs hnab d hF hc ⟨e⟩ x hpump
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q =>
    have hr : 3 ≤ r := hF
    have hp : q.p = 2 := hc
    have hm := blueprintLieModel_twistedA r q hv e
    obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hm.admissible hm
    haveI : Finite (primeFormP h (idGram K (r + 1))) := Finite.of_equiv S e0.toEquiv
    have hpump' := hpump.of_congr e0
    rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj] at hpump'
    exact not_up34Pumpup_conj_psu CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      h hp (by omega) (e0 x) hpump'
  | _ => exact hF.elim

end Closed

end Up34Chev2

end CFSG.HardMathSupport.Dickson.Sec6
