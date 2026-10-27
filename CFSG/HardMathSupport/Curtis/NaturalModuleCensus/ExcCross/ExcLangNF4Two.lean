module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNEmbed
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNTorus
public import CFSG.HardMathSupport.Malle.Proving.E27OrderModTwo
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeRank
public import CFSG.RankThree.PartOne.K133H.F4Weyl

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice

section Main


theorem exists_weyl_neg_F4 : ∃ w0 : WeylGroup Tag.F4, ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u := by
  refine ⟨(coxeterSystem Tag.F4).wordProd f4TwoWord, fun u => ?_⟩
  have h : toMat Tag.F4.rank f4TwoMat = (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) := by
    decide +kernel
  rw [wordProd_smul_eq_wordMat_mulVec, f4Two_wordMat, h, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem card_NFix_F4 {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F) {w0 : WeylGroup Tag.F4}
    (hw0 : ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u) :
    Nat.card (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr) =
      (Nat.card F + 1) ^ 4 * 1152 := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  rw [card_NFix Fr hw0 hFr, card_twistedTorusOf_negOne Fr w0 hw0 hFr,
    CFSG.RankThree.PartOne.K133H.card_weylGroup_F4]
  rfl

theorem finite_NFix_F4 {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F) {w0 : WeylGroup Tag.F4}
    (hw0 : ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u) :
    Finite (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_NFix_F4 Fr hFr hw0]
    exact mul_ne_zero (pow_ne_zero _ (Nat.succ_ne_zero _)) (by norm_num))

theorem v3_card_NFix_F4 {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F) {w0 : WeylGroup Tag.F4}
    (hw0 : ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u) (h3 : 3 ∣ Nat.card F + 1) :
    padicValNat 3 (Nat.card (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)) =
      4 * padicValNat 3 (Nat.card F + 1) + 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 1 < Nat.card F := Finite.one_lt_card
  rw [card_NFix_F4 Fr hFr hw0, padicValNat.mul (pow_ne_zero _ (by omega)) (by norm_num),
    padicValNat.pow (Nat.card F + 1) 4,
    show (1152 : ℕ) = 3 ^ 2 * 2 ^ 7 by norm_num,
    padicValNat.mul (by positivity) (by positivity), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (p := 3) (n := 2 ^ 7) (by norm_num)]

theorem exists_F4_two_sylow {F : Type} [Field F] [Finite F] {L : Type} [Field L] [Algebra F L]
    [IsAlgClosure F L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card F)
    (h3 : 3 ∣ Nat.card F + 1) {w0 : WeylGroup Tag.F4}
    (hw0 : ∀ u : Fin Tag.F4.rank → ℤ, w0 • u = -u) :
    ∃ ι : NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr →* ↥(adjointGroup Tag.F4 F),
      Function.Injective ι ∧
      ∃ P : Subgroup (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr),
        IsPGroup 3 P ∧ Nat.card P = 3 ^ (Nat.card ↥(adjointGroup Tag.F4 F)).factorization 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hfin := finite_NFix_F4 Fr hFr hw0
  have hJfin : Finite ↥(adjointGroup Tag.F4 F) := generated_group_finite Tag.F4 F
  obtain ⟨ι, hι⟩ := exists_embedding_nfix w0 Fr hFr
    (fun X _ hXC hXF => relIndex_dvd_F4 F L Fr hFr X hXC hXF) hfin
  refine ⟨ι, hι, ?_⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr)) :=
    inferInstance
  refine ⟨(S : Subgroup _), S.isPGroup', ?_⟩
  rw [Sylow.card_eq_multiplicity]
  congr 1
  have hJ : Nat.card ↥(adjointGroup Tag.F4 F) ≠ 0 := Nat.card_pos.ne'
  have hN : Nat.card (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr) ≠ 0 :=
    Nat.card_pos.ne'
  rw [Nat.factorization_def _ Nat.prime_three, Nat.factorization_def _ Nat.prime_three]
  have hlow := v3_card_NFix_F4 Fr hFr hw0 h3
  have hdvd : Nat.card (NFix (canonicalRep (coxeterSystem Tag.F4) L w0) Fr) ∣
      Nat.card ↥(adjointGroup Tag.F4 F) := Subgroup.card_dvd_of_injective ι hι
  have hup := (padicValNat_dvd_iff_le hJ).1
    ((pow_padicValNat_dvd (p := 3)).trans hdvd)
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4,
    CFSG.HardMathSupport.Malle.Proving.padicValNat_three_ordF4_of_mod_two hq (by omega)]
    at hup ⊢
  omega

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
