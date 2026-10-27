module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInSpTransFactor
public import CFSG.LieType.SeitzGeneration.OuterSpData
public import CFSG.RankThree.PartOne.CTP.SeitzSpOuter
public import CFSG.RankThree.PartOne.S11d.PSLDescent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S171
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open scoped commutatorElement


private theorem sympMatrixCase (h : SympCompMatrixAnalysis)
    {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G}
    (hS : Setup p L J A d b) {n m : ℕ} {K : Type} [Field K] [Finite K] {x y : StatedSp m K}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSp m K)}
    (hKcard : Nat.card K = 2 ^ n) (hm2 : 2 ≤ m)
    (hx : LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * l * d)
      (MulAut.conj (proj m K x)))
    (hy : LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b)
      (MulAut.conj (proj m K y))) :
    InnDiagOn p (Subgroup.zpowers b) J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hKcard
  haveI : NeZero m := ⟨by omega⟩
  have hqJ : CFSG.IsQuasisimple (PQuot p J) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr
        (isQuasisimple_pQuot_of_glaPComponent hS.prime hS.pcomp))
  by_cases hbz : b ∈ Subgroup.zpowers d
  · exact innDiagOn_zpowers_of_mem_zpowers hS.prime hS.pcomp hS.chevJ hS.b_norm
      (hS.comp.1.1.trans inf_le_right) hbz
  by_cases hbJ : b ∈ Subgroup.centralizer (J : Set G)
  · exact innDiagOn_of_mem_centralizer hS.prime hS.pcomp hS.chevJ hS.b_norm hbJ
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := S171.normalizer_of_innerDiagMarking hS.idiag
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hAN hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := hAN hS.b_mem
  have hZ : Subgroup.center (StatedProj (StatedSp m K)) = ⊥ :=
    CFSG.LieType.SeitzGeneration.center_statedProj_statedSp_eq_bot hm2
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hxp : x ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ
      (conjAut_pow_eq_one_of_largeEvenInduces hdN (hS.elem.2 d hS.d_mem) hx)
  have hyp : y ^ p = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ
      (conjAut_pow_eq_one_of_largeEvenInduces hbN (hS.elem.2 b hS.b_mem) hy)
  have hbd : b * d = d * b :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_commute hS.elem hS.b_mem hS.d_mem
  have hcommβ : Commute (MulAut.conj (proj m K x)) (MulAut.conj (proj m K y)) :=
    conjAut_commute_of_largeEvenInduces hdN hbN hbd hx hy
  have hxy : x * y = y * x := commute_symp_of_conjAut_commute hZ hcommβ
  rcases h p L J A d b m n K x y θ hS hKcard hm2 hx hy hxp hyp hxy hbz hbJ with
    ⟨htype, hmem⟩ | ⟨htype, hmem⟩ | hi
  · exact innAutDerivedInnDiag_linear p J b hS.b_norm hS.prime hqJ htype hmem
  · exact innAutDerivedInnDiag_unitary p J b hS.b_norm hS.prime hqJ htype hmem
  · exact CFSG.LocalAnalysis.GLTheoremA.MI.inner_innDiag_holds hS.prime hS.pcomp hS.chevJ
      hS.b_norm hi

theorem innerCompNonShape_symp_charTwo (h : SympCompMatrixAnalysis) :
    InnerCompNonShape fun i => isSympBCIdx i ∧ i.characteristic = 2 := by
  intro G _ _ p L J A d b hS hcat _hshape _hin
  obtain ⟨idx, hidx, ⟨eS⟩⟩ := hcat
  cases idx with
  | cyclic n _ => exact absurd hidx (by simp [onLie])
  | alternating n _ => exact absurd hidx (by simp [onLie])
  | sporadic s => exact absurd hidx (by simp [onLie])
  | lie j =>
    have hsymp : isSympBCIdx j.1 := hidx.1
    have hchar : j.1.characteristic = 2 := hidx.2
    obtain ⟨d, hv⟩ := j
    cases d with
    | B m q =>
      have hchar' : TauCeti.LieTypeIndex.characteristic (.B m q) = 2 := hchar
      rw [TauCeti.LieTypeIndex.characteristic_B] at hchar'
      have hqcard : q.card = 2 ^ q.exponent := by
        rw [TauCeti.PrimePower.card_def, hchar']
      obtain ⟨K, hKfield, hKfinite, hKcard, hm2, θ, hforall⟩ :=
        spMarking_holds (G := G) p L J A d b m q.exponent hS
          ⟨.lie ⟨.B m q, hv⟩, ⟨q, Or.inl rfl, hqcard⟩, ⟨eS⟩⟩
      letI := hKfield
      letI := hKfinite
      obtain ⟨x, hx⟩ := hforall d hS.d_mem
      obtain ⟨y, hy⟩ := hforall b hS.b_mem
      exact sympMatrixCase h hS hKcard hm2 hx hy
    | C m q =>
      have hchar' : TauCeti.LieTypeIndex.characteristic (.C m q) = 2 := hchar
      rw [TauCeti.LieTypeIndex.characteristic_C] at hchar'
      have hqcard : q.card = 2 ^ q.exponent := by
        rw [TauCeti.PrimePower.card_def, hchar']
      obtain ⟨K, hKfield, hKfinite, hKcard, hm2, θ, hforall⟩ :=
        spMarking_holds (G := G) p L J A d b m q.exponent hS
          ⟨.lie ⟨.C m q, hv⟩, ⟨q, Or.inr rfl, hqcard⟩, ⟨eS⟩⟩
      letI := hKfield
      letI := hKfinite
      obtain ⟨x, hx⟩ := hforall d hS.d_mem
      obtain ⟨y, hy⟩ := hforall b hS.b_mem
      exact sympMatrixCase h hS hKcard hm2 hx hy
    | _ => exact absurd hsymp (by simp [isSympBCIdx])

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
