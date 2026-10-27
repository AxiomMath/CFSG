module

public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutGN
public import CFSG.LocalAnalysis.RankThreeUC.GN15SolvAlt
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
public import CFSG.GH74.Generic.S45.LOut
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WU3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Q8Psl2
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Adapters.TauCetiExceptional.EvenBridgeG2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.LowTwoRank CFSG.Open
open scoped commutatorElement

namespace JOutOdd

theorem odd_card_commutator_outer_of_psl_two_model {X : Type} [Group X] {m : ℕ}
    (h : StatedClassicalModel X .PSL 2 2 m) : Odd (Nat.card (commutator (Outer X))) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have e' : X ≃* CFSG.RankThree.PartOne.KCRootAxis.SL₂ K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (CFSG.RankThree.PartOne.KCRootAxis.slEquivPSL K).symm
  refine CFSG.ComponentClassification.RankTwoExceptional.odd_card_commutator_outer_of_equiv e' ?_
  haveI : IsCyclic (Outer (CFSG.RankThree.PartOne.KCRootAxis.SL₂ K)) :=
    CFSG.RankThree.PartOne.KCRootAxis.out_sl2_isCyclic
  let : CommGroup (Outer (CFSG.RankThree.PartOne.KCRootAxis.SL₂ K)) := IsCyclic.commGroup
  exact CFSG.ComponentClassification.RankTwoExceptional.odd_card_commutator_of_comm
    fun a b => mul_comm a b


section G2

open TauCeti

theorem odd_card_commutator_outer_of_G2_index
    (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid) (hp2 : q.p = 2) {Y : Type} [Group Y]
    (e : Y ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) : Odd (Nat.card (commutator (Outer Y))) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq3 : 3 ≤ q.card :=
    (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', PrimePower.card_def]
  obtain ⟨e0⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hp2
    (GaloisField q.p q.exponent) hK
  have hce : CFSG.Blueprint.ChevalleyExceptionalModel (CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl, ?_⟩, GaloisField q.p q.exponent, inferInstance,
      inferInstance, ?_, ⟨e0.symm⟩⟩
    · rw [← PrimePower.card_def]
      exact hq3
    · rw [hK, PrimePower.card_def]
  rw [hp2] at hce
  have hm : 2 ≤ q.exponent := by
    by_contra hlt
    have h1 : q.exponent = 1 := by have := q.exponent_pos; omega
    rw [PrimePower.card_def, hp2, h1] at hq3
    omega
  exact CFSG.ComponentClassification.RankTwoExceptional.odd_card_commutator_outer_of_equiv e
    (CFSG.ComponentClassification.RankTwoExceptional.odd_card_commutator_outer_G2 hm hce)

end G2

section Small

open CFSG.GorensteinWalter

theorem odd_card_commutator_outer_of_psl_two_seven {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 2 7 1) : Odd (Nat.card (commutator (Outer X))) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hK7 : Nat.card K = 7 := by rw [hK]; norm_num
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hK7]; norm_num⟩
  have hcard : 3 < Nat.card K := by rw [hK7]; norm_num
  have e' : X ≃* PSL2 K := e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hK7 hodd hcard
  let φ : PGL2 K ≃* MulAut (PSL2 K) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 K hodd hcard) hbij
  have hInn : CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.map
        φ.toMonoidHom := by
    ext δ
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL y, ⟨y, rfl⟩, ?_⟩
      exact pgl2InnerAutPSL2_toPGL K hodd hcard y
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, (pgl2InnerAutPSL2_toPGL K hodd hcard y).symm⟩
  have h2 : (Subgroup.map φ.toMonoidHom
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range).index =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.index :=
    Subgroup.index_map_equiv _ φ
  have hidx : (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K)).index = 2 := by
    rw [hInn, h2, pgl2_psl2Range_index_eq_two K hodd]
  have hc2 : Nat.card (Outer (PSL2 K)) = 2 := hidx
  haveI : Fact (Nat.Prime (Nat.card (Outer (PSL2 K)))) := ⟨by rw [hc2]; exact Nat.prime_two⟩
  haveI : IsCyclic (Outer (PSL2 K)) := isCyclic_of_prime_card hc2
  refine CFSG.ComponentClassification.RankTwoExceptional.odd_card_commutator_outer_of_equiv e' ?_
  let : CommGroup (Outer (PSL2 K)) := IsCyclic.commGroup
  exact CFSG.ComponentClassification.RankTwoExceptional.odd_card_commutator_of_comm
    fun a b => mul_comm a b

end Small

section Dispatch

open TauCeti CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabAutIrr

theorem odd_card_commutator_outer_of_u33 {Y : Type} [Group Y] (q : PrimePower)
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3)
    (e : Y ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) :
    Odd (Nat.card (commutator (Outer Y))) := by
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hq' : q.p ^ q.exponent = 3 := by rw [← PrimePower.card_def]; exact hq
  obtain ⟨hp3, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 3)).mp hq'
  rw [hp3, he1] at h
  exact CFSG.GH74.GLS.IVK.Proofs2.ivk93w_uni3_outer_commutator_odd (by norm_num) h

theorem odd_card_commutator_outer_of_lie_index
    (d : ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1) {Y : Type} [Group Y]
    (e : Y ≃* (CFSGIndex.lie d).Group) : Odd (Nat.card (commutator (Outer Y))) := by
  rcases classical_model_or_g2 d hd e with ⟨t, n, f, ht, hm⟩ | ⟨q, hq, hq2, hdq⟩
  · have hadm := hm.1
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨-, -, hn2, -⟩ := hadm
      rcases Nat.lt_or_ge n 3 with h3 | h3
      · obtain rfl : n = 2 := by omega
        exact odd_card_commutator_outer_of_psl_two_model hm
      · exact CFSG.ComponentClassification.RankTwoClassical.odd_card_commutator_outer_of_psl_model
          h3 hm
    · exact CFSG.ComponentClassification.RankTwoClassical.odd_card_commutator_outer_of_psu_model hm
    · obtain ⟨-, -, hn2, -⟩ := hadm
      exact CFSG.ComponentClassification.RankTwoClassical.odd_card_commutator_outer_of_psp_model
        hn2 hm
    · obtain ⟨-, -, hn4⟩ := hadm
      rcases Nat.lt_or_ge n 5 with h5 | h5
      · obtain rfl : n = 4 := by omega
        exact CFSG.ComponentClassification.RankTwoClassical.odd_card_commutator_outer_POmegaPlus_four hm
      · exact CFSG.ComponentClassification.RankTwoClassical.odd_card_commutator_outer_POmegaPlus h5 hm
    · obtain ⟨-, -, hn4⟩ := hadm
      exact CFSG.ComponentClassification.RankTwoClassical.odd_card_commutator_outer_POmegaMinus hn4 hm
  · subst hdq
    exact odd_card_commutator_outer_of_G2_index q hq hq2 e

end Dispatch


section Perfect

open CFSG.HardMathSupport.Cooperstein.Coordinator TauCeti CFSG.AGLEmbedding

theorem odd_card_commutator_outer_of_ffConclusion
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (h : FFConclusion (L ⧸ Subgroup.center L)) : Odd (Nat.card (commutator (Outer L))) := by
  have halt : ∀ m : ℕ, 5 ≤ m → Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin m)) →
      Odd (Nat.card (commutator (Outer L))) := fun m hm ⟨e⟩ =>
    CFSG.GH74.Generic.S45.odd_card_commutator_of_isMulCommutative
      (isMulCommutative_outer_of_alternating hm e)
  have hY : Odd (Nat.card (commutator (Outer (L ⧸ Subgroup.center L)))) →
      Odd (Nat.card (commutator (Outer L))) := fun h' =>
    CFSG.GH74.Generic.S45.odd_card_commutator_outer_of_perfect inferInstance h'
  rcases h with hcl | ⟨m, hm, ⟨e⟩⟩
  · rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact hY (odd_card_commutator_outer_of_lie_index d hd e)
    · exact halt n (by omega) ⟨e⟩
    · obtain ⟨d1, hv⟩ := d
      rcases hd with ⟨q, hq, hd1⟩ | ⟨q, hq, hd1⟩
      · simp only at hd1
        subst hd1
        have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        have hq' : q.p ^ q.exponent = 7 := by rw [← PrimePower.card_def]; exact hq
        obtain ⟨hp7, he1⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp hq'
        rw [hp7, he1] at h
        exact hY (odd_card_commutator_outer_of_psl_two_seven h)
      · simp only at hd1
        subst hd1
        exact hY (odd_card_commutator_outer_of_u33 q hv hq e)
  · exact halt m hm ⟨e⟩

end Perfect

end JOutOdd

section GN

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.AGLEmbeddingD2.GN

theorem outDerivedOdd_of_ffModuleTheorem
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem) : OutDerivedOdd := by
  intro X _ _ T hX L hL hne
  have hQ : CFSG.IsQuasisimple L := ((CFSG.isComponent_iff_open L).2 hL).1
  have hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L :=
    commutator_eq_of_ne_bot hQ (thompsonJ_le_normalizer_of_isComponentOf hX hL) hne
  have hff := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.gn_ffConclusion hFF X T hX L hL hJ
  haveI : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  exact JOutOdd.odd_card_commutator_outer_of_ffConclusion hff

theorem jOutCentral_of_ffOffender
    (hFF : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem)
    (hS : FFOffenderInvertsOdd) : JOutCentral :=
  jOutCentral_of_offender hS (outDerivedOdd_of_ffModuleTheorem hFF)

end GN

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
