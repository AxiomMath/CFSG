module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.LocalAnalysis.StandardType.MarkingSmall
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenG2Two
public import CFSG.Quasithin.EmptyFaithfulMultiple.G2TwoUnitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.AtlasOrders2
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LieType.Steinberg.CentralExt.UnitaryPerfect
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.CharacterTheory.Burnside
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Sporadic.Schreier.TitsIso
public import CFSG.Sporadic.Schreier.TitsCert
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Assembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CommutatorFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FixedPointsTwo
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OddTwoImages
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRKill3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltBigVector
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltFixed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentreOneImage
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LowRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageOdd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SLModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SpModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.TwoImageLowRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionComponent
public import CFSG.RankThree.PartTwo.Sec4.T444.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

namespace Res

open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.Adapters.RankTwoModelTransports
open CFSG.ComponentClassification.PresentationLocal
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsUThreeThree)

theorem solv_of_natCard {G : Type*} [Group G] [Finite G] {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (h : Nat.card G = p ^ a * q ^ b) : Group.IsSolvable G := by
  have := Fintype.ofFinite G
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card, h])

theorem nonab_of_simple {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hp : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  haveI : IsMulCommutative X := ⟨⟨hc⟩⟩
  exact hp (Group.is_simple_iff_prime_card.mp hs)

theorem chevSimple_of_equiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : IsChevSimple 2 T) :
    IsChevSimple 2 S := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

theorem chevSimple_alt {R : Type} [Group R] {n : ℕ} (hn : 5 ≤ n) (h : n = 5 ∨ n = 6 ∨ n = 8)
    (e : R ≃* alternatingGroup (Fin n)) : IsChevSimple 2 R := by
  refine Or.inr ⟨.alternating n hn, ?_, ⟨e⟩⟩
  rcases h with rfl | rfl | rfl <;> simp [ambiguousChev]

theorem chevSimple_of_uThreeThree {X : Type} [Group X] (h : IsUThreeThree X) :
    IsChevSimple 2 X := by
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := h
  refine Or.inr ⟨TauCeti.CFSGIndex.lie d, ?_, ⟨e⟩⟩
  simp only [ambiguousChev, hd]
  exact ⟨hq, trivial⟩

theorem isUThreeThree_of_stated {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 1) : IsUThreeThree X := by
  obtain ⟨hadm, K, hfield, hfinite, hK, ⟨e⟩⟩ := h
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, one_pos⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, TauCeti.PrimePower.card_def]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let L := GaloisField 3 (2 * 1)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype L := Fintype.ofFinite L
  have hcard : Fintype.card K = Fintype.card L := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  let φ : K ≃+* L := FiniteField.ringEquivOfCardEq hcard
  let e1 := statedProjCongr (glCongr (ι := Fin 3) φ) (glCongr_statedSU φ 3 (3 ^ 1))
    (glCongr_statedScalars φ)
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv
  exact ⟨⟨_, hv⟩, ⟨q, by simp [q, TauCeti.PrimePower.card_def], rfl⟩, ⟨(e.trans e1).trans eT.symm⟩⟩

theorem solvable_A11 (D : Type) [Group D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.A, 1, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Group.IsSolvable D := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeLinear] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hcard : Nat.card (LargeEvenSLGroup (Fin (1 + 1)) K) = 2 ^ 1 * 3 ^ 1 := by
    rw [largeEvenSLGroup_eq_statedSL]
    have := CFSG.Open.StatedAPI.card_statedSL_two K
    rw [hK2] at this
    exact this.trans (by norm_num : (2 : ℕ) * (2 ^ 2 - 1) = 2 ^ 1 * 3 ^ 1)
  haveI : Finite (LargeEvenSLGroup (Fin (1 + 1)) K) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hs : Group.IsSolvable (LargeEvenSLGroup (Fin (1 + 1)) K) :=
    solv_of_natCard Nat.prime_two Nat.prime_three (by norm_num) hcard
  haveI : Group.IsSolvable (LargeEvenProj (LargeEvenSLGroup (Fin (1 + 1)) K)) :=
    inferInstanceAs (Group.IsSolvable (_ ⧸ _))
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem solvable_twA21 (D : Type) [Group D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.twA, 2, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Group.IsSolvable D := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeUnitary] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LieType.Steinberg.charP_of_card_eq_sq_pow (f := 1) Nat.prime_two hK'
  have hcard : Nat.card (LargeEvenSUGroup (Fin (2 + 1)) K (2 ^ 1)) = 2 ^ 3 * 3 ^ 3 := by
    have := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 2) (f := 1) hK'
    exact this.trans (by norm_num)
  haveI : Finite (LargeEvenSUGroup (Fin (2 + 1)) K (2 ^ 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hs : Group.IsSolvable (LargeEvenSUGroup (Fin (2 + 1)) K (2 ^ 1)) :=
    solv_of_natCard Nat.prime_two Nat.prime_three (by norm_num) hcard
  haveI : Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup (Fin (2 + 1)) K (2 ^ 1))) :=
    inferInstanceAs (Group.IsSolvable (_ ⧸ _))
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

theorem datumCore_sp21 {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) (D : Type) [Group D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨t, 2, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    DatumCore D := by
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 1 ∧
      Nonempty (D ≃* LargeEvenProj (LargeEvenSpGroup K 2)) := by
    rcases ht with rfl | rfl <;> exact h
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨eP⟩ := nonempty_largeEvenProj_equiv_of_card_two hK2 (LargeEvenSpGroup K 2)
  obtain ⟨eS⟩ := nonempty_largeEvenSpGroup_equiv_sympFour hK2
  let eD : D ≃* ↥sympFour := (e'.trans eP).trans eS
  obtain ⟨eC⟩ := nonempty_commutator_equiv eD
  let eE : ↥(commutator D) ≃* alternatingGroup (Fin 6) := eC.trans commutatorEquivAlternating
  have hsimple : IsSimpleGroup ↥(commutator D) :=
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    eE.isSimpleGroup_congr.2 inferInstance
  have hDcard : Nat.card D = 720 := by
    rw [Nat.card_congr eD.toEquiv,
      Nat.card_congr (MulEquiv.ofBijective omegaPerm
        ⟨omegaPerm_injective, omegaPerm_surjective⟩).toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have hEcard : Nat.card ↥(commutator D) = 360 := by
    rw [Nat.card_congr eE.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  refine ⟨commutator D, hsimple, ?_, ?_, Or.inr (by rw [hDcard, hEcard]),
    Or.inl (chevSimple_alt (by norm_num) (by simp) eE)⟩
  · by_contra hc
    push Not at hc
    have : IsMulCommutative ↥(commutator ↥sympFour) :=
      ⟨⟨fun x y => eC.symm.injective (by rw [map_mul, map_mul]; exact hc _ _)⟩⟩
    exact not_isMulCommutative_commutator_sympFour this
  · intro T hT
    rw [← hT, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

section Suzuki


theorem solvable_twB2 (D : Type) [Group D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.twB2, 0, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    Group.IsSolvable D := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeSuzuki] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have ha : (1 - 1) / 2 = 0 := rfl
  rw [ha] at hK e
  have hK' : Nat.card K = 2 ^ (2 * 0 + 1) := hK
  have hcard : Nat.card (LargeEvenSzGroup 0 K) = 2 ^ 2 * 5 ^ 1 := by
    rw [largeEvenSzGroup_eq]
    have := CFSG.LieType.Ree.suzuki_order (a := 0) (K := K) hK'
    rw [this]
    norm_num
  haveI : Finite (LargeEvenSzGroup 0 K) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hs : Group.IsSolvable (LargeEvenSzGroup 0 K) :=
    solv_of_natCard Nat.prime_two (by norm_num : Nat.Prime 5) (by norm_num) hcard
  haveI : Group.IsSolvable (LargeEvenCenterQuot (LargeEvenSzGroup 0 K)) :=
    inferInstanceAs (Group.IsSolvable (_ ⧸ _))
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end Suzuki

theorem datumCore_of_equiv {D D' : Type} [Group D] [Group D'] (e : D ≃* D') (h : DatumCore D') :
    DatumCore D := by
  obtain ⟨E', hs, hna, hperf, hidx, hch⟩ := h
  let eE : ↥E' ≃* ↥(E'.map e.symm.toMonoidHom) :=
    E'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hcD : Nat.card D = Nat.card D' := Nat.card_congr e.toEquiv
  have hcE : Nat.card ↥(E'.map e.symm.toMonoidHom) = Nat.card ↥E' := (Nat.card_congr eE.toEquiv).symm
  refine ⟨E'.map e.symm.toMonoidHom, eE.isSimpleGroup_congr.1 hs, ?_, ?_, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eE x, eE y, fun hh => hxy (eE.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · intro T hT
    have hTm : ⁅T.map e.toMonoidHom, T.map e.toMonoidHom⁆ = T.map e.toMonoidHom := by
      rw [← Subgroup.map_commutator, hT]
    have h1 := hperf _ hTm
    intro x hx
    refine ⟨e x, h1 ⟨x, hx, rfl⟩, ?_⟩
    simp
  · rw [hcD, hcE]
    exact hidx
  · rcases hch with hh | hh
    · exact Or.inl (chevSimple_of_equiv eE.symm hh)
    · exact Or.inr (by rw [hcE]; exact hh)

section G2


theorem datumCore_adjointG2_two {K : Type} [Field K] [Finite K] (hK2 : Nat.card K = 2) :
    DatumCore ↥(adjointGroup .G2 K) := by
  obtain ⟨eC⟩ := nonempty_commutator_subgroup_equiv (adjointGroup .G2 K)
  let eX : ↥(commutator ↥(adjointGroup .G2 K)) ≃* ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ :=
    eC.symm
  have hL := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds K hK2
  have hC := hL.statedClassicalModel (by decide)
  have hU := isUThreeThree_of_stated hC
  have hX6048 := CFSG.AGLEmbeddingD2.McLaughlin.card_of_isUThreeThree hU
  haveI : Finite ↥⁅adjointGroup .G2 K, adjointGroup .G2 K⁆ :=
    Nat.finite_of_card_ne_zero (by rw [hX6048]; norm_num)
  obtain ⟨hXs, -, -⟩ := CFSG.AGLEmbeddingD2.McLaughlin.u33_simple_card_center hU
  have hDcard : Nat.card ↥(adjointGroup .G2 K) = 12096 :=
    CFSG.ComponentClassification.ExcSelector.card_adjointGroup_G2_two hK2
  have hEcard : Nat.card ↥(commutator ↥(adjointGroup .G2 K)) = 6048 := by
    rw [Nat.card_congr eX.toEquiv, hX6048]
  refine ⟨commutator ↥(adjointGroup .G2 K), eX.isSimpleGroup_congr.2 hXs, ?_, ?_,
    Or.inr (by rw [hDcard, hEcard]),
    Or.inl (chevSimple_of_equiv eX (chevSimple_of_uThreeThree hU))⟩
  · obtain ⟨a, b, hab⟩ := nonab_of_simple hXs (by rw [hX6048]; norm_num)
    exact ⟨eX.symm a, eX.symm b,
      fun hh => hab (eX.symm.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · intro T hT
    rw [← hT, commutator_def]
    exact Subgroup.commutator_mono le_top le_top

theorem datumCore_g2 (D : Type) [Group D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.G2, 0, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    DatumCore D := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  obtain ⟨e1⟩ := centerQuot_chevGroup_equiv K .G2
  have hZ : Subgroup.center ↥(adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eQ : AdjointQuotient .G2 K ≃* ↥(adjointGroup .G2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact datumCore_of_equiv ((e.trans e1).trans eQ) (datumCore_adjointG2_two hK2)

end G2

section Tits


theorem datumCore_twF4 (D : Type) [Group D]
    (h : CFSG.Assembly.LargeEvenRawDatum ⟨.twF4, 0, 1⟩ (fun R' _ _ _ => Nonempty (D ≃* R'))) :
    DatumCore D := by
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have ha : (1 - 1) / 2 = 0 := rfl
  rw [ha] at hK e
  have hR : ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩
  obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hR
  obtain ⟨d, hd, ⟨f⟩⟩ := index_of_reeTits_two (Or.inr rfl) hR
  have eD : D ≃* CFSG.Sporadic.Schreier.Tits.titsD := e.trans eT
  have hcard : Nat.card CFSG.Sporadic.Schreier.Tits.titsD = 17971200 :=
    CFSG.Sporadic.Schreier.Tits.card_titsD
  haveI : Finite CFSG.Sporadic.Schreier.Tits.titsD :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hs : IsSimpleGroup CFSG.Sporadic.Schreier.Tits.titsD :=
    CFSG.Sporadic.Schreier.Tits.titsD_simple
  have hna := nonab_of_simple hs (by rw [hcard]; norm_num)
  refine datumCore_of_simple (eD.isSimpleGroup_congr.2 hs) ?_ (Or.inl ?_)
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨eD.symm a, eD.symm b,
      fun hh => hab (eD.symm.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · exact Or.inl ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using hd, ⟨e.trans f⟩⟩

end Tits

section Dispatch


theorem smallDatum_holds : SmallDatum := by
  intro p lab D _ hp hlab hpn hnot h
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hn hl hpn hnot h
  obtain ⟨m, rfl⟩ := hpn
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp at hn
    · exact h0
  have hdiv : p * m / p = m := Nat.mul_div_cancel_left m hp.pos
  rw [hdiv] at hnot h
  have hp2 := hp.two_le
  have hpm : 2 ≤ p * m := by nlinarith
  cases tag <;> simp only [LargeEvenInLambda2] at hnot
  case A =>
    have h1 : rank = 1 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inl (solvable_A11 D h)
  case twA =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inl (solvable_twA21 D h)
  case B =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inr (datumCore_sp21 (Or.inl rfl) D h)
  case C =>
    have h1 : rank = 2 ∧ m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hl.1, fun hr => ?_⟩
      by_cases hm1 : m = 1
      · exact absurd ⟨hr, hm1⟩ hcon
      · omega
    obtain ⟨rfl, rfl⟩ := h1
    exact Or.inr (datumCore_sp21 (Or.inr rfl) D h)
  case D => exact absurd ⟨hm, hl⟩ hnot
  case twD => exact absurd ⟨hm, hl⟩ hnot
  case E6 => exact absurd ⟨hm, hl⟩ hnot
  case E7 => exact absurd ⟨hm, hl⟩ hnot
  case E8 => exact absurd ⟨hm, hl⟩ hnot
  case F4 => exact absurd ⟨hm, hl⟩ hnot
  case twE6 => exact absurd ⟨hm, hl⟩ hnot
  case triD4 => exact absurd ⟨hm, hl⟩ hnot
  case G2 =>
    have h1 : m = 1 := by
      by_contra hcon
      apply hnot
      exact ⟨hm, hl.1, by omega⟩
    obtain rfl := h1
    obtain rfl := hl.1
    exact Or.inr (datumCore_g2 D h)
  case twB2 =>
    obtain ⟨hr, hodd, h3⟩ := hl
    have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
    have h1 : m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hr, hmodd, ?_⟩
      obtain ⟨k, hk⟩ := hmodd
      omega
    obtain rfl := h1
    obtain rfl := hr
    exact Or.inl (solvable_twB2 D h)
  case twF4 =>
    obtain ⟨hr, hodd, h3⟩ := hl
    have hmodd : Odd m := (Nat.odd_mul.1 hodd).2
    have h1 : m = 1 := by
      by_contra hcon
      apply hnot
      refine ⟨hm, hr, hmodd, ?_⟩
      obtain ⟨k, hk⟩ := hmodd
      omega
    obtain rfl := h1
    obtain rfl := hr
    exact Or.inr (datumCore_twF4 D h)
  case B2der =>
    exfalso
    have h1 : p * m = 1 := hl.2
    have : p ∣ 1 := ⟨m, h1.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  case G2der =>
    exfalso
    have h1 : p * m = 1 := hl.2
    have : p ∣ 1 := ⟨m, h1.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  case twF4der =>
    exfalso
    have h1 : p * m = 1 := hl.2
    have : p ∣ 1 := ⟨m, h1.symm⟩
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)

end Dispatch

end Res

end FR

end CFSG.LocalAnalysis.GLTheoremA
