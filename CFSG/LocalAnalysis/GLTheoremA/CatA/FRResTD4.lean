module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011CentTD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriD4Outer
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
public import CFSG.Adapters.RankThreeOutcomesReverse
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FR

namespace Res

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (PiField glPi slPi ModThree)
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)
open scoped commutatorElement

theorem modThree_two_pow {π : Bool} {f : ℕ} (h : cond π (Even f) (Odd f)) : ModThree π (2 ^ f) := by
  cases π
  · obtain ⟨m, rfl⟩ := h
    simp only [ModThree, Bool.cond_false]
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  · obtain ⟨m, rfl⟩ := h
    simp only [ModThree, Bool.cond_true]
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num

section ProjImage

variable {π : Bool} {f : ℕ} {F : Type} [Field F]

theorem chevSimple_projImage_sl (hK : PiField π 2 f F) (hf : cond π 2 3 ≤ f) :
    IsChevSimple 2 ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) := by
  haveI := hK.finite
  cases π
  · have hadm : StatedLieAdmissible .PSU 3 2 f := by
      refine ⟨Nat.prime_two, by simp at hf; omega, by norm_num, ?_⟩
      intro h
      simp only [Prod.mk.injEq] at h
      have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by simpa using hf)
      omega
    have hm : StatedClassicalModel ↥(CFSG.PGLModel.projImage (slPi false 3 (2 ^ f) F)) .PSU 3 2 f :=
      ⟨hadm, F, inferInstance, inferInstance, by simpa [Sec4.piCard] using hK.card,
        ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (slPi false 3 (2 ^ f) F)).symm⟩⟩
    rcases classical_two_cases hm with ⟨d, hd, ⟨e⟩⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
    · exact Or.inl ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using hd, ⟨e⟩⟩
    all_goals exact absurd h (by decide)
  · have hadm : StatedLieAdmissible .PSL 3 2 f := by
      refine ⟨Nat.prime_two, by simp at hf; omega, by norm_num, ?_, ?_⟩
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
    have hm : StatedClassicalModel ↥(CFSG.PGLModel.projImage (slPi true 3 (2 ^ f) F)) .PSL 3 2 f :=
      ⟨hadm, F, inferInstance, inferInstance, by simpa [Sec4.piCard] using hK.card,
        ⟨(CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (slPi true 3 (2 ^ f) F)).symm⟩⟩
    rcases classical_two_cases hm with ⟨d, hd, ⟨e⟩⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
    · exact Or.inl ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using hd, ⟨e⟩⟩
    · exact absurd h (by decide)
    · simp at hf; omega
    · exact absurd h (by decide)

theorem coreAbs_projImage (hK : PiField π 2 f F) (hmod : ModThree π (2 ^ f)) (hq2 : 2 < 2 ^ f)
    (hf : cond π 2 3 ≤ f) : CoreAbs ↥(CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)) := by
  haveI := hK.finite
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) F →* _)
      (QuotientGroup.mk'_surjective _)
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    fun h => by subst h; exact hK.unitary
  have hSP : CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F) ≤
      CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F) := Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  haveI : Finite ↥(CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)) := Subtype.finite
  have hcomm := Sec13.commutator_projImage_glPi hK hq2
  let eE : ↥((CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)).subgroupOf
      (CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F))) ≃* ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) :=
    Subgroup.subgroupOfEquivOfLe hSP
  have hs : IsSimpleGroup ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hperf : Group.IsPerfect ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  haveI : Nontrivial ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) := hs.toNontrivial
  have hc3 : Nat.card ↥(CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)) =
      3 * Nat.card ↥((CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)).subgroupOf
        (CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F))) := by
    rw [Nat.card_congr eE.toEquiv, mul_comm,
      Sec16.ProofKSL3Two.card_projImage_glPi hK, Sec13.card_slPi_three hK,
      ← Sec13.card_projImage_slPi_mul_three hK hmod]
  refine ⟨(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)).subgroupOf
      (CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)), eE.isSimpleGroup_congr.2 hs, ?_, ?_, ?_,
    Or.inl (chevSimple_of_equiv eE (chevSimple_projImage_sl hK hf))⟩
  · obtain ⟨a, b, hab⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperf
    exact ⟨eE.symm a, eE.symm b,
      fun hh => hab (eE.symm.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · intro T hT
    rw [← hT, ← hcomm, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · rw [hc3, FP.twoPart_mul_odd (by decide) Nat.card_pos.ne']
    omega

end ProjImage

section G2


variable {k : Type} [Field k] [Finite k] {f : ℕ}

theorem chevSimple_adjointG2 (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f) :
    IsChevSimple 2 ↥(adjointGroup .G2 k) := by
  have hadm : StatedLieAdmissible .G2 0 2 f := ⟨Nat.prime_two, by omega, rfl, by
    calc 3 ≤ 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf⟩
  have hZ : Subgroup.center ↥(adjointGroup .G2 k) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eQ : AdjointQuotient .G2 k ≃* ↥(adjointGroup .G2 k) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hC : ChevalleyExceptionalModel ↥(adjointGroup .G2 k) .G2 2 f :=
    ⟨hadm, k, inferInstance, inferInstance, hk, ⟨eQ.symm⟩⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := index_of_chevalleyExceptional (by simp [chevalleyExceptionalTags]) hC
  exact Or.inl ⟨TauCeti.CFSGIndex.lie d, by simpa [onLie] using hd, ⟨e⟩⟩

theorem coreAbs_adjointG2 (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) : CoreAbs ↥(adjointGroup .G2 k) := by
  rcases Nat.eq_or_lt_of_le hf with h1 | h2
  · subst h1
    exact coreAbs_of_datumCore (datumCore_adjointG2_two (by simpa using hk))
  · have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2
    have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (K := k)
      (by omega)
    obtain ⟨hs, a, b, hab⟩ := CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.isSimple_of_isQuasisimple_center_bot hq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
    refine ⟨⊤, (Subgroup.topEquiv).isSimpleGroup_congr.2 hs, ⟨⟨a, trivial⟩, ⟨b, trivial⟩,
      fun hh => hab (congrArg Subtype.val hh)⟩, fun T _ => le_top, ?_,
      Or.inl (chevSimple_of_equiv Subgroup.topEquiv (chevSimple_adjointG2 h2 hk))⟩
    rw [Subgroup.card_top]
    exact Nat.le_mul_of_pos_left _ (by norm_num)

end G2

section TD4


theorem td4_index' {S : Type} [Group S]
    (h : catalogIs S (onLie fun | .trialityD4 _ => True | _ => False)) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | trialityD4 q => exact ⟨q, hv, ⟨e⟩⟩
  | _ => exact hP.elim

theorem td4_blueprint_model' {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    CFSG.Blueprint.LieModel S .trialityD4 0 q.p q.exponent := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hto : 0 < (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by decide
  have hKc : Nat.card (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order)) =
      (q.p ^ q.exponent) ^ (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hto.ne'), pow_mul]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.trialityD4 q hv
    (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order))
    (by rw [hKc, TauCeti.PrimePower.card_def]) (iterateFrobenius _ q.p q.exponent)
    (fun x => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order), inferInstance,
      inferInstance, hKc, iterateFrobenius _ q.p q.exponent,
      fun x => by rw [iterateFrobenius_def], ⟨e.trans b.symm⟩⟩
  exact Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hC⟩)

theorem td4_odd_false' {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp : q.p ≠ 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hchev : IsChevSimple 2 S) :
    False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hodd := td4_blueprint_model' hv e
  have hadm := CFSG.Blueprint.LieModel.admissible hodd
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hcard := (hO S .trialityD4 0 q.p q.exponent hadm hodd).2.1
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hQ : 3 ≤ q.p ^ q.exponent := le_trans hp3 (Nat.le_self_pow q.exponent_pos.ne' _)
  have hNS : Nat.card S = (q.p ^ q.exponent) ^ 12 * ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
      ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) := by
    simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] using hcard
  have hbig : 3 ^ 12 ≤ Nat.card S := by
    rw [hNS]
    have h6 : 2 ≤ (q.p ^ q.exponent) ^ 6 := le_trans (by omega) (Nat.pow_le_pow_left hQ 6)
    have h2 : 2 ≤ (q.p ^ q.exponent) ^ 2 := le_trans (by omega) (Nat.pow_le_pow_left hQ 2)
    have hX : 0 < ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
        ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have h12 : 3 ^ 12 ≤ (q.p ^ q.exponent) ^ 12 := Nat.pow_le_pow_left hQ 12
    calc 3 ^ 12 ≤ (q.p ^ q.exponent) ^ 12 := h12
      _ ≤ (q.p ^ q.exponent) ^ 12 * (((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
          ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1)) :=
        Nat.le_mul_of_pos_right _ hX
      _ = _ := by ring
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases hchev with ⟨t', n', f', hX⟩ | ⟨e6⟩ | hPSU
  · have hodd' : CFSG.Blueprint.OddLieType S :=
      ⟨.trialityD4, 0, q.p, q.exponent, q.prime_p, hp, hadm, hodd⟩
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO hX hodd' with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 2) = 60 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 2) = 1 from rfl] at h
      norm_num at hbig
      omega
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 1) = 168 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 1) = 1 from rfl] at h
      norm_num at hbig
      omega
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 from rfl] at h
      norm_num at hbig
      omega
  · obtain ⟨e6'⟩ := e6
    have h6 : Nat.card S = 360 := by
      rw [Nat.card_congr e6'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    norm_num at hbig
    omega
  · have hL : CFSG.Blueprint.LieModel S .PSU 3 3 1 :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩
    have h := (hO S .PSU 3 3 1 (CFSG.Blueprint.LieModel.admissible hL) hL).2.1
    rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 from by decide,
      show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (3 ^ 1) = 1 from rfl] at h
    norm_num at hbig
    omega


theorem fixSub_eq_autFix {X : Type} [Group X] (α : MulAut X) :
    FP.fixSub α = Sec4.autFix α := Subgroup.ext fun _ => Iff.rfl

theorem autFix_inv'' {X : Type} [Group X] (α : MulAut X) : Sec4.autFix α⁻¹ = Sec4.autFix α := by
  ext x
  rw [Sec4.mem_autFix, Sec4.mem_autFix]
  constructor
  · intro h
    have := congrArg α h
    rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
    exact this.symm
  · intro h
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact h.symm

theorem td4Core_holds : TD4Core := by
  intro G _ _ X L b hb hX hchev hb3 hTD4 hNI hT
  obtain ⟨T, hTC, hTp, hTne⟩ := hT
  have hp3 : Nat.Prime 3 := Nat.prime_three
  obtain ⟨q, hv, ⟨eS⟩⟩ := td4_index' hTD4
  have hq2 : q.p = 2 := by
    by_contra hne
    exact td4_odd_false' hv hne eS hchev
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eC⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK' : Nat.card K = (2 ^ q.exponent) ^ 3 := by rw [hK, hq2]
  have hσ' : ∀ c, σ c = c ^ 2 ^ q.exponent := fun c => by rw [hσ c, hq2]
  have hβ3 : indAut 3 L b hb ^ 3 = 1 := by
    have : indAut 3 L b hb = (chevAut 3 L ⟨b, hb⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [this, inv_pow, chevAut_pow_eq_one 3 L hb hb3, inv_one]
  have hβout : indAut 3 L b hb ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 L) :=
    fun h => hNI.2 ((indAut_mem_inner_iff hp3 hX hb).1 h)
  let e' : PSimple 3 L ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom := eS.trans eC
  have hφ3 : MulAut.congr e' (indAut 3 L b hb) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hφout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut (MulAut.congr e' (indAut 3 L b hb)) :=
    fun h => hβout ((FQ.congr_mem_range_conj e' _).1 h)
  have eFix : ↥(FP.fixSub (indAut 3 L b hb)) ≃* ↥(Sec4.autFix (MulAut.congr e' (indAut 3 L b hb))) :=
    (fixSubEquivCongr e' (indAut 3 L b hb)).trans
      (MulEquiv.subgroupCongr (fixSub_eq_autFix _))
  suffices key : ∃ (Y : Type) (_ : Group Y),
      Nonempty (↥(FP.fixSub (indAut 3 L b hb)) ≃* Y) ∧ CoreAbs Y by
    obtain ⟨Y, _, ⟨e⟩, hc⟩ := key
    exact coreSub_of_equiv e hc
  set φ := MulAut.congr e' (indAut 3 L b hb) with hφ
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv
      hf hK' hσ' hφ3 hφout with ⟨β', hβ' | hβ'⟩ | ⟨e2⟩
  ·
    have eA : ↥(Sec4.autFix φ) ≃* ↥(Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [hβ', ← CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.mulAut_congr_eq]
      exact Sec4.autFixCongrEquiv β' _
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨eG⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
      (ℓ := 2) (by norm_num) hf (Or.inl rfl) hK' σ hσ'
    have hkc : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ q.exponent :=
      CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hf hK' σ hσ'
    haveI : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
    exact ⟨_, inferInstance, ⟨eFix.trans (eA.trans ((MulEquiv.subgroupCongr rfl).trans eG))⟩,
      coreAbs_adjointG2 hf hkc⟩
  ·
    have eA : ↥(Sec4.autFix φ) ≃* ↥(Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [hβ', ← CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.mulAut_congr_eq]
      exact (Sec4.autFixCongrEquiv β' _).trans (MulEquiv.subgroupCongr (autFix_inv'' _))
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨eG⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
      (ℓ := 2) (by norm_num) hf (Or.inl rfl) hK' σ hσ'
    have hkc : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ q.exponent :=
      CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hf hK' σ hσ'
    haveI : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
    exact ⟨_, inferInstance, ⟨eFix.trans (eA.trans ((MulEquiv.subgroupCongr rfl).trans eG))⟩,
      coreAbs_adjointG2 hf hkc⟩
  ·
    obtain ⟨e2⟩ := e2
    rcases Nat.even_or_odd q.exponent with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds q.exponent hfe hf K σ hK' hσ'
      have hPi : PiField true 2 q.exponent F := ⟨Nat.prime_two, hf, hF⟩
      have hf2 : 2 ≤ q.exponent := by
        obtain ⟨k, hk⟩ := hfe
        omega
      have hq4 : 2 < 2 ^ q.exponent :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact ⟨_, inferInstance, ⟨eFix.trans (e2.trans e3)⟩,
        coreAbs_projImage hPi (modThree_two_pow (π := true) hfe) hq4 (by simpa using hf2)⟩
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds q.exponent hfo K σ
          hK' hσ'
      have hPi : PiField false 2 q.exponent F := ⟨Nat.prime_two, hf, hF⟩
      by_cases h1 : q.exponent = 1
      · exfalso
        have hsol : Group.IsSolvable ↥(CFSG.PGLModel.projImage (glPi false 3 (2 ^ q.exponent) F)) :=
          Sec13.isSolvable_projImage_glPi_two hPi (by simp [h1])
        let eT := eFix.trans (e2.trans e3)
        haveI : Group.IsSolvable ↥(FP.fixSub (indAut 3 L b hb)) :=
          Group.isSolvable_of_isSolvable_injective (f := eT.toMonoidHom) eT.injective
        exact false_of_perfect_solvable hTC hTp hTne inferInstance
      · have hf3 : 3 ≤ q.exponent := by
          obtain ⟨k, hk⟩ := hfo
          omega
        have hq4 : 2 < 2 ^ q.exponent :=
          lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
        exact ⟨_, inferInstance, ⟨eFix.trans (e2.trans e3)⟩,
          coreAbs_projImage hPi (modThree_two_pow (π := false) hfo) hq4 (by simpa using hf3)⟩

end TD4

end Res

end FR

end CFSG.LocalAnalysis.GLTheoremA
