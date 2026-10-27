module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263CILift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResTD4
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021FixHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL613Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S628Common
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.StrongMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma32
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yDefs
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.C22PfH
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import Certificates.Certificate214002
public import Certificates.Certificate214003
public import Certificates.Certificate5118

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.Assembly CFSG.StandardType
  CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremA.FR.Res
open CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (PiField glPi slPi ModThree)
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor)
open scoped commutatorElement

private def T263Core3 (Y : Type) [Group Y] : Prop :=
  ∃ E : Subgroup Y, IsSimpleGroup ↥E ∧ (∃ x y : ↥E, x * y ≠ y * x) ∧
    (∀ T : Subgroup Y, ⁅T, T⁆ = T → T ≤ E) ∧ 3 ∣ Nat.card ↥E

section Pure

private theorem t263CI_core3_of_equiv {S : Type} [Group S] {C : Subgroup S} {Y : Type} [Group Y]
    (e : ↥C ≃* Y) (h : T263Core3 Y) :
    ∃ E : Subgroup S, E ≤ C ∧ IsSimpleGroup ↥E ∧ (∃ x y : ↥E, x * y ≠ y * x) ∧
      (∀ T : Subgroup S, T ≤ C → ⁅T, T⁆ = T → T ≤ E) ∧ 3 ∣ Nat.card ↥E := by
  obtain ⟨E', hs, hna, hperf, h3⟩ := h
  let e1 : ↥E' ≃* ↥(E'.map e.symm.toMonoidHom) :=
    E'.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  let e2 : ↥(E'.map e.symm.toMonoidHom) ≃* ↥((E'.map e.symm.toMonoidHom).map C.subtype) :=
    (E'.map e.symm.toMonoidHom).equivMapOfInjective C.subtype C.subtype_injective
  let eE : ↥E' ≃* ↥((E'.map e.symm.toMonoidHom).map C.subtype) := e1.trans e2
  have hcE : Nat.card ↥((E'.map e.symm.toMonoidHom).map C.subtype) = Nat.card ↥E' :=
    (Nat.card_congr eE.toEquiv).symm
  refine ⟨(E'.map e.symm.toMonoidHom).map C.subtype, Subgroup.map_subtype_le _,
    eE.isSimpleGroup_congr.1 hs, ?_, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hna
    exact ⟨eE x, eE y, fun hh => hxy (eE.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · intro T hTC hTp
    have hTT : (T.subgroupOf C).map C.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTC
    have hT'p : ⁅T.subgroupOf C, T.subgroupOf C⁆ = T.subgroupOf C := by
      apply Subgroup.map_injective C.subtype_injective
      rw [Subgroup.map_commutator, hTT, hTp]
    have hTm : ⁅(T.subgroupOf C).map e.toMonoidHom, (T.subgroupOf C).map e.toMonoidHom⁆ =
        (T.subgroupOf C).map e.toMonoidHom := by
      rw [← Subgroup.map_commutator, hT'p]
    have h1 := hperf _ hTm
    rw [← hTT]
    refine Subgroup.map_mono (fun x hx => ?_)
    exact ⟨e x, h1 ⟨x, hx, rfl⟩, by simp⟩
  · rw [hcE]
    exact h3

private theorem t263CI_three_dvd_sq_sub_one (f : ℕ) : 3 ∣ (2 ^ f) ^ 2 - 1 := by
  have h : (2 ^ f) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num [Nat.pow_mod]
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  omega

end Pure

section Dispatch


section G2

variable {k : Type} [Field k] [Finite k] {f : ℕ}

private theorem t263CI_core3_adjointG2 (hf : 2 ≤ f) (hk : Nat.card k = 2 ^ f) :
    T263Core3 ↥(adjointGroup .G2 k) := by
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hq := CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card (K := k) (by omega)
  obtain ⟨hs, a, b, hab⟩ :=
    CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux.isSimple_of_isQuasisimple_center_bot hq
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have hadm : StatedLieAdmissible .G2 0 2 f := ⟨Nat.prime_two, by omega, rfl, by omega⟩
  have hZ : Subgroup.center ↥(adjointGroup .G2 k) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eQ : AdjointQuotient .G2 k ≃* ↥(adjointGroup .G2 k) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hC : ChevalleyExceptionalModel ↥(adjointGroup .G2 k) .G2 2 f :=
    ⟨hadm, k, inferInstance, inferInstance, hk, ⟨eQ.symm⟩⟩
  have hcard : Nat.card ↥(adjointGroup .G2 k) = ordG2 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hC
  refine ⟨⊤, (Subgroup.topEquiv).isSimpleGroup_congr.2 hs, ⟨⟨a, trivial⟩, ⟨b, trivial⟩,
    fun hh => hab (congrArg Subtype.val hh)⟩, fun T _ => le_top, ?_⟩
  rw [Subgroup.card_top, hcard]
  unfold ordG2
  exact Dvd.dvd.mul_left (t263CI_three_dvd_sq_sub_one f) _

end G2

section ProjImage

variable {π : Bool} {f : ℕ} {F : Type} [Field F]

private theorem t263CI_core3_projImage (hK : PiField π 2 f F) (hmod : ModThree π (2 ^ f)) (hq2 : 2 < 2 ^ f) :
    T263Core3 ↥(CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)) := by
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
  have hc3 := Sec13.card_projImage_slPi_mul_three hK hmod
  have h3 : 3 ∣ Nat.card ↥(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)) := by
    have hq2' := t263CI_three_dvd_sq_sub_one f
    obtain ⟨u, hu⟩ := hq2'
    cases π
    ·
      have hm : (2 ^ f) % 3 = 2 := hmod
      obtain ⟨v, hv⟩ : 3 ∣ (2 ^ f) ^ 3 + 1 := by
        have : (2 ^ f) ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hm]
        omega
      simp only [Bool.cond_false] at hc3
      rw [hu, hv] at hc3
      have : Nat.card ↥(CFSG.PGLModel.projImage (slPi false 3 (2 ^ f) F)) * 3 =
          3 * (3 * ((2 ^ f) ^ 3 * u * v)) := by rw [hc3]; ring
      exact ⟨(2 ^ f) ^ 3 * u * v, by omega⟩
    ·
      have hm : (2 ^ f) % 3 = 1 := hmod
      obtain ⟨v, hv⟩ : 3 ∣ (2 ^ f) ^ 3 - 1 := by
        have : (2 ^ f) ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hm]
        have h1 : 1 ≤ (2 ^ f) ^ 3 := Nat.one_le_pow _ _ (by positivity)
        omega
      simp only [Bool.cond_true] at hc3
      rw [hu, hv] at hc3
      have : Nat.card ↥(CFSG.PGLModel.projImage (slPi true 3 (2 ^ f) F)) * 3 =
          3 * (3 * ((2 ^ f) ^ 3 * u * v)) := by rw [hc3]; ring
      exact ⟨(2 ^ f) ^ 3 * u * v, by omega⟩
  refine ⟨(CFSG.PGLModel.projImage (slPi π 3 (2 ^ f) F)).subgroupOf
      (CFSG.PGLModel.projImage (glPi π 3 (2 ^ f) F)), eE.isSimpleGroup_congr.2 hs, ?_, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ :=
      CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperf
    exact ⟨eE.symm a, eE.symm b,
      fun hh => hab (eE.symm.injective (by rw [map_mul, map_mul]; exact hh))⟩
  · intro T hT
    rw [← hT, ← hcomm, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · rw [Nat.card_congr eE.toEquiv]
    exact h3

end ProjImage

theorem t263CI_td4_core3 {G : Type} [Group G] [Finite G] {X L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hX : GLAPComponent 3 X L) (hb3 : b ^ 3 = 1)
    (hNI : NonInner 3 b L) {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid)
    (hq2 : q.p = 2) (hf2 : 2 ≤ q.exponent)
    (eS : PSimple 3 L ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) :
    ∃ E : Subgroup (PSimple 3 L), E ≤ FP.fixSub (indAut 3 L b hb) ∧ IsSimpleGroup ↥E ∧
      (∃ x y : ↥E, x * y ≠ y * x) ∧
      (∀ T : Subgroup (PSimple 3 L), T ≤ FP.fixSub (indAut 3 L b hb) → ⁅T, T⁆ = T → T ≤ E) ∧
      3 ∣ Nat.card ↥E := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
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
    (FR.fixSubEquivCongr e' (indAut 3 L b hb)).trans
      (MulEquiv.subgroupCongr (fixSub_eq_autFix _))
  suffices key : ∃ (Y : Type) (_ : Group Y),
      Nonempty (↥(FP.fixSub (indAut 3 L b hb)) ≃* Y) ∧ T263Core3 Y by
    obtain ⟨Y, _, ⟨e⟩, hc⟩ := key
    exact t263CI_core3_of_equiv e hc
  set φ := MulAut.congr e' (indAut 3 L b hb) with hφ
  rcases CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv
      hf hK' hσ' hφ3 hφout with ⟨β', hβ' | hβ'⟩ | ⟨e2⟩
  ·
    have eA : ↥(Sec4.autFix φ) ≃* ↥(Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [hβ', ← CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.mulAut_congr_eq]
      exact Sec4.autFixCongrEquiv β' _
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨eG⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
        (ℓ := 2) (by norm_num) hf (Or.inl rfl) hK' σ hσ'
    have hkc : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ q.exponent :=
      CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hf hK' σ hσ'
    haveI : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
    exact ⟨_, inferInstance, ⟨eFix.trans (eA.trans ((MulEquiv.subgroupCongr rfl).trans eG))⟩,
      t263CI_core3_adjointG2 hf2 hkc⟩
  ·
    have eA : ↥(Sec4.autFix φ) ≃* ↥(Sec4.autFix (fieldActor (t := TwistTag.D4) σ σ)) := by
      rw [hβ', ← CFSG.RankThree.PartTwo.Sec8.LangTwistedProof.mulAut_congr_eq]
      exact (Sec4.autFixCongrEquiv β' _).trans (MulEquiv.subgroupCongr (autFix_inv'' _))
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨eG⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_fixSubgroup_fieldActor_equiv_G2
        (ℓ := 2) (by norm_num) hf (Or.inl rfl) hK' σ hσ'
    have hkc : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = 2 ^ q.exponent :=
      CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_two hf hK' σ hσ'
    haveI : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := Subtype.finite
    exact ⟨_, inferInstance, ⟨eFix.trans (eA.trans ((MulEquiv.subgroupCongr rfl).trans eG))⟩,
      t263CI_core3_adjointG2 hf2 hkc⟩
  ·
    obtain ⟨e2⟩ := e2
    rcases Nat.even_or_odd q.exponent with hfe | hfo
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0Even_holds q.exponent hfe hf K σ hK' hσ'
      have hPi : PiField true 2 q.exponent F := ⟨Nat.prime_two, hf, hF⟩
      have hq4 : 2 < 2 ^ q.exponent :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact ⟨_, inferInstance, ⟨eFix.trans (e2.trans e3)⟩,
        t263CI_core3_projImage hPi (modThree_two_pow (π := true) hfe) hq4⟩
    · obtain ⟨F, _, _, hF, ⟨e3⟩⟩ :=
        CFSG.RankThree.PartTwo.Sec8.kF82D4SecondCentY0_holds q.exponent hfo K σ hK' hσ'
      have hPi : PiField false 2 q.exponent F := ⟨Nat.prime_two, hf, hF⟩
      have hq4 : 2 < 2 ^ q.exponent :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf2)
      exact ⟨_, inferInstance, ⟨eFix.trans (e2.trans e3)⟩,
        t263CI_core3_projImage hPi (modThree_two_pow (π := false) hfo) hq4⟩

end Dispatch

end CFSG.LocalAnalysis.GLTheoremA.T263

end
