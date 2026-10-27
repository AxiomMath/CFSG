module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.NotA6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.FixPlaneRee
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Sporadic.Schreier.Tits TauCeti

set_option linter.unusedSectionVars false

noncomputable def quotientCenterEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem isEmpty_quotient_center_alt6_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsEmpty ((B ⧸ Subgroup.center B) ≃* alternatingGroup (Fin 6))) :
    IsEmpty ((A ⧸ Subgroup.center A) ≃* alternatingGroup (Fin 6)) :=
  ⟨fun f => h.false ((quotientCenterEquiv e).symm.trans f)⟩

theorem exists_noncomm_of_isQuasisimple {T : Type*} [Group T] (hq : CFSG.IsQuasisimple T) :
    ∃ x y : T, x * y ≠ y * x := by
  obtain ⟨a, b, hab⟩ := ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian T
    (LieSemisimple.open_isQuasisimple hq)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨x, y, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem lieCompExport_of_quasisimple_fix {q : ℕ} {S : Type} [Group S] [Finite S]
    {β : MulAut S} (hq : CFSG.IsQuasisimple ↥(fixSubgroup β))
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), LieFactorData q X ∧
      ∃ f : X →* ↥(fixSubgroup β), Function.Surjective f ∧ f.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((↥(fixSubgroup β) ⧸ Subgroup.center ↥(fixSubgroup β)) ≃*
      alternatingGroup (Fin 6))) :
    LieCompExport q β := by
  haveI hn : ((fixSubgroup β).subgroupOf (fixSubgroup β)).Normal := by
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hsol : Group.IsSolvable
      (↥(fixSubgroup β) ⧸ (fixSubgroup β).subgroupOf (fixSubgroup β)) := by
    haveI : Subsingleton (↥(fixSubgroup β) ⧸ (fixSubgroup β).subgroupOf (fixSubgroup β)) := by
      refine ⟨fun a b => ?_⟩
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact QuotientGroup.eq.2 (by rw [Subgroup.mem_subgroupOf]; exact SetLike.coe_mem _)
    infer_instance
  exact lieCompExport_of_normal_quasisimple le_rfl hq hsol hX hA6

theorem map_commutator_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (commutator A).map e.toMonoidHom = commutator B := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

noncomputable def commutatorMulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    ↥(commutator A) ≃* ↥(commutator B) :=
  ((commutator A).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_commutator_mulEquiv e))

noncomputable def commutatorSubgroupEquiv {G : Type*} [Group G] (C : Subgroup G) :
    ↥⁅C, C⁆ ≃* ↥(commutator ↥C) :=
  (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator C).symm).trans
    ((commutator ↥C).equivMapOfInjective C.subtype C.subtype_injective).symm

section Tits


theorem reeTitsModel_commutator_reeFixed {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) :
    ReeTitsModel ↥(commutator ↥(reeFixed ReeTag.F4 k 0)) .Tits 2 1 := by
  refine ⟨⟨Nat.prime_two, le_rfl, ⟨rfl, rfl, rfl⟩⟩, 0, rfl, k, inferInstance, inferInstance, ?_,
    ⟨?_⟩⟩
  · rw [hk, pow_one]
  · exact ((QuotientGroup.quotientMulEquivOfEq (center_commutator_reeFixed hk)).trans
      QuotientGroup.quotientBot).symm.trans
      (CFSG.LieType.BorelTits.derivedCentralQuotientEquiv _
        ((MulEquiv.subgroupCongr (reeFixedGroup_eq_map_reeFixed ReeTag.F4 k 0)).trans
          ((reeFixed ReeTag.F4 k 0).equivMapOfInjective _ Subtype.val_injective).symm)).symm

theorem nonempty_commutator_reeFixed_equiv_cat_tits {k : Type} [Field k] [Finite k]
    [CharP k ReeTag.F4.prime] (hk : Nat.card k = 2) (hv : LieTypeIndex.tits.Valid) :
    Nonempty (↥(commutator ↥(reeFixed ReeTag.F4 k 0)) ≃* (CFSGIndex.lie ⟨.tits, hv⟩).Group) := by
  obtain ⟨e₁⟩ := titsModelEquiv _ 2 1 (reeTitsModel_commutator_reeFixed hk)
  obtain ⟨e₂⟩ := titsModelEquiv (CFSGIndex.lie ⟨.tits, hv⟩).Group 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩)
  exact ⟨e₁.trans e₂.symm⟩

end Tits

section Ree


theorem lieCompExport_reeGamma_inner {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = 3) :
    LieCompExport 2 (MulAut.conj y) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K
    hK y hy
  have hF'card : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  haveI : Fintype (GaloisField 2 (2 * (2 * a + 1))) := Fintype.ofFinite _
  have hF'fcard : Fintype.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF'card
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hF'card (by omega)).1
  let E : ↥(fixSubgroup (MulAut.conj y)) ≃*
      ↥(CFSG.Open.StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) :=
    (MulEquiv.subgroupCongr (CFSG.HardMathSupport.Dickson.SuzukiReeB.fixSubgroup_conj y)).trans e
  have hmq : ((3 : ℕ), 2 ^ (2 * a + 1)) ≠ ((3 : ℕ), 2) := by
    intro h
    have h2 : 2 ^ (2 * a + 1) = 2 := (Prod.mk.inj h).2
    have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hch : ringChar (GaloisField 2 (2 * (2 * a + 1))) = 2 :=
    ringChar.eq (GaloisField 2 (2 * (2 * a + 1))) 2
  have hFD : LieFactorData 2
      ↥(CFSG.Open.StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) := by
    have h := suFactorFacts_holds (GaloisField 2 (2 * (2 * a + 1))) 3 (2 ^ (2 * a + 1))
      hF'fcard (by norm_num) hmq
    rw [hch] at h
    exact h
  haveI : Finite ↥(CFSG.Open.StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) :=
    Finite.of_equiv _ E.toEquiv
  refine lieCompExport_of_quasisimple_fix (q := 2) (CFSG.LocalCores.isQuasisimple_of_mulEquiv
    E.symm hq) ⟨_, inferInstance, inferInstance, hFD, E.symm.toMonoidHom, E.symm.surjective, ?_⟩
    (isEmpty_quotient_center_alt6_of_equiv E
      (suAltSixFacts_holds (GaloisField 2 (2 * (2 * a + 1))) 3 (2 ^ (2 * a + 1)) hF'fcard
        (by norm_num)))
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have : x = 1 := E.symm.injective (by rw [map_one]; exact hx)
  rw [this]
  exact one_mem _

theorem exists_fixSubgroup_fieldAut_equiv {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ (b : ℕ) (_ : Nat.card (fixSubfield σ) = 2 ^ (2 * b + 1))
      (_ : CharP (fixSubfield σ) ReeTag.F4.prime),
      Nonempty (↥(fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)) ≃*
        ↥(ReeTag.F4.reeGamma (fixSubfield σ) b)) := by
  classical
  obtain ⟨b, -, hkcard, hfixed⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.largeRee_fixed_data_odd hK hp hp2 σ hσ
  have : Finite (fixSubfield σ) := Subtype.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP (fixSubfield σ) ReeTag.F4.prime := by
    have : Fintype (fixSubfield σ) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (f := 2 * b + 1) (by
      rw [← Nat.card_eq_fintype_card, hkcard]
      rfl)
  haveI := hchar
  have hFix : fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ) =
      (ReeTag.F4.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _) := rfl
  refine ⟨b, hkcard, hchar, ⟨?_⟩⟩
  exact (((fixSubgroup (ReeTag.F4.reeGammaFieldAut K a σ)).equivMapOfInjective
      (ReeTag.F4.reeGamma K a).subtype (ReeTag.F4.reeGamma K a).subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [hFix]; exact hfixed))).trans
    ((ReeTag.F4.reeGamma (fixSubfield σ) b).equivMapOfInjective _
      (baseChangeGL_injective (τ := ReeTag.F4.tag) (fixSubfield σ).subtype)).symm

theorem lieCompExport_reeGamma_fieldAut {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K)
    (hσ : orderOf σ = 3) : LieCompExport 2 (ReeTag.F4.reeGammaFieldAut K a σ) := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨b, hkcard, hchar, ⟨eC⟩⟩ := exists_fixSubgroup_fieldAut_equiv hK Nat.prime_three
    (by norm_num) σ hσ
  haveI := hchar
  haveI : Finite (fixSubfield σ) := Subtype.finite
  haveI : Finite (ModGL ReeTag.F4.tag (fixSubfield σ)) := finite_modGL
  haveI : Finite ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) := Subtype.finite
  set δ := ReeTag.F4.reeGammaFieldAut K a σ with hδ
  haveI : Finite ↥(fixSubgroup δ) := Subtype.finite
  rcases Nat.eq_zero_or_pos b with rfl | hb
  ·
    have hk2 : Nat.card (fixSubfield σ) = 2 := by simpa using hkcard
    have hv : LieTypeIndex.tits.Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simp [LieTypeIndex.inStandardRange_iff]
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨eT⟩ := nonempty_commutator_reeFixed_equiv_cat_tits hk2 hv
    let eJT : ↥⁅fixSubgroup δ, fixSubgroup δ⁆ ≃*
        ↥(commutator ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0)) :=
      (commutatorSubgroupEquiv (fixSubgroup δ)).trans ((commutatorMulEquiv eC).trans
        (commutatorMulEquiv (ReeTag.reeFixedEquivReeGamma (fixSubfield σ) 0).symm))
    let eJ : ↥⁅fixSubgroup δ, fixSubgroup δ⁆ ≃* (CFSGIndex.lie ⟨.tits, hv⟩).Group := eJT.trans eT
    have hT := (CFSG.LieType.Simplicity.titsData (fixSubfield σ) hk2).isQuasisimple hk2
    haveI : Finite ↥(commutator ↥(reeFixed ReeTag.F4 (fixSubfield σ) 0)) := Subtype.finite
    haveI : Finite ↥⁅fixSubgroup δ, fixSubgroup δ⁆ := Subtype.finite
    haveI : IsSimpleGroup (CFSGIndex.lie ⟨.tits, hv⟩).Group :=
      (CFSG.LieType.Simplicity.fam_tits_simplicity _ 2 1
        (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩)).2
    haveI hJs : IsSimpleGroup ↥⁅fixSubgroup δ, fixSubgroup δ⁆ :=
      (MulEquiv.isSimpleGroup_congr eJ).2 inferInstance
    obtain ⟨xT, yT, hxyT⟩ := exists_noncomm_of_isQuasisimple hT
    have hJnc : ∃ x y : ↥⁅fixSubgroup δ, fixSubgroup δ⁆, x * y ≠ y * x :=
      ⟨eJT.symm xT, eJT.symm yT, fun h => hxyT (by
        apply eJT.symm.injective
        rw [map_mul, map_mul]
        exact h)⟩
    refine lieCompExport_of_derived_eq_simple (J := ⁅fixSubgroup δ, fixSubgroup δ⁆) rfl hJs hJnc
      ⟨_, inferInstance, inferInstance, lieFactorData_of_simple hJnc
        (isChevSimple_of_lie ⟨.tits, hv⟩ (by simp [LieTypeIndex.characteristic_tits]) eJ),
        MonoidHom.id _, Function.surjective_id, by simp⟩ ?_
    exact isEmpty_quotient_center_alt6 (b3Lie_center_eq_bot hJnc)
      ⟨fun f => (isEmpty_cat_alt6 ⟨.tits, hv⟩ (Or.inr ⟨by simp [CFSG.Yardstones.Md42047359a2a.lieFamily],
        fun m => by simp⟩)).false (eJ.symm.trans f)⟩
  ·
    have hv : (LieTypeIndex.reeF4 b).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [LieTypeIndex.inStandardRange_iff] using Nat.one_le_iff_ne_zero.2 hb.ne'
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨eCat⟩ := CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeGamma_equiv_cat_of_card
      hb hv hkcard
    let E : ↥(fixSubgroup δ) ≃* (CFSGIndex.lie ⟨.reeF4 b, hv⟩).Group := eC.trans eCat.symm
    have hs : IsSimpleGroup ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) :=
      CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hb hkcard
    haveI : IsSimpleGroup ↥(fixSubgroup δ) := (MulEquiv.isSimpleGroup_congr eC).2 hs
    have hnc : ∃ x y : ↥(fixSubgroup δ), x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      have hperf : commutator (ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊤ :=
        ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hb hkcard
      have hc : commutator ↥(ReeTag.F4.reeGamma (fixSubfield σ) b) = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        have h := hcon (eC.symm y) (eC.symm x)
        apply eC.symm.injective
        rw [map_mul, map_mul]
        exact h
      rw [hperf] at hc
      exact top_ne_bot hc
    haveI : IsSimpleGroup (CFSGIndex.lie ⟨.reeF4 b, hv⟩).Group :=
      (MulEquiv.isSimpleGroup_congr E).1 inferInstance
    refine lieCompExport_of_quasisimple_fix (LieSemisimple.isQuasisimple_of_isSimpleGroup
      inferInstance hnc)
      ⟨_, inferInstance, inferInstance, lieFactorData_of_simple hnc
        (isChevSimple_of_lie ⟨.reeF4 b, hv⟩ (by simp [LieTypeIndex.characteristic_reeF4]) E),
        MonoidHom.id _, Function.surjective_id, by simp⟩ ?_
    exact isEmpty_quotient_center_alt6 (b3Lie_center_eq_bot hnc)
      ⟨fun f => (isEmpty_cat_alt6 ⟨.reeF4 b, hv⟩ (Or.inr ⟨by simp [CFSG.Yardstones.Md42047359a2a.lieFamily],
        fun m => by simp⟩)).false (E.symm.trans f)⟩

theorem lieCompExport_reeF4 (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) {S : Type} [Group S]
    [Finite S] (he : Nonempty (S ≃* (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group)) {β : MulAut S}
    (hβ : β ^ 3 = 1) (hβ1 : β ≠ 1) : LieCompExport 2 β := by
  classical
  obtain ⟨e0⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e0
  obtain ⟨-, a, ha, -, K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.exists_mulEquiv_reeGamma hR
  refine LieCompExport.of_congr e ?_
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hβ' : (MulAut.congr e β) ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1' : MulAut.congr e β ≠ 1 := fun h =>
    hβ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  by_cases hin : ∃ g : ReeTag.F4.reeGamma K a, MulAut.congr e β = MulAut.conj g
  · obtain ⟨g, hg⟩ := hin
    have hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ :=
      ReeTag.large_Ree_fixed_group_center_trivial a K hK
    obtain ⟨y, hy, hyp, hy1⟩ :=
      CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range hZ ⟨g, hg.symm⟩ hβ' hβ1'
    rw [hy]
    exact lieCompExport_reeGamma_inner ha hK y (orderOf_eq_prime hyp hy1)
  · push Not at hin
    obtain ⟨g, σ, hσ, hg⟩ := CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.reeF4_stdDescent_odd
      ha hK Nat.prime_three (MulAut.congr e β) ⟨orderOf_eq_prime hβ' hβ1', hin⟩
    rw [hg]
    refine lieCompExport_of_conj (MulAut.conj g)⁻¹ _ ?_
    have h : (MulAut.conj g)⁻¹ * (MulAut.conj g * ReeTag.F4.reeGammaFieldAut K a σ *
        (MulAut.conj g)⁻¹) * ((MulAut.conj g)⁻¹)⁻¹ = ReeTag.F4.reeGammaFieldAut K a σ := by group
    rw [h]
    exact lieCompExport_reeGamma_fieldAut hK σ hσ

end Ree

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
