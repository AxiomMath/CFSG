module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsNotReeOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsNotReeUntw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsNotReeTriD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcInputsNotReeTwE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxAll
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup lieOrderBridge_holds)
open CFSG.ComponentClassification.OuterAutomorphisms (inner innAutDerived inner_le_innAutDerived)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (compRel compRelC sameShape fieldSize suzRee)

set_option linter.unusedSectionVars false

private theorem not_suzRee_of_core {d : TauCeti.LieTypeIndex} (hd : S2019ExcCoreIdx d) :
    ¬ suzRee d := by
  cases d <;> simp_all [S2019ExcCoreIdx, suzRee]

private theorem ne_reeG2_of_core {d : TauCeti.LieTypeIndex} (hd : S2019ExcCoreIdx d) :
    ∀ k, d ≠ .reeG2 k := by
  rintro k rfl
  exact hd

private theorem ne_reeG2_of_compRel {d e : TauCeti.LieTypeIndex} (hd : S2019ExcCoreIdx d)
    (h : compRel d e) : ∀ k, e ≠ .reeG2 k := by
  rintro k rfl
  rcases h with ⟨-, -, hs⟩ | ⟨-, ⟨q, hq, -⟩ | ⟨q, hq, -⟩⟩ | ⟨-, q, hq, -⟩
  · exact not_suzRee_of_core hd (hs trivial)
  · cases hq
  · cases hq
  · cases hq

private theorem ne_reeG2_of_sameShape {d e : TauCeti.LieTypeIndex} (hd : S2019ExcCoreIdx d)
    (h : sameShape d e) : ∀ k, e ≠ .reeG2 k := by
  rintro k rfl
  cases d <;> first | exact h.elim | exact hd

private theorem compRel_self (d : TauCeti.LieTypeIndex) : compRel d d :=
  Or.inl ⟨rfl, ⟨1, le_rfl, (pow_one _).symm⟩, id⟩

private noncomputable def quotientCenterEquivOfBot {J : Type} [Group J]
    (hZ : Subgroup.center J = ⊥) : J ⧸ Subgroup.center J ≃* J :=
  (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

section Identify


theorem glaPComponent_fixSubgroup_one {p : ℕ} (hp : p.Prime) {K : Type} [Group K] [Finite K]
    {d : TauCeti.ValidLieTypeIndex} (eK : K ≃* (TauCeti.CFSGIndex.lie d).Group) {J : Subgroup K}
    (hJ : GLAPComponent p (fixSubgroup (1 : MulAut K)) J) :
    IsComponentOf J (fixSubgroup (1 : MulAut K)) ∧ Subgroup.center ↥J = ⊥ ∧
      Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  classical
  haveI := (CFSG.Assembly.lie_finite_simple d).2
  haveI : IsSimpleGroup K := eK.isSimpleGroup
  have hKna := exists_mul_ne_mul_of_glaPComponent hp hJ
  have h1 : fixSubgroup (1 : MulAut K) = ⊤ := by
    ext x
    simp [mem_fixSubgroup]
  let eF : ↥(fixSubgroup (1 : MulAut K)) ≃* K := (MulEquiv.subgroupCongr h1).trans Subgroup.topEquiv
  have hs : IsSimpleGroup ↥(fixSubgroup (1 : MulAut K)) := eF.isSimpleGroup
  have hnc : ∃ a b : ↥(fixSubgroup (1 : MulAut K)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKna
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  have hlayer :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_of_isSimpleGroup 1 hs hnc
  have hJc : IsComponentOf J (fixSubgroup (1 : MulAut K)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ
      (hlayer J hJ.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ))).1
  haveI : ((fixSubgroup (1 : MulAut K)).subgroupOf (fixSubgroup (1 : MulAut K))).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  haveI : Subsingleton (↥(fixSubgroup (1 : MulAut K)) ⧸
      (fixSubgroup (1 : MulAut K)).subgroupOf (fixSubgroup (1 : MulAut K))) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (a⁻¹ * b).2)
  have hF : FixCompsEquiv (1 : MulAut K) (TauCeti.CFSGIndex.lie d).Group :=
    fixCompsEquiv_of_normal_simple le_rfl hs hnc inferInstance (eF.trans eK)
  have hT : Subgroup.center (TauCeti.CFSGIndex.lie d).Group = ⊥ := by
    have hZK : Subgroup.center K = ⊥ :=
      CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hKna
    rw [← Subgroup.map_center_eq eK, hZK, Subgroup.map_bot]
  exact ⟨hJc, hF.center_eq_bot hT hJc, hF J hJc⟩

theorem s2019ExcComp_identify {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq2 : q ≠ 2) (hqp : q ≠ p)
    {K : Type} [Group K] [Finite K] {d : TauCeti.ValidLieTypeIndex}
    (hdq : d.1.characteristic = q) (hd : S2019ExcCoreIdx d.1)
    (eK : K ≃* (TauCeti.CFSGIndex.lie d).Group) {β : MulAut K} (hβ : β ^ p = 1) {J : Subgroup K}
    (hJ : GLAPComponent p (fixSubgroup β) J) :
    IsComponentOf J (fixSubgroup β) ∧
      ((∃ a : K, MulAut.conj a = β) → ∃ i : TauCeti.CFSGIndex, compRelC d.1 i ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group)) ∧
      ((∀ a : K, MulAut.conj a ≠ β) → Subgroup.center ↥J = ⊥ ∧
        ∃ e : TauCeti.ValidLieTypeIndex, sameShape d.1 e.1 ∧ fieldSize e.1 ^ p = fieldSize d.1 ∧
          Nonempty (↥J ≃* (TauCeti.CFSGIndex.lie e).Group)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  by_cases hβ1 : β = 1
  · subst hβ1
    obtain ⟨hJc, hZ, ⟨φ⟩⟩ := glaPComponent_fixSubgroup_one hp eK hJ
    refine ⟨hJc, fun _ => ⟨.lie d, compRel_self d.1, ⟨(quotientCenterEquivOfBot hZ).trans φ⟩⟩,
      fun hout => (hout 1 (map_one _)).elim⟩
  haveI := (CFSG.Assembly.lie_finite_simple d).2
  haveI : IsSimpleGroup K := eK.isSimpleGroup
  have hKna := exists_mul_ne_mul_of_glaPComponent hp hJ
  have hpq : p ≠ d.1.characteristic := by rw [hdq]; exact Ne.symm hqp
  have hlayer := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent K
    inferInstance hKna d ⟨eK⟩ p hp hp2 hpq β hβ hβ1
  have hJc : IsComponentOf J (fixSubgroup β) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ
      (hlayer J hJ.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ))).1
  refine ⟨hJc, ?_, ?_⟩
  ·
    rintro ⟨a, rfl⟩
    have hI : KD264Lie.CompIdxAt p d.1 K :=
      KD264Lie.compIdxAt_of_mulEquiv eK.symm (KD264Lie.lieCompIdx_all d p hp hp2 hpq trivial)
    obtain ⟨i, hφ, hrel⟩ := hI (MulAut.conj a) (inner_le_innAutDerived K ⟨a, rfl⟩) hβ hβ1 J hJc
    exact ⟨i, hrel, hφ⟩
  ·
    intro hout
    obtain ⟨d1, hv⟩ := d
    have hq2' : ∀ Q : TauCeti.PrimePower, Q.p = q → Q.p ≠ 2 := fun Q hQ => hQ ▸ hq2
    cases d1 with
    | G2 Q =>
      obtain ⟨hZ, Q', hv', hpow, hφ⟩ :=
        s2019OuterComp_G2 hp hp5 Q hv (hq2' Q (by simpa using hdq)) eK β hβ hout J hJc
      exact ⟨hZ, ⟨.G2 Q', hv'⟩, trivial, hpow, hφ⟩
    | F4 Q =>
      obtain ⟨hZ, Q', hv', hpow, hφ⟩ :=
        s2019OuterComp_F4 hp hp5 Q hv (hq2' Q (by simpa using hdq)) eK β hβ hout J hJc
      exact ⟨hZ, ⟨.F4 Q', hv'⟩, trivial, hpow, hφ⟩
    | E6 Q =>
      obtain ⟨hZ, Q', hv', hpow, hφ⟩ :=
        s2019OuterComp_E6 hp hp5 Q hv (hq2' Q (by simpa using hdq)) eK β hβ hout J hJc
      exact ⟨hZ, ⟨.E6 Q', hv'⟩, trivial, hpow, hφ⟩
    | E7 Q =>
      obtain ⟨hZ, Q', hv', hpow, hφ⟩ :=
        s2019OuterComp_E7 hp hp5 Q hv (hq2' Q (by simpa using hdq)) eK β hβ hout J hJc
      exact ⟨hZ, ⟨.E7 Q', hv'⟩, trivial, hpow, hφ⟩
    | E8 Q =>
      obtain ⟨hZ, Q', hv', hpow, hφ⟩ :=
        s2019OuterComp_E8 hp hp5 Q hv (hq2' Q (by simpa using hdq)) eK β hβ hout J hJc
      exact ⟨hZ, ⟨.E8 Q', hv'⟩, trivial, hpow, hφ⟩
    | trialityD4 Q =>
      obtain ⟨hZ, Q', hv', hpow, hφ⟩ := s2019OuterComp_trialityD4 hp hp5 Q hv eK β hβ hout J hJc
      exact ⟨hZ, ⟨.trialityD4 Q', hv'⟩, trivial, hpow, hφ⟩
    | twistedE6 Q =>
      obtain ⟨hZ, Q', hv', hpow, hφ⟩ := s2019OuterComp_twistedE6 hp hp5 Q hv eK β hβ hout J hJc
      exact ⟨hZ, ⟨.twistedE6 Q', hv'⟩, trivial, hpow, hφ⟩
    | _ => exact hd.elim

end Identify

section NotRee


theorem s2019ExcCompNotRee_holds : S2019ExcCompNotRee := by
  intro p q hp hp2 hq hq2 hqp K _ _ hK β hβ J hJ hRee
  classical
  obtain ⟨i, hi, ⟨eK⟩⟩ := hK
  cases i with
  | lie d =>
    obtain ⟨hdq, hd⟩ : d.1.characteristic = q ∧ S2019ExcCoreIdx d.1 := hi
    obtain ⟨m, hm, hcard⟩ := card_of_catalogIs_ree lieOrderBridge_holds hRee
    have hnotLie : ∀ e : TauCeti.ValidLieTypeIndex, (∀ k, e.1 ≠ .reeG2 k) →
        IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* (TauCeti.CFSGIndex.lie e).Group) := fun e he =>
      isEmpty_mulEquiv_lie_of_card_ree lieOrderBridge_holds hm hcard e he
    by_cases hβ1 : β = 1
    · subst hβ1
      obtain ⟨-, hZ, ⟨φ⟩⟩ := glaPComponent_fixSubgroup_one hp eK hJ
      exact (hnotLie d (ne_reeG2_of_core hd)).false ((quotientCenterEquivOfBot hZ).trans φ)
    by_cases hq3 : q = 3
    · subst hq3
      have hp5 : 5 ≤ p := by
        have := hp.two_le
        rcases Nat.lt_or_ge p 5 with h | h
        · interval_cases p <;> first | omega | exact absurd hp (by decide)
        · exact h
      obtain ⟨-, hinn, hout⟩ := s2019ExcComp_identify hp hp5 hq2 hqp hdq hd eK hβ hJ
      by_cases hin : ∃ a : K, MulAut.conj a = β
      · obtain ⟨i, hrel, ⟨φ⟩⟩ := hinn hin
        cases i with
        | lie e => exact (hnotLie e (ne_reeG2_of_compRel hd hrel)).false φ
        | alternating n hn => exact (isEmpty_mulEquiv_alternating_of_card_ree hm hcard n hn).false φ
        | _ => exact hrel.elim
      · push Not at hin
        obtain ⟨hZ, e, hsh, -, ⟨φ⟩⟩ := hout hin
        exact (hnotLie e (ne_reeG2_of_sameShape hd hsh)).false
          ((quotientCenterEquivOfBot hZ).trans φ)
    · haveI := (CFSG.Assembly.lie_finite_simple d).2
      have hKs : IsSimpleGroup K := eK.isSimpleGroup
      obtain ⟨-, hchev⟩ := isComponentOf_and_isChevSimple hp hp2 hqp hKs
        (exists_mul_ne_mul_of_glaPComponent hp hJ) hdq eK hβ hβ1 hJ
      exact not_isChevSimple_of_card_ree lieOrderBridge_holds hm hcard hq hq3 hchev
  | _ => exact hi.elim

end NotRee

end CFSG.LocalAnalysis.GLTheoremA.S2019
