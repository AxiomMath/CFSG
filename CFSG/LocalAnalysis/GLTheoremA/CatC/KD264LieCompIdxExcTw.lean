module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompRel
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTSolvable
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4SLayer
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutReeF4
import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCrit
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer
import CFSG.LieType.ChevTwo.OppositeFixedExcReeModel
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived inner Outer)

open CFSG.HardMathSupport.Dickson.SuzukiReeB (exists_eq_conj_of_mem_range fixSubgroup_conj)


theorem compIdxAt_excTw_of_isSolvable {p : ℕ} {d : TauCeti.LieTypeIndex} {S : Type} [Group S]
    (h : ∀ β : MulAut S, β ∈ innAutDerived S → β ^ p = 1 → β ≠ 1 →
      Group.IsSolvable ↥(fixSubgroup β)) : CompIdxAt p d S := by
  intro β hβ hβp hβ1 K hK
  exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.not_isComponentOf_of_isSolvable
    (h β hβ hβp hβ1) hK).elim

theorem innAutDerived_le_inner_excTw_of_isCyclic {S : Type} [Group S] (h : IsCyclic (Outer S)) :
    innAutDerived S ≤ inner S :=
  sup_le le_rfl (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outreef4_commutator_le_inner h)

theorem innAutDerived_le_inner_excTw_of_mulEquiv {S M : Type} [Group S] [Group M] (e : S ≃* M)
    (h : innAutDerived S ≤ inner S) : innAutDerived M ≤ inner M := by
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.map_innAutDerived_congr e,
    ← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
  exact Subgroup.map_mono h

theorem compIdxAt_suzukiGroup_excTw {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (d : TauCeti.LieTypeIndex) : CompIdxAt p d ↥(suzukiGroup a K) := by
  refine compIdxAt_excTw_of_isSolvable fun β hβ hβp hβ1 => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥(suzukiGroup a K) := (suzuki_simple ha hK).1
  have hinn : β ∈ inner ↥(suzukiGroup a K) := innAutDerived_le_inner_excTw_of_isCyclic
    (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).1 hβ
  obtain ⟨x, rfl, hxp, hx1⟩ :=
    exists_eq_conj_of_mem_range (CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK) hinn hβp hβ1
  have hodd : Odd (orderOf x) := by
    rw [orderOf_eq_prime hxp hx1]
    exact hp.odd_of_ne_two hp2
  obtain ⟨hcard, -⟩ :=
    (CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers ha hK).2 x hx1 hodd
  rw [fixSubgroup_conj]
  exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard

theorem compIdxAt_cat_suzuki (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CompIdxAt p (.suzuki m) (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group := by
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK', hf]
  exact compIdxAt_of_mulEquiv θ.symm (compIdxAt_suzukiGroup_excTw ha hK hp hp2 _)

theorem compIdxAt_reeGamma_G2_excTw
    {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (d : TauCeti.LieTypeIndex) :
    CompIdxAt p d ↥(ReeTag.G2.reeGamma K a) := by
  refine compIdxAt_excTw_of_isSolvable fun β hβ hβp hβ1 => ?_
  haveI : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  haveI : Fact p.Prime := ⟨hp⟩
  have hinn : β ∈ inner ↥(ReeTag.G2.reeGamma K a) := innAutDerived_le_inner_excTw_of_isCyclic
    (CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.isCyclic_outer_reeG2 ha hK) hβ
  obtain ⟨-, hsimple, hnc⟩ :=
    CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple ha K hK
  haveI := hsimple
  obtain ⟨x, rfl, hxp, hx1⟩ := exists_eq_conj_of_mem_range
    (CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc) hinn hβp hβ1
  rw [fixSubgroup_conj]
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_centralizer_reeGamma_G2 ha K hK
    hp hp2 hp3 (orderOf_eq_prime hxp hx1)

theorem compIdxAt_cat_reeG2
    (m : ℕ)
    (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : CompIdxAt p (.reeG2 m) (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group := by
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, ⟨MulEquiv.refl _⟩⟩)
  exact compIdxAt_of_mulEquiv e.symm (compIdxAt_reeGamma_G2_excTw ha hK hp hp2 hp3 _)

theorem compIdxAt_titsD_excTw
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (d : TauCeti.LieTypeIndex) :
    CompIdxAt p d CFSG.Sporadic.Schreier.Tits.titsD := by
  refine compIdxAt_excTw_of_isSolvable fun β _ hβp hβ1 => ?_
  obtain ⟨x, rfl, hxp, hx1⟩ := exists_eq_conj_of_mem_range CFSG.Sporadic.Schreier.Tits.titsD_center
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.titsD_mem_inner_of_pow_eq_one hp hp2 hβp)
    hβp hβ1
  rw [fixSubgroup_conj]
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_centralizer_titsD hp hp2 hxp hx1

theorem compIdxAt_cat_tits
    (hv : TauCeti.LieTypeIndex.tits.Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CompIdxAt p .tits (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨MulEquiv.refl _⟩⟩)
  exact compIdxAt_of_mulEquiv e.symm (compIdxAt_titsD_excTw hp hp2 _)

theorem compRelC_reeF4_of_idxOver {a : ℕ} {i : TauCeti.CFSGIndex}
    (h : IdxOver 2 (2 ^ (2 * a + 1)) i) : compRelC (.reeF4 a) i :=
  compRelC_of_idxOver (j := 1) le_rfl (by
    simpa only [TauCeti.LieTypeIndex.characteristic_reeF4, fieldSize, pow_one] using h)

theorem compRelC_reeF4_suzuki {a : ℕ} (ha : 1 ≤ a) :
    compRelC (.reeF4 a)
      (.lie ⟨.suzuki a, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suzuki_valid ha⟩) :=
  Or.inl ⟨by simp, ⟨1, le_rfl, by simp [fieldSize]⟩, fun _ => trivial⟩

theorem compIdx_reeGamma_F4_three_excTw
    {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = 3) {J : Subgroup ↥(ReeTag.F4.reeGamma K a)}
    (hJ : IsComponentOf J (fixSubgroup (MulAut.conj y))) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧
      compRelC (.reeF4 a) i := by
  classical
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite ↥(ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨e⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hy
  have hFcard : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  haveI : Fintype (GaloisField 2 (2 * (2 * a + 1))) := Fintype.ofFinite _
  have hFfcard : Fintype.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hFcard
  have hq := (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
    (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hFcard (by omega)).1
  let E : ↥(fixSubgroup (MulAut.conj y)) ≃*
      ↥(StatedSU 3 (2 ^ (2 * a + 1)) (GaloisField 2 (2 * (2 * a + 1)))) :=
    (MulEquiv.subgroupCongr (fixSubgroup_conj y)).trans e
  have hmq : ((3 : ℕ), 2 ^ (2 * a + 1)) ≠ ((3 : ℕ), 2) := by
    intro h
    have h2 : 2 ^ (2 * a + 1) = 2 := (Prod.mk.inj h).2
    have : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hCq : CFSG.IsQuasisimple ↥(fixSubgroup (MulAut.conj y)) :=
    CFSG.IsQuasisimple.of_mulEquiv E hq
  have hJC : J = fixSubgroup (MulAut.conj y) :=
    CFSG.HardMathSupport.Solomon.Coordinator.component_eq_of_normal_quasisimple hJ le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance) hCq fun H hH _ => hH
  subst hJC
  obtain ⟨i, ⟨φ⟩, hi⟩ := (catalogueOver_su (GaloisField 2 (2 * (2 * a + 1))) 3 (2 ^ (2 * a + 1))
    hFfcard le_rfl hmq).of_mulEquiv E.symm
  refine ⟨i, ⟨φ⟩, compRelC_reeF4_of_idxOver ?_⟩
  have hch : ringChar (GaloisField 2 (2 * (2 * a + 1))) = 2 :=
    ringChar.eq (GaloisField 2 (2 * (2 * a + 1))) 2
  rwa [hch] at hi

theorem compIdx_reeGamma_F4_gt3_excTw
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = p)
    {J : Subgroup ↥(ReeTag.F4.reeGamma K a)} (hJ : IsComponentOf J (fixSubgroup (MulAut.conj y))) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧
      compRelC (.reeF4 a) i := by
  classical
  rw [fixSubgroup_conj] at hJ
  obtain ⟨N, hall, hty⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.LevelLieRF4SLayer.largeRee_typed ha hK hp hp3 y hy
  have hJN : J = N :=
    hall J (CFSG.LocalAnalysis.GLTheoremA.LevelLieRF4SLayer.isComponentOf_rankThree_of_open hJ)
  subst hJN
  rcases hty with hbot | hf | hf
  · exfalso
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
    have hnt : Nontrivial ↥J := (QuotientGroup.mk_surjective (s := Subgroup.center ↥J)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot J).1 hnt hbot
  · obtain ⟨f⟩ := hf
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : Fintype.card K = 2 ^ (2 * a + 1) := by
      rw [← Nat.card_eq_fintype_card]
      exact hK
    have h4 : 4 ≤ Fintype.card K := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨i, ⟨φ⟩, hi⟩ := (catalogueOver_sl K 2 le_rfl fun _ => h4).of_mulEquiv f
    refine ⟨i, ⟨φ⟩, compRelC_reeF4_of_idxOver ?_⟩
    have hch : ringChar K = 2 := ringChar.eq K 2
    rwa [hch, hcard] at hi
  · obtain ⟨f⟩ := hf
    obtain ⟨c⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_suzukiGroup_equiv_cat ha hK
    have hZ : Subgroup.center ↥(suzukiGroup a K) = ⊥ :=
      CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
    let g : (↥J ⧸ Subgroup.center ↥J) ≃*
        (↥(suzukiGroup a K) ⧸ Subgroup.center ↥(suzukiGroup a K)) :=
      QuotientGroup.congr _ _ f.symm (Subgroup.map_center_eq f.symm)
    let z : (↥(suzukiGroup a K) ⧸ Subgroup.center ↥(suzukiGroup a K)) ≃* ↥(suzukiGroup a K) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact ⟨_, ⟨g.trans (z.trans c)⟩, compRelC_reeF4_suzuki ha⟩

theorem compIdxAt_reeGamma_F4_excTw
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (hinn : innAutDerived ↥(ReeTag.F4.reeGamma K a) ≤ inner ↥(ReeTag.F4.reeGamma K a)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : CompIdxAt p (.reeF4 a) ↥(ReeTag.F4.reeGamma K a) := by
  intro β hβ hβp hβ1 J hJ
  haveI : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  haveI : Finite ↥(ReeTag.F4.reeGamma K a) := Subtype.finite
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, rfl, hyp, hy1⟩ := exists_eq_conj_of_mem_range
    (ReeTag.large_Ree_fixed_group_center_trivial a K hK) (hinn hβ) hβp hβ1
  have hy : orderOf y = p := orderOf_eq_prime hyp hy1
  have hp3 : p = 3 ∨ 3 < p := by
    have := hp.two_le
    omega
  rcases hp3 with rfl | hp3
  · exact compIdx_reeGamma_F4_three_excTw ha hK y hy hJ
  · exact compIdx_reeGamma_F4_gt3_excTw ha hK hp hp3 y hy hJ

theorem compIdxAt_cat_reeF4
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CompIdxAt p (.reeF4 m) (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group := by
  have hm : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm hR
  exact compIdxAt_of_mulEquiv e.symm (compIdxAt_reeGamma_F4_excTw hm hK
    (innAutDerived_le_inner_excTw_of_mulEquiv e
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.t6outreef4_innAutDerived_le_inner hR)) hp hp2)

@[expose] def TwistedE6CompIdx : Prop :=
  LieCompIdx fun e => ∃ q : TauCeti.PrimePower, e = .twistedE6 q

theorem lieCompIdx_suzukiReeTits :
    LieCompIdx fun e => isExcTwistedIdx e ∧ ∀ q : TauCeti.PrimePower, e ≠ .twistedE6 q := by
  rintro ⟨e, hv⟩ p hp hp2 hpc ⟨hP, hne⟩
  cases e with
  | twistedE6 q => exact absurd rfl (hne q)
  | suzuki m => exact compIdxAt_cat_suzuki m hv hp hp2
  | reeG2 m => exact compIdxAt_cat_reeG2 m hv hp hp2 (by simpa using hpc)
  | reeF4 m => exact compIdxAt_cat_reeF4 m hv hp hp2
  | tits => exact compIdxAt_cat_tits hv hp hp2
  | _ => exact absurd hP (by simp [isExcTwistedIdx])

theorem lieCompIdx_excTwisted_of_twistedE6
    (h : TwistedE6CompIdx) : LieCompIdx isExcTwistedIdx := by
  rintro ⟨e, hv⟩ p hp hp2 hpc hP
  by_cases hE6 : ∃ q : TauCeti.PrimePower, e = .twistedE6 q
  · exact h ⟨e, hv⟩ p hp hp2 hpc hE6
  · exact lieCompIdx_suzukiReeTits ⟨e, hv⟩ p hp hp2 hpc
      ⟨hP, fun q hq => hE6 ⟨q, hq⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
