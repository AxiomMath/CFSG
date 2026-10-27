module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShape
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRowsA
public import CFSG.RankThree.OddKernel.SporadicKernelTh

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.SporAltTh

open CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

section Simple'

variable {Q : Type} [Group Q] [Finite Q]

theorem shapeRkAt_of_simple_small_index' {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    {t : Q} (ht3 : orderOf t = 3)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({t} : Set Q)) = ⊥)
    (E : Subgroup Q) (hEC : E ≤ Subgroup.centralizer ({t} : Set Q))
    (hs : IsSimpleGroup ↥E) (hnab : ∃ a b : ↥E, a * b ≠ b * a) (h3 : 3 ∣ Nat.card ↥E)
    (hnd : ∀ n ≤ 14, ¬ Nat.card ↥E ∣ n.factorial)
    (hC : Nat.card ↥(Subgroup.centralizer ({t} : Set Q)) < 15 * Nat.card ↥E)
    (hG : Good ↥E) : ShapeRkAt 3 Good (fun _ _ => True) t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.centralizer ({t} : Set Q) with hCdef
  have hEZ : Subgroup.center ↥E = ⊥ := center_eq_bot_of_simple_nonab hnab
  set E' : Subgroup ↥C := E.subgroupOf C with hE'def
  have eE : ↥E' ≃* ↥E := Subgroup.subgroupOfEquivOfLe hEC
  haveI : IsSimpleGroup ↥E' := eE.isSimpleGroup_congr.2 hs
  have hcardE' : Nat.card E' = Nat.card E := Nat.card_congr eE.toEquiv
  have hEpos : 0 < Nat.card E := Nat.card_pos
  have hidx : E'.index ≤ 14 := by
    have h1 : E'.index * Nat.card E' = Nat.card C := Subgroup.index_mul_card E'
    rw [hcardE'] at h1
    by_contra h
    have : 15 ≤ E'.index := by omega
    nlinarith
  have hnormE' : E'.Normal := by
    refine normal_of_simple_not_dvd_factorial E' ?_
    rw [hcardE']
    exact hnd _ hidx
  have hLn : ∀ g ∈ C, ∀ l ∈ E, g * l * g⁻¹ ∈ E := by
    intro g hg l hl
    have := hnormE'.conj_mem ⟨l, hEC hl⟩ (Subgroup.mem_subgroupOf.2 hl) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hLq : CFSG.Open.IsQuasisimple ↥E := by
    refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hEZ).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥E) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  have hcore : GLAPPrimeCore 3 ↥E = ⊥ := by
    haveI := hs
    exact glaPPrimeCore_eq_bot_of_simple Nat.prime_three h3
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (E : Set Q)) := by
    set Z : Subgroup Q := C ⊓ Subgroup.centralizer (E : Set Q) with hZdef
    have hZC : Z ≤ C := inf_le_left
    set Z0 : Subgroup ↥C := Z.subgroupOf C with hZ0def
    have eZ : ↥Z0 ≃* ↥Z := Subgroup.subgroupOfEquivOfLe hZC
    haveI hZ0n : Z0.Normal := by
      constructor
      intro x hx g
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨C.mul_mem (C.mul_mem g.2 x.2) (C.inv_mem g.2), Subgroup.mem_centralizer_iff.2 ?_⟩
      intro e he
      have he' : (g : Q)⁻¹ * e * g ∈ E := by
        simpa using hLn _ (C.inv_mem g.2) e he
      have h1 := Subgroup.mem_centralizer_iff.1 hx.2 _ he'
      calc e * (g * x * g⁻¹ : ↥C) = g * ((g : Q)⁻¹ * e * g * x) * (g : Q)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
        _ = g * (x * ((g : Q)⁻¹ * e * g)) * (g : Q)⁻¹ := by rw [h1]
        _ = (g * x * g⁻¹ : ↥C) * e := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have htZ : t ∈ Z := ⟨htC, Subgroup.mem_centralizer_iff.2 fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.1 (hEC hh)⟩
    have hs0Z : (⟨t, htC⟩ : ↥C) ∈ Z0 := Subgroup.mem_subgroupOf.2 htZ
    have hs0c : ∀ c : ↥C, c * (⟨t, htC⟩ : ↥C) = (⟨t, htC⟩ : ↥C) * c := fun c =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
    have hs03 : orderOf (⟨t, htC⟩ : ↥C) = 3 := by rw [Subgroup.orderOf_mk]; exact ht3
    have hinj : Function.Injective ((QuotientGroup.mk' E').comp Z0.subtype) := by
      rw [injective_iff_map_eq_one]
      intro z hz
      have hzE : (z : ↥C) ∈ E' := (QuotientGroup.eq_one_iff _).1 hz
      have hzE2 : ((z : ↥C) : Q) ∈ E := Subgroup.mem_subgroupOf.1 hzE
      have hzZ : ((z : ↥C) : Q) ∈ Subgroup.centralizer (E : Set Q) :=
        (Subgroup.mem_subgroupOf.1 z.2).2
      have hmem : (⟨((z : ↥C) : Q), hzE2⟩ : ↥E) ∈ Subgroup.center ↥E := by
        rw [Subgroup.mem_center_iff]
        intro b
        exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hzZ b b.2))
      rw [hEZ, Subgroup.mem_bot] at hmem
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hmem
      simpa using this
    have hZ0card : Nat.card Z0 < 18 := by
      have h1 := Subgroup.card_dvd_of_injective _ hinj
      have h2 : Nat.card (↥C ⧸ E') = E'.index := rfl
      rw [h2] at h1
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
      omega
    have hO' := normal_coprime_eq_bot_of_gla hO
    have hp := isPGroup_three_of_small_central hs0Z hs03 hs0c hZ0card hO'
    exact hp.of_equiv eZ
  exact shapeRkAt_of_normal_quasisimple Nat.prime_three hEC hLn hLq h3 (by
    simpa [inf_comm] using hcent)
    (hGood _ _ (pSimpleEquivSelf E hcore hEZ).symm hG) trivial

end Simple'

end CFSG.HardMathSupport.Dickson.I271.SporAltTh

namespace CFSG.HardMathSupport.Dickson.I271.SporAltTh

open CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.SectionRank.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th.ThThreeNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
  CFSG.RankThree.PartTwo.Sec4.Item434SporTh CFSG.HardMathSupport.Dickson.Sec6
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open CFSG.GH74.QTGen4.Recog.G23 (g23Words SatisfiesG23Words)

section Shape'


theorem leaf_closure_of_six {X : Type} [Group X] (ε : Fin 6 → X) (hε : SatisfiesG23Words ε)
    (hne : ε 0 ≠ 1) :
    LeafType 3 ↥(Subgroup.closure (Set.range ε)) ∧ IsSimpleGroup ↥(Subgroup.closure (Set.range ε)) ∧
      (∃ a b : ↥(Subgroup.closure (Set.range ε)), a * b ≠ b * a) ∧
      Nat.card ↥(Subgroup.closure (Set.range ε)) = 4245696 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_adjointG2_of_six ε hε ⟨0, hne⟩
  exact leafType_three_of_equiv_adjointG2 e

theorem th_shape_S' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    ShapeRkAt 3 CFSG.LocalAnalysis.GLTheoremA.SporAltRows.STypeThree (fun _ _ => True) thS := by
  haveI : Finite ↥J := finite_J
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr => (lift_mk_eq_evalW _ r).trans (hrel r hr)
  obtain ⟨hleaf, hsimp, hnab, hcard⟩ := leaf_closure_of_six thEps hε hne
  have hEC : Subgroup.closure (Set.range thEps) ≤ Subgroup.centralizer ({thS} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  have hs3 : orderOf thS = 3 := th_orderOf.1
  have hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({thS} : Set ↥J)) = ⊥ :=
    oPrimeCoreTrivialAt_Th_three_of_residual thThreeResidual_holds thS hs3
  have hC : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 :=
    th3_facts.2.2.2.2.2
  refine shapeRkAt_of_simple_small_index' CFSG.LocalAnalysis.GLTheoremA.SporAltRows.stypeThree_of_equiv
    hs3 hO _ hEC hsimp hnab ?_ ?_ ?_
    (CFSG.LocalAnalysis.GLTheoremA.SporAltRows.stypeOK_of_card hb (N := 4245696) (by rw [hcard] <;> norm_num) (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))
  · rw [hcard]; norm_num
  · rw [hcard]
    intro n hn
    interval_cases n <;> decide
  · rw [hcard]; omega

end Shape'

end CFSG.HardMathSupport.Dickson.I271.SporAltTh

namespace CFSG.HardMathSupport.Dickson.I271.SporAltTh

open CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Sporadic.Th CFSG.Blueprint
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent
open CFSG.LocalAnalysis.GLTheoremA.SporAltRows (STypeThree stypeThree_of_equiv)

section Assembly'


theorem th_shape_Z' : ShapeRkAt 3 STypeThree (fun _ _ => True) thZ := by
  unfold ShapeRkAt
  left
  have hz : orderOf thZ = 3 := th_orderOf.2.1
  have hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({thZ} : Set ↥CFSG.Sporadic.Th.J)) = ⊥ :=
    oPrimeCoreTrivialAt_Th_three_of_residual thThreeResidual_holds thZ hz
  haveI : Finite ↥CFSG.Sporadic.Th.J := finite_J
  exact pConstrainedShape_of_solvable Nat.prime_three
    (isSolvable_of_card_dvd_two_three card_centralizer_zJ_dvd) hO

theorem th_shape_U' : ShapeRkAt 3 STypeThree (fun _ _ => True) thU := by
  unfold ShapeRkAt
  left
  refine pConstrainedShape_of_map_injective J.subtype J.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨R, hle, hnorm, hcard, hcent⟩ := th_caseU_spec
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) hcard) hcent

theorem th_centShapeRk' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CentShapeRk 3 STypeThree (fun _ _ => True) ↥J := by
  haveI : Finite ↥J := finite_J
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨hS3, hZ3, hU3⟩ := th_orders
  intro k hk1 hkp
  have hk3 : orderOf k = 3 := orderOf_eq_prime hkp hk1
  obtain ⟨h, c, hc, e, he, hcon⟩ := th_census k hk3
  have hrep : c ^ 3 = 1 ∧ ShapeRkAt 3 STypeThree (fun _ _ => True) c := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨hS3, th_shape_S' hb⟩
    · exact ⟨hZ3, th_shape_Z'⟩
    · exact ⟨hU3, th_shape_U'⟩
  obtain ⟨hc3, hshape⟩ := hrep
  have hshape' : ShapeRkAt 3 STypeThree (fun _ _ => True) (c ^ e) :=
    ShapeRkAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc3 he).symm hshape
  have hconj := ShapeRkAt.of_equiv Nat.prime_three stypeThree_of_equiv hRk (MulAut.conj h) hshape'
  have hk : (MulAut.conj h) (c ^ e) = k := by
    rw [MulAut.conj_apply]
    exact hcon
  rw [hk] at hconj
  exact hconj

theorem srow_Th_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.SporAltRows.SRow .Th 3 := by
  have hfin : Finite ↥CFSG.Sporadic.Th.J := finite_J
  have e : CFSG.Blueprint.NativeSporadic.Th ≃* ↥CFSG.Sporadic.Th.J := CFSG.Sporadic.Th.thEquivJ
  have hs : IsSimpleGroup ↥CFSG.Sporadic.Th.J :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_J CFSG.Sporadic.Th.th_kernel_facts
  have hnc : ∃ a c : ↥CFSG.Sporadic.Th.J, a * c ≠ c * a := by
    haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      Finite.of_equiv _ CFSG.Sporadic.Th.thEquivJ.symm.toEquiv
    haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .Th) :=
      CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
        CFSG.Sporadic.Th.th_kernel_facts
    have hcC : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Th) = 90745943887872000 :=
      CFSG.RankThree.OddKernel.card_Th_eq
    obtain ⟨a, c, hac⟩ := CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (S := CFSG.Blueprint.NativeSporadic.Carrier .Th) (by rw [hcC]; norm_num)
    refine ⟨e a, e c, fun h => hac ?_⟩
    exact e.injective ((e.map_mul a c).trans (h.trans (e.map_mul c a).symm))
  have b : ↥CFSG.Sporadic.Th.J ≃* (TauCeti.CFSGIndex.sporadic .Th).Group :=
    e.symm.trans (hbr .Th).some
  exact @CFSG.LocalAnalysis.GLTheoremA.SporAltRows.srow_of_centShape .Th 3 ↥CFSG.Sporadic.Th.J _
    hfin hs hOut b hnc Nat.prime_three (by norm_num) STypeThree
    (CentShape.of_centShapeRk (th_centShapeRk' hb)) fun _ _ h => h

end Assembly'

end CFSG.HardMathSupport.Dickson.I271.SporAltTh
