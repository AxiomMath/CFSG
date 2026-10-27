module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables2
public import CFSG.HardMathSupport.Dickson.BMRows.M13L33Invol
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSpor5
import CFSG.HardMathSupport.Dickson.BMRows.M13Rows
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24Five

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables3

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Yardstones.Md0ec50421ce4 (PSimple PQuot)

section Simple

theorem exists_noncomm_of_simple_card {G : Type} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact h (IsSimpleGroup.prime_card (α := G))

theorem card_pSimple_of_isAltType_seven {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp7 : p ∣ 2520) {Λ : Subgroup S} (h : IsAltType 7 ↥Λ) : Nat.card (PSimple p Λ) = 2520 := by
  have hcard := Inputs2324.card_of_isAltType_seven h
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥Λ := e.isSimpleGroup
  have hcore : GLAPPrimeCore p ↥Λ = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.glaPPrimeCore_eq_bot_of_simple hp (by rw [hcard]; exact hp7)
  have hZ : Subgroup.center ↥Λ = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab
      (exists_noncomm_of_simple_card (by rw [hcard]; norm_num))
  rw [Nat.card_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivSelf Λ hcore hZ).toEquiv, hcard]

end Simple

section S_fi23FiveNoA6_holds

theorem fi23FiveNoA6_holds : SporTables2.Fi23FiveNoA6 := by
  intro x hx I hI
  haveI : Finite CFSG.Sporadic.Fi23.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi23.card_J]; norm_num)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) :=
    Finite.of_equiv CFSG.Sporadic.Fi23.J CFSG.Sporadic.Fi23.fi23EquivJ.symm.toEquiv
  obtain ⟨Λ, -, huniq, h7, -⟩ := InputsSpor5.fi23FiveLayer_holds
    (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi23)
    x hx
  rw [huniq I hI, card_pSimple_of_isAltType_seven Nat.prime_five (by norm_num) h7]
  norm_num

end S_fi23FiveNoA6_holds

section L33

theorem isLpType_three_three_of_goodL33 {T : Type} [Group T]
    (h : CFSG.HardMathSupport.Dickson.BMRows.M13L33.GoodL33 T) : IsLpType 3 3 T := by
  obtain ⟨e⟩ := h
  exact ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3,
    ⟨(e.trans CFSG.HardMathSupport.Dickson.BMRows.M13L33.slEquivPsl).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 3))⟩⟩

end L33

section S_mThirteenADown_holds

open CFSG.AGLEmbedding.Norton.MON5_7 (gw) in
open CFSG.Monster.Generated (Gmat) in
theorem mThirteenADown_holds : SporTables2.MThirteenADown := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  have φ : Gmat ≃* CFSG.Monster.Existence.MGriess :=
    (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
  refine SporTables2.mThirteenADown_of_L33 fun I hI => ?_
  rcases CFSG.HardMathSupport.Dickson.BMRows.shapeRkAt_xE φ with hc | ⟨J, -, hu, hg, -⟩
  · exact (CFSG.HardMathSupport.Dickson.I271.no_glaPComponent_of_pConstrainedShape (by norm_num) hc
      hI).elim
  · rw [hu I hI]
    exact isLpType_three_three_of_goodL33 hg

end S_mThirteenADown_holds

section Sylow

theorem exists_conj_mem_of_card_sylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M S : Subgroup G} (hSM : S ≤ M) (hS : Nat.card S = p ^ (Nat.card M).factorization p)
    {x : G} (hxM : x ∈ M) {k : ℕ} (hx : orderOf x = p ^ k) : ∃ m ∈ M, m⁻¹ * x * m ∈ S := by
  let S' : Sylow p M := Sylow.ofCard (S.subgroupOf M)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv, hS])
  let x' : M := ⟨x, hxM⟩
  have hP : IsPGroup p (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hx])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M S' Q
  have hxQ : x' ∈ (Q : Subgroup M) := hQ (Subgroup.mem_zpowers x')
  rw [← hm, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  refine ⟨m, m.2, ?_⟩
  have h2 : (MulAut.conj m)⁻¹ • x' = m⁻¹ * x' * m := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [h2, Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hxQ
  exact hxQ

theorem pow_eq_one_of_mem_closure_pair {G : Type*} [Group G] {n : ℕ} {x f : G} (hxf : Commute x f)
    (hx : x ^ n = 1) (hf : f ^ n = 1) {g : G} (hg : g ∈ Subgroup.closure ({x, f} : Set G)) :
    g ^ n = 1 := by
  have h1 : ∀ a ∈ Subgroup.closure ({x, f} : Set G), Commute a x ∧ Commute a f := by
    intro a ha
    have hle : Subgroup.closure ({x, f} : Set G) ≤
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({f} : Set G) := by
      rw [Subgroup.closure_le]
      rintro c (rfl | rfl)
      · exact ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
          Subgroup.mem_centralizer_singleton_iff.2 hxf.eq⟩
      · exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hxf.symm.eq,
          Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    obtain ⟨hax, haf⟩ := hle ha
    exact ⟨(Subgroup.mem_centralizer_singleton_iff.1 hax), (Subgroup.mem_centralizer_singleton_iff.1 haf)⟩
  have h2 : ∀ a ∈ Subgroup.closure ({x, f} : Set G), ∀ b ∈ Subgroup.closure ({x, f} : Set G),
      Commute a b := by
    intro a ha b hb
    have hle : Subgroup.closure ({x, f} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.closure_le]
      rintro c (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (h1 a ha).1.symm.eq
      · exact Subgroup.mem_centralizer_singleton_iff.2 (h1 a ha).2.symm.eq
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hb)).symm
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | rfl
    · exact hx
    · exact hf
  | one => exact one_pow n
  | mul a b ha hb iha ihb => rw [(h2 a ha b hb).mul_pow, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

end Sylow

section S_bSevenNoL28_holds

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven (xSeven) in
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal (uOne uTwo) in
theorem bSevenNoL28_holds
    : SporTables2.BSevenNoL28 := by
  intro I hI h504
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hs, -⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab (by norm_num : Nat.Prime 7) hI
  haveI := hs
  obtain ⟨e⟩ := CFSG.ComponentClassification.LiteratureLocal.nonempty_mulEquiv_psl2_eight_of_simple h504
  let π : ↥I →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' _).comp (QuotientGroup.mk' _))
  have hπ : Function.Surjective π :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  obtain ⟨c, hc⟩ := CFSG.CGT.Timmesfeld75.exists_orderOf_nine_of_surjective_psl2_eight π hπ
  have hcC : (c : CFSG.Blueprint.NativeSporadic.B) ∈
      Subgroup.centralizer ({xSeven} : Set CFSG.Blueprint.NativeSporadic.B) := hI.1 c.2
  have hco : orderOf (c : CFSG.Blueprint.NativeSporadic.B) = 3 ^ 2 := by
    rw [Subgroup.orderOf_coe, hc]
    norm_num
  obtain ⟨hQ, hQle, -⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.uQ_facts
  have P := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.bSevenElem_parts
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  have h3 := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.card_centralizer_seven_three
    xSeven hxS
  obtain ⟨m, -, hm⟩ := exists_conj_mem_of_card_sylow hQle (by rw [hQ, h3]) hcC hco
  have L := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal.localParts_of_certificate
  have hcube := @pow_eq_one_of_mem_closure_pair CFSG.Blueprint.NativeSporadic.B Units.instGroup 3 uOne uTwo
    L.u1_u2 L.u1_pow L.u2_pow _ hm
  have hdvd := orderOf_dvd_of_pow_eq_one hcube
  rw [InputsSpor5.orderOf_inv_mul_mul, hco] at hdvd
  norm_num at hdvd

end S_bSevenNoL28_holds

section S_fi24FiveA9_holds

theorem fi24FiveA9_holds : SporTables.Fi24FiveA9 := by
  haveI : Finite CFSG.Sporadic.Fi24.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
    Finite.of_equiv CFSG.Sporadic.Fi24.J CFSG.HardMathSupport.Dickson.I271.fi24EquivCarrier.symm.toEquiv
  have hJ : SporTables.CentTypes 5 (fun T _ => Nat.card T = 181440) CFSG.Sporadic.Fi24.J :=
    (SporTables.centTypes_of_centShapeRk Nat.prime_five
      CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows.centShapeRk_five).mono
      fun _ _ h => CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows.card_of_goodA9 h
  have h2 : SporTables.CentTypes 5 (fun T _ => Nat.card T = 181440)
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) :=
    @SporTables.CentTypes.of_equiv 5 Nat.prime_five (fun T _ => Nat.card T = 181440)
      (SporTables.typeInv_card fun N => N = 181440) CFSG.Sporadic.Fi24.J
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) (inferInstance : Group CFSG.Sporadic.Fi24.J)
      (inferInstance : Group (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime)) inferInstance
      CFSG.HardMathSupport.Dickson.I271.fi24EquivCarrier hJ
  exact h2

end S_fi24FiveA9_holds

section Structure3

structure SporDownResidual3 : Prop where
  B_three : CFSG.HardMathSupport.Dickson.I271.TabBThreeBNoComp
  M_three : CFSG.HardMathSupport.Dickson.I271.M3ResBNoComp
  B_five : CFSG.HardMathSupport.Dickson.I271.TabBFiveBNoComp
  M_five : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)
  M_eleven : SporTables2.MElevenDown

end Structure3

section S_sporDownResidualPP_of_residual3

theorem sporDownResidual''_of_residual3
    (h : SporDownResidual3) : SporTables2.SporDownResidual'' where
  B_three := h.B_three
  M_three := h.M_three
  Fi23_five := fi23FiveNoA6_holds
  Fi24Prime_five := fi24FiveA9_holds
  B_five := h.B_five
  M_five := h.M_five
  B_seven := bSevenNoL28_holds
  M_eleven := h.M_eleven
  M_thirteen_A := mThirteenADown_holds

end S_sporDownResidualPP_of_residual3

section S_sporDownResidualP_of_residual3

theorem sporDownResidual'_of_residual3
    (h : SporDownResidual3) : Claims1116d.SporDownResidual' :=
  SporTables2.sporDownResidual'_of_residual'' (sporDownResidual''_of_residual3 h)

end S_sporDownResidualP_of_residual3

section S_inputSporDownChev_of_residual3

theorem inputSporDownChev_of_residual3
    (h : SporDownResidual3) : Claims1116b.InputSporDownChev :=
  SporTables2.inputSporDownChev_of_residual'' (sporDownResidual''_of_residual3 h)

end S_inputSporDownChev_of_residual3

section S_sporDownResidualK_of_mElevenDown

theorem sporDownResidualK_of_mElevenDown
    (h : SporTables2.MElevenDown) : SporTables2.SporDownResidualK where
  Fi23_five := fi23FiveNoA6_holds
  Fi24Prime_five := fi24FiveA9_holds
  B_seven := bSevenNoL28_holds
  M_eleven := h
  M_thirteen_A := mThirteenADown_holds

end S_sporDownResidualK_of_mElevenDown

section S_sporDownResidualP_of_mElevenDown_kGroup

theorem sporDownResidual'_of_mElevenDown_kGroup
    (hB : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group)
    (hM : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) (h : SporTables2.MElevenDown) :
    Claims1116d.SporDownResidual' :=
  SporTables2.sporDownResidual'_of_residualK hB hM (sporDownResidualK_of_mElevenDown h)

end S_sporDownResidualP_of_mElevenDown_kGroup

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables3

end
