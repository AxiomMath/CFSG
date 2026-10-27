module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs295
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Co3Shape
public import CFSG.Sporadic.Recognition.McLASCert
public import CFSG.RankThree.Asc83Table.J3
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzC
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyB
public import CFSG.Sporadic.Recognition.LyonsAS44Cert
public import CFSG.Sporadic.Recognition.LyonsAS4NormQuot
public import CFSG.Sporadic.Recognition.LyonsAS4Quot
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.Sporadic.HNSchreier.Faithful
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Witness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Lift
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Three
public import CFSG.Sporadic.Co2Cert.Faithful
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThreeClose
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Census
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo1
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeMoore
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeQuasi
public import CFSG.Sporadic.Co1Block.Perm
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24ThreeE
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66RealFix
public import CFSG.Sporadic.Fi24.ExtFi23
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBLevel1
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBElem
public import CFSG.RankThree.OddKernel.SporadicKernelTh
public import CFSG.Sporadic.Fi23.Simple
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFAut
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11I102
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434O8pOuter
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27
public import CFSG.HardMathSupport.Dickson.Bal207.D42Triality
public import CFSG.HardMathSupport.Dickson.Bal207.D42TriModel
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSimple
public import CFSG.HardMathSupport.Dickson.I271.SporGenBM
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Tree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24Red
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabLyA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeB
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeC
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BM2Census
public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMDownMGmat
public import CFSG.HardMathSupport.Foote.E27.OrbitF3
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCo3
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKleinFrontier
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.AgreeTasks
public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineSp
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.YGroups.Y443.Native.Image
public import Certificates.Certificate13622Base
public import Certificates.Data.CFSGNative.Timmesfeld.PcFus

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295

open CFSG.Open
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)

section Co3

open CFSG.HardMathSupport.Dickson.I271 CFSG.Sporadic.Schreier.Co3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T

theorem no295_co3P :
    No295 ↥co3P := by
  intro _ k hk
  have hk' : orderOf (k : Equiv.Perm (Fin 276)) = 3 := by rw [← hk]; exact Subgroup.orderOf_coe k
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := exists_conj_classes k.2 hk'
  have hcm : c ∈ co3P := by
    rcases hc with rfl | rfl | rfl
    · exact caseA_spec.2.2.1
    · exact caseB_spec.2.2.1
    · exact yPerm_mem
  have hc3 : c ^ 3 = 1 := by
    rcases hc with rfl | rfl | rfl
    · exact caseA_spec.1
    · exact caseB_spec.1
    · exact yPerm_pow
  have hexc : Excl295At (⟨c, hcm⟩ : ↥co3P) := by
    rcases hc with rfl | rfl | rfl
    · obtain ⟨-, -, -, hcard, hle, -⟩ := caseA_spec
      exact excl295At_of_ambient hcm hle (by rw [hcard]; norm_num)
    · obtain ⟨-, -, -, hcard, hle, -⟩ := caseB_spec
      exact excl295At_of_ambient hcm hle (by rw [hcard]; norm_num)
    · obtain ⟨⟨hC, -⟩, hLC, -, hLcard, -⟩ := caseC_spec
      obtain ⟨eL⟩ := nonempty_mulEquiv_L
      exact excl295At_of_ambient_simple hcm (hC ▸ hLC) (isSimpleGroup_of_equiv_P9 eL)
        (nonabelian_of_equiv_P9 eL) (by rw [hLcard]; norm_num)
  refine Excl295At.of_conj_pow (x := (⟨c, hcm⟩ : ↥co3P)) (Subtype.ext (by simpa using hc3)) he
    ?_ hexc
  refine isConj_iff.2 ⟨⟨h, hh⟩⁻¹, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, inv_inv]
  rw [← hcon]
  group

theorem no295_Co3
    [Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co3)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Co3) :=
  No295.of_equiv (co3PermEquiv : CFSG.Blueprint.NativeSporadic.Co3 ≃* co3P) no295_co3P

end Co3

theorem no295_nativeMcL
    [Finite CFSG.Blueprint.NativeSporadic.McL] : No295 CFSG.Blueprint.NativeSporadic.McL := by
  intro _ y hy
  obtain ⟨x₁, x₂, -, -, c₁, c₂, -, hall⟩ :=
    CFSG.Sporadic.Recognition.McLAS.mcl_two_classes_order_three_of_certificate
  rcases hall y hy with h | h
  · exact Excl295At.of_isConj h (excl295At_of_card_dvd (by rw [c₁]; norm_num))
  · exact Excl295At.of_isConj h (excl295At_of_card_dvd (by rw [c₂]; norm_num))

theorem no295_McL
    [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .McL)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
  haveI : Finite CFSG.Blueprint.NativeSporadic.McL := hf
  No295.of_equiv (T := CFSG.Blueprint.NativeSporadic.McL) (MulEquiv.refl _) no295_nativeMcL

theorem no295_J3
    [Finite (CFSG.Blueprint.NativeSporadic.Carrier .J3)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .J3) := by
  apply no295_of_pRank_le
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
    (CFSG.RankThree.Asc83Table.J3.table (L := CFSG.Blueprint.NativeSporadic.Carrier .J3)
      ⟨MulEquiv.refl _⟩).1]

section Suz

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT CFSG.Sporadic.SuzOddCore
  CFSG.HardMathSupport.Dickson.I271.TabSuzC

theorem no295_suzM :
    No295 ↥suzM := by
  intro _ k hk
  have hk' : orderOf (k : Equiv.Perm (Fin 1782)) = 3 := by
    rw [← hk]; exact Subgroup.orderOf_coe k
  obtain ⟨h, hh, hcase⟩ := exists_conj_D_or_y k.2 hk'
  have hconj : ∀ {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzM), h * k * h⁻¹ = c →
      IsConj k ⟨c, hc⟩ := fun hc hkc => isConj_iff.2 ⟨⟨h, hh⟩, Subtype.ext (by simpa using hkc)⟩
  have hy : Excl295At (⟨yPerm, yPerm_mem⟩ : ↥suzM) := by
    obtain ⟨eA⟩ := nonempty_mulEquiv_Esub_alt6
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have hcard : Nat.card Esub = 360 := Esub_derived.2
    exact excl295At_of_ambient_simple yPerm_mem Esub_le_C eA.isSimpleGroup
      (exists_noncomm_of_isSimpleGroup eA.isSimpleGroup (by rw [hcard]; norm_num))
      (by rw [hcard]; norm_num)
  rcases hcase with hD | hy1 | hy2
  · have hm : h * k * h⁻¹ ∈ suzM := suzM.mul_mem (suzM.mul_mem hh k.2) (suzM.inv_mem hh)
    refine Excl295At.of_isConj (hconj hm rfl)
      (excl295At_of_ambient hm (le_inf (fun d hd => ?_) Dg_le) (by rw [card_Dg]; norm_num))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Dg_comm _ hd _ hD
  · exact Excl295At.of_isConj (hconj yPerm_mem hy1) hy
  · refine Excl295At.of_isConj (hconj (suzM.pow_mem yPerm_mem 2) hy2) ?_
    refine Excl295At.of_centralizer_eq ?_ hy
    exact (centralizer_pow_two_eq (x := (⟨yPerm, yPerm_mem⟩ : ↥suzM))
      (Subtype.ext (by simpa using yPerm_pow))).symm

theorem no295_Suz
    [Finite (CFSG.Blueprint.NativeSporadic.Carrier .Suz)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Suz) :=
  No295.of_equiv (suzEquivM : CFSG.Blueprint.NativeSporadic.Suz ≃* suzM) no295_suzM

end Suz

section Ly

open CFSG.Sporadic.Recognition.LyonsSims CFSG.HardMathSupport.Dickson.I271

theorem no295_Ly
    [Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ly)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Ly) := by
  intro _ g hg
  have hS : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Ly ≃*
      CFSG.Blueprint.NativeSporadic.Carrier .Ly) := ⟨MulEquiv.refl _⟩
  obtain ⟨t, ρ, D⟩ := exists_lyData_of_oneClassDoubleCover
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult.oneClassDoubleCover_of_ly hS)
  obtain ⟨x₁, x₂, x₃, St⟩ := D.exists_lyStd
  rcases (lemma45_classes_of_certificate D St).1 g hg with h | h
  · exact Excl295At.of_isConj h
      (excl295At_of_card_dvd (by rw [D.card_centralizer_x1 St.pow₁ St.rho₁]; norm_num))
  · exact Excl295At.of_isConj h
      (excl295At_of_le (tabLy_QE_le D St) (by rw [D.card_QE St]; norm_num))

end Ly

section HN

open CFSG.Sporadic.HNSchreier

theorem no295_JH :
    No295 ↥JH := by
  intro _ x hx
  rcases (order_three_classes x).1 hx with h | h
  · exact Excl295At.of_isConj h.symm (excl295At_of_card_dvd (by rw [card_CJ_s1]; norm_num))
  · exact Excl295At.of_isConj h.symm (excl295At_of_card_dvd (by rw [card_CJ_s3]; norm_num))

theorem no295_HN
    [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .HN)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .HN) := by
  haveI hf' : Finite CFSG.Blueprint.NativeSporadic.HN := hf
  exact @No295.of_equiv CFSG.Blueprint.NativeSporadic.HN
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.HN) hf' ↥JH (inferInstance : Group ↥JH)
    (inferInstance : Finite ↥JH) hnEquivJ no295_JH

end HN

section Fischer

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three

theorem allExcl295_Fi22J :
    AllExcl295 ↥CFSG.Sporadic.Fi22.J := by
  intro s hs
  obtain ⟨k, hk, hc⟩ := fi22_classify s hs
  exact Excl295At.of_isConj hc (excl295At_of_card_dvd
    ((by norm_num : 3 ^ 5 ∣ 2187).trans (three_pow_seven_dvd_card_centralizer_xRep hk)))

theorem no295_Fi22
    [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi22)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Fi22) := by
  haveI hf' : Finite CFSG.Blueprint.NativeSporadic.Fi22 := hf
  exact @No295.of_equiv CFSG.Blueprint.NativeSporadic.Fi22
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.Fi22) hf' ↥CFSG.Sporadic.Fi22.J
    (inferInstance : Group ↥CFSG.Sporadic.Fi22.J) (inferInstance : Finite ↥CFSG.Sporadic.Fi22.J)
    CFSG.Sporadic.Fi22.fi22EquivJ (No295.of_all allExcl295_Fi22J)

theorem allExcl295_Fi23J :
    AllExcl295 ↥CFSG.Sporadic.Fi23.J := by
  intro x hx
  obtain ⟨e, he, hex⟩ := Fi23Sylow.fi23ThreeTranspositionFixed x hx
  obtain ⟨t, ht, hcard, -⟩ :=
    CFSG.HardMathSupport.Dickson.I271.TabFi23.exists_lift_conj he hx hex.symm
  obtain ⟨k, hk, hc⟩ := fi22_classify t ht
  have h22 : 3 ^ 5 ∣ Nat.card (Subgroup.centralizer ({t} : Set ↥CFSG.Sporadic.Fi22.J)) := by
    rw [card_centralizer_eq_of_isConj hc]
    exact (by norm_num : 3 ^ 5 ∣ 2187).trans (three_pow_seven_dvd_card_centralizer_xRep hk)
  refine excl295At_of_le (J := Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.Fi23.J) ⊓
    Subgroup.centralizer ({e} : Set ↥CFSG.Sporadic.Fi23.J)) inf_le_left ?_
  rw [hcard]
  exact h22.mul_left 2

theorem no295_Fi23
    [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi23)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) := by
  haveI hf' : Finite CFSG.Blueprint.NativeSporadic.Fi23 := hf
  exact @No295.of_equiv CFSG.Blueprint.NativeSporadic.Fi23
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.Fi23) hf' ↥CFSG.Sporadic.Fi23.J
    (inferInstance : Group ↥CFSG.Sporadic.Fi23.J) (inferInstance : Finite ↥CFSG.Sporadic.Fi23.J)
    CFSG.Sporadic.Fi23.fi23EquivJ (No295.of_all allExcl295_Fi23J)

end Fischer

section Co2

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.Sporadic.Co2Cert

theorem allExcl295_co2P :
    AllExcl295 ↥co2P := by
  intro k hk
  have hk' : orderOf (k : Equiv.Perm (Fin 2300)) = 3 := by
    rw [← hk]; exact Subgroup.orderOf_coe k
  obtain ⟨h, hh, hD⟩ := exists_conj_mem_Dg k.2 hk'
  have hm : h * k * h⁻¹ ∈ co2P := Dg_le hD
  refine Excl295At.of_isConj (y := ⟨h * k * h⁻¹, hm⟩)
    (isConj_iff.2 ⟨⟨h, hh⟩, Subtype.ext (by simp)⟩) ?_
  exact excl295At_of_mem_elem (A := Tg) (Subgroup.mem_subgroupOf.2 hD) Tg_elemAbelian
    (by rw [card_Tg]; norm_num)

theorem no295_Co2
    [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co2)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Co2) := by
  haveI hf' : Finite CFSG.Blueprint.NativeSporadic.Co2 := hf
  exact @No295.of_equiv CFSG.Blueprint.NativeSporadic.Co2
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.Co2) hf' ↥co2P
    (inferInstance : Group ↥co2P) (inferInstance : Finite ↥co2P)
    co2PermEquiv (No295.of_all allExcl295_co2P)

end Co2

section Th

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem allExcl295_ThJ :
    @AllExcl295 ↥CFSG.Sporadic.Th.J _ CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J := by
  intro s hs
  obtain ⟨⟨P, hP, hPp, hPc⟩, -⟩ := thThreeResidual_holds s hs
  exact Or.inl ⟨P, hP, hPp, le_trans (by norm_num) hPc⟩

theorem no295_Th
    [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Th)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Th) := by
  haveI hf' : Finite CFSG.Blueprint.NativeSporadic.Th := hf
  exact @No295.of_equiv CFSG.Blueprint.NativeSporadic.Th
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.Th) hf' ↥CFSG.Sporadic.Th.J
    (inferInstance : Group ↥CFSG.Sporadic.Th.J)
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
    CFSG.Sporadic.Th.thEquivJ (No295.of_all allExcl295_ThJ)

end Th

section Baby

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

theorem allExcl295_B :
    @AllExcl295 CFSG.Blueprint.NativeSporadic.B _ CFSG.Monster.B.Pinned.finite_B := by
  intro s hs
  obtain ⟨i, hi⟩ := bThree_classes s hs
  have hord : orderOf (t3 i) = 3 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hi
    rw [← orderOf_injective phiB phiB_injective, ← hc, ← MulAut.conj_apply,
      MulEquiv.orderOf_eq, hs]
  exact Excl295At.of_isConj hi
    (Excl295At.of_injective phiB phiB_injective (allExcl295_Fi23J _ hord))

theorem no295_B
    [Finite (CFSG.Blueprint.NativeSporadic.Carrier .B)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .B) :=
  @No295.of_all CFSG.Blueprint.NativeSporadic.B _ CFSG.Monster.B.Pinned.finite_B allExcl295_B

end Baby

section Co1

open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator

theorem card_co1E :
    Nat.card Co1T.eSplit.T = 3 ^ 6 := by
  rw [Co1T.SplitData.T, MonoidHom.range_eq_map,
    Subgroup.card_map_of_injective (Co1T.SplitData.φ_injective _), Subgroup.card_top,
    Co3T.card_vec, Co1T.aGA_length]

theorem co1_eE_mem
    {k : ℕ} (hk : k < 729) : Co1Spor.eE k ∈ Co1T.eSplit.T := by
  have hlen : k < (_root_.Timmesfeld.Co1Leaf.expVecs 3 6).length := by
    rw [Co1Spor.expVecs_length]; norm_num; exact hk
  have he : Co1Spor.eExp k ∈ _root_.Timmesfeld.Co1Leaf.expVecs 3 6 := by
    unfold Co1Spor.eExp
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem hlen
  obtain ⟨hl, hlt⟩ := Co1T.mem_expVecs_iff.1 he
  rw [Co1Spor.eE, ← Co1T.vecProd_eq_eltG Co1T.aGA (by rw [hl, Co1T.aGA_length]) hlt]
  exact ⟨Multiplicative.ofAdd (Co1T.listVec Co1T.aGA.length (Co1Spor.eExp k)), rfl⟩

theorem allExcl295_GA :
    @AllExcl295 ↥GA _ CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.finite_GA := by
  haveI : Finite ↥GA := Co1T.finite_GA
  intro s hs
  obtain ⟨k, r, hr, hkr⟩ := Co1Spor.exists_rep hs
  refine Excl295At.of_isConj (y := r) (isConj_iff.2 ⟨k⁻¹, by rw [← hkr]; group⟩) ?_
  have hE : ∀ {j : ℕ}, j < 729 → Excl295At (Co1Spor.eE j) := fun hj =>
    excl295At_of_mem_comm (co1_eE_mem hj) Co1T.eSplit.T_comm (by rw [card_co1E]; norm_num)
  rcases hr with rfl | rfl | rfl | rfl
  · exact hE (by norm_num)
  · exact hE (by norm_num)
  · exact hE (by norm_num)
  · have hx : MRep (CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeDRoot.rootRows3D ())
        ((Co1T.root 2 : ↥GA) : GL24) := Co1T.wordL_rep _
    obtain ⟨-, -, hxy, hM, hy1⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.moore_data hx
    obtain ⟨-, ⟨e⟩⟩ := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 9)
      (by norm_num) CFSG.HardMathSupport.Dickson.I271.TabCo1.mooreM hM).2.2.2.2.2 (by norm_num)
      ⟨1, ⟨le_rfl, by norm_num⟩, hy1⟩
    have hLC :
        Subgroup.closure (CFSG.HardMathSupport.Dickson.I271.TabCo1.mooreM '' Set.Icc 1 (9 - 2)) ≤
        Subgroup.centralizer ({((Co1T.root 2 : ↥GA) : GL24)} : Set GL24) ⊓ GA := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨j, ⟨hj1, hj7⟩, rfl⟩
      exact ⟨Subgroup.mem_centralizer_singleton_iff.2 (hxy j hj1 (by omega)).symm,
        CFSG.HardMathSupport.Dickson.I271.TabCo1.mooreM_mem j⟩
    obtain ⟨hsL, hnab, hcardL⟩ := CFSG.HardMathSupport.Dickson.I271.alt9_subgroup_data e
    exact excl295At_of_ambient_simple (Co1T.root 2).2 hLC hsL hnab (by rw [hcardL]; norm_num)

theorem no295_Co1
    [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Co1)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Co1) := by
  haveI hf' : Finite CFSG.Blueprint.NativeSporadic.Co1 := hf
  exact @No295.of_equiv CFSG.Blueprint.NativeSporadic.Co1
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.Co1) hf' ↥GA
    (inferInstance : Group ↥GA) Co1T.finite_GA
    CFSG.Sporadic.Co1Block.co1MatEquiv (No295.of_all allExcl295_GA)

end Co1

section Fi24

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

theorem fi24_excl_of_fix
    {x : ↥CFSG.Sporadic.Fi24.J} (hx : orderOf x = 3) {u : Fin 306936} (hu : x • u = u) :
    @Excl295At ↥CFSG.Sporadic.Fi24.J _ Fi24Three.finite_J x := by
  haveI : Finite ↥CFSG.Sporadic.Fi24.J := Fi24Three.finite_J
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥CFSG.Sporadic.Fi24.J CFSG.Sporadic.Fi24.root u
  have hyM : g⁻¹ * x * g ∈ CFSG.Sporadic.Fi24.M := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hg, hu, ← hg, inv_smul_smul]
  have hconj : MulAut.conj g⁻¹ x = g⁻¹ * x * g := by
    rw [MulAut.conj_apply, inv_inv]
  have hy3 : orderOf (g⁻¹ * x * g) = 3 := by
    rw [← hconj, MulEquiv.orderOf_eq, hx]
  have h0 : orderOf (CFSG.Sporadic.Fi24.fi23EquivM ⟨g⁻¹ * x * g, hyM⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy3]
  have h1 := @Excl295At.of_equiv ↥CFSG.Sporadic.Fi24.M
    (inferInstance : Group ↥CFSG.Sporadic.Fi24.M) (inferInstance : Finite ↥CFSG.Sporadic.Fi24.M)
    ↥CFSG.Sporadic.Fi23.J (inferInstance : Group ↥CFSG.Sporadic.Fi23.J)
    (inferInstance : Finite ↥CFSG.Sporadic.Fi23.J) CFSG.Sporadic.Fi24.fi23EquivM
    ⟨g⁻¹ * x * g, hyM⟩ (allExcl295_Fi23J _ h0)
  exact Excl295At.of_isConj (y := g⁻¹ * x * g) (isConj_iff.2 ⟨g⁻¹, by rw [inv_inv]⟩)
    (Excl295At.of_subgroup hyM h1)

theorem fi24_excl_xJ :
    @Excl295At ↥CFSG.Sporadic.Fi24.J _ Fi24Three.finite_J
      CFSG.HardMathSupport.Dickson.I271.TabFi24.xJ := by
  haveI : Finite ↥CFSG.Sporadic.Fi24.J := Fi24Three.finite_J
  have hF := CFSG.HardMathSupport.Dickson.I271.TabFi24.frame_facts
  obtain ⟨-, -, -, hcard⟩ := CFSG.HardMathSupport.Dickson.I271.TabFi24.leaf_closure_of_six_some
    CFSG.HardMathSupport.Dickson.I271.TabFi24.epsJ hF.eps_rel hF.eps_ne
  have hLS : Subgroup.closure (Set.range CFSG.HardMathSupport.Dickson.I271.TabFi24.epsJ) ≤
      CFSG.HardMathSupport.Dickson.I271.TabFi24.stab4 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨h0, h1, hA, hB⟩ := hF.eps_fix i
    exact CFSG.HardMathSupport.Dickson.I271.TabFi24.mem_stab4.2
      ⟨CFSG.HardMathSupport.Dickson.I271.TabFi24.mem_lvl_two_of_fix h0 h1, hA, hB⟩
  exact excl295At_of_le (hLS.trans CFSG.HardMathSupport.Dickson.I271.TabFi24.stab4_le_centX)
    (by rw [hcard]; norm_num)

theorem allExcl295_Fi24J :
    @AllExcl295 ↥CFSG.Sporadic.Fi24.J _ Fi24Three.finite_J := by
  haveI : Finite ↥CFSG.Sporadic.Fi24.J := Fi24Three.finite_J
  intro x hx
  obtain ⟨i, hi⟩ := Fi24Sylow.fi24ThreeClasses_holds x hx
  have hord : orderOf (fi24Rep3 i) = 3 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hi
    rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  refine Excl295At.of_isConj hi ?_
  by_cases h4 : i = 4
  · subst h4
    exact Excl295At.of_isConj CFSG.HardMathSupport.Dickson.I271.TabFi24.isConj_rep4_xJ
      fi24_excl_xJ
  · have hpos : 0 < Nat.card (MulAction.fixedBy (Fin 306936) (fi24Rep3 i)) := by
      rw [Fi24Sylow.card_fixedBy_fi24Rep3]
      fin_cases i <;> simp_all [Fi24Sylow.repFix]
    obtain ⟨⟨u, hu⟩⟩ := (Nat.card_pos_iff.1 hpos).1
    exact fi24_excl_of_fix hord hu

theorem no295_Fi24
    [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .Fi24Prime) := by
  haveI hf' : Finite CFSG.Blueprint.NativeSporadic.Fi24prime := hf
  exact @No295.of_equiv CFSG.Blueprint.NativeSporadic.Fi24prime
    (inferInstance : Group CFSG.Blueprint.NativeSporadic.Fi24prime) hf' ↥CFSG.Sporadic.Fi24.J
    (inferInstance : Group ↥CFSG.Sporadic.Fi24.J) Fi24Three.finite_J
    CFSG.Sporadic.Fi24.fi24EquivJ (No295.of_all allExcl295_Fi24J)

end Fi24

section Monster

open CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.I271

theorem allExcl295_MGriess [Finite MGriess] : AllExcl295 MGriess := by
  have hE : MonsterExistenceStatement MGriess :=
    CFSG.Milestones.cl_lit_monster_existence_griess_conway
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  haveI : Finite CFSG.Monster.Generated.Gmat := Finite.of_equiv MGriess φ.toEquiv
  intro s hs
  by_cases hinv : InvertedByTwoA s
  · obtain ⟨α, -, -, -, i, hi, hsh⟩ :=
      invertedByTwoA_data_twoA hE Nat.prime_three (by norm_num) hs hinv
    have hi34 : i = 3 ∨ i = 4 := by
      clear hsh
      revert i
      decide
    rcases hi34 with rfl | rfl
    · obtain ⟨e⟩ := hsh
      refine excl295At_of_le (J := Subgroup.centralizer ({α} : Set MGriess) ⊓
        Subgroup.centralizer ({s} : Set MGriess)) inf_le_right ?_
      rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
      norm_num
    · obtain ⟨e⟩ := hsh
      refine excl295At_of_le (J := Subgroup.centralizer ({α} : Set MGriess) ⊓
        Subgroup.centralizer ({s} : Set MGriess)) inf_le_right ?_
      rw [Nat.card_congr e.toEquiv, CFSG.RankThree.OddKernel.card_Th_eq]
      norm_num
  · have hinv' : ¬ InvertedByTwoA (φ s) := fun h => hinv (by
      simpa using InvertedByTwoA.map φ.symm h)
    have hc := CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bClass_holds (φ s)
      (by rw [MulEquiv.orderOf_eq, hs]) hinv'
    refine Excl295At.of_equiv φ (Excl295At.of_isConj hc ?_)
    refine excl295At_of_le (J := ThreeBNF.QQ) (fun q hq => ?_) (by rw [ThreeBNF.card_QQ]; norm_num)
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 ThreeBNF.tbw_mem_centralizer) q hq)

theorem no295_M [hf : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M)] :
    No295 (CFSG.Blueprint.NativeSporadic.Carrier .M) := by
  obtain ⟨e⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  haveI hf' : Finite CFSG.Blueprint.NativeSporadic.MonsterModel.y443Derived.Carrier := hf
  haveI hg : Finite CFSG.Blueprint.NativeSporadic.MonsterModel.griess.Carrier :=
    Finite.of_equiv _ e.symm.toEquiv
  haveI : Finite MGriess := hg
  exact No295.of_equiv e.symm (No295.of_all allExcl295_MGriess)

end Monster

section Lie

open CFSG.HardMathSupport.Solomon.Coordinator (IsChevOfChar)
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs)

@[expose] def Input29_5'LieId : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S →
      Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) →
      catalogIs (↥L ⧸ Subgroup.center ↥L) CFSG.LocalAnalysis.GLTheoremA.S9.isD4two ∧
        ∀ Q : Subgroup X, IsSylowIn 3 (L ⊓ Subgroup.centralizer ({x} : Set X)) Q →
          (∀ q ∈ Q, q ^ 3 = 1) ∧ ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₂ ≠ q₂ * q₁

@[expose] def Input29_5'LieNotD42 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ¬ CFSG.LocalAnalysis.GLTheoremA.S9.isD4two (TauCeti.CFSGIndex.lie d) →
    ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S →
      Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) → False

@[expose] def Input29_5'LieD42 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    CFSG.LocalAnalysis.GLTheoremA.S9.isD4two (TauCeti.CFSGIndex.lie d) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S →
      Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) →
      ∀ Q : Subgroup X, IsSylowIn 3 (L ⊓ Subgroup.centralizer ({x} : Set X)) Q →
        (∀ q ∈ Q, q ^ 3 = 1) ∧ ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₂ ≠ q₂ * q₁

@[expose] def IsClassicalTwoIndex : TauCeti.CFSGIndex → Prop
  | .lie d => match d.1 with
    | .A _ q | .twistedA _ q | .B _ q | .D _ q | .twistedD _ q => q.card = 2
    | _ => False
  | _ => False

@[expose] def Input29_5'LieTwo : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d) →
    ¬ CFSG.LocalAnalysis.GLTheoremA.S9.isD4two (TauCeti.CFSGIndex.lie d) →
    ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S →
      Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) → False

@[expose] def Input29_5'LieOther : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ¬ IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d) →
    ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S →
      Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) → False

theorem input29_5'LieNotD42_of_split (hT : Input29_5'LieTwo) (hO : Input29_5'LieOther) :
    Input29_5'LieNotD42 := by
  intro X _ _ L hLn hq hK hC d he h42 hchev hrk x hx hC4 hrk3 hsolv
  by_cases h2 : IsClassicalTwoIndex (TauCeti.CFSGIndex.lie d)
  · exact hT X L hLn hq hK hC d he h2 h42 hchev hrk x hx hC4 hrk3 hsolv
  · exact hO X L hLn hq hK hC d he h2 hchev hrk x hx hC4 hrk3 hsolv

theorem input29_5'LieId_of_split (hN : Input29_5'LieNotD42) (hD : Input29_5'LieD42) :
    Input29_5'LieId := by
  intro X _ _ L hLn hq hK hC d he hchev hrk x hx hC4 hrk3 hsolv
  by_cases h42 : CFSG.LocalAnalysis.GLTheoremA.S9.isD4two (TauCeti.CFSGIndex.lie d)
  · exact ⟨⟨_, h42, he⟩, hD X L hLn hq hK hC d he h42 hrk x hx hC4 hrk3 hsolv⟩
  · exact (hN X L hLn hq hK hC d he h42 hchev hrk x hx hC4 hrk3 hsolv).elim

theorem center_eq_bot_of_cent {X : Type} [Group X] {L : Subgroup X}
    (hC : ∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) : Subgroup.center ↥L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine hC z fun l hl => ?_
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨l, hl⟩).symm

theorem catalogIs_of_center_eq_bot {L : Type} [Group L] (hZ : Subgroup.center L = ⊥)
    {P : TauCeti.CFSGIndex → Prop} (h : catalogIs (L ⧸ Subgroup.center L) P) : catalogIs L P := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans f⟩⟩

theorem not_mem_of_d42 (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hK : CFSG.Open.IsKGroup ↥L)
    (hD42 : catalogIs (↥L ⧸ Subgroup.center ↥L) CFSG.LocalAnalysis.GLTheoremA.S9.isD4two)
    {x : X} (hx : orderOf x = 3)
    (hrk3 : CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3) : x ∉ L := by
  intro hxL
  have hType : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.IsD4Type ↥L :=
    ⟨2, 1, by norm_num, CFSG.LocalAnalysis.GLTheoremA.D4XF.statedModel_of_d4two hD42⟩
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; norm_num at hx
  have hq' : CFSG.IsQuasisimple ↥L := ⟨⟨hq.1⟩, hq.2,
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L hq⟩
  have hK' : CFSG.IsKGroup ↥L := CFSG.KCore.KGroupNonab.kGroupAllSimple
    CFSG.Assembly.inCatalog_isoInvariant CFSG.Assembly.inCatalog_containsAbelianSimple hK
  have h4 := (hD4 ↥L hq' hK' hType).2 ⟨x, hxL⟩ (Subtype.ext (by simpa using hx3))
    (fun h => hx1 (congrArg Subtype.val h))
  have hle : (Subgroup.centralizer ({⟨x, hxL⟩} : Set ↥L)).map L.subtype ≤
      Subgroup.centralizer ({x} : Set X) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    exact congrArg Subtype.val hy
  have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) L.subtype
    L.subtype_injective (Subgroup.centralizer ({⟨x, hxL⟩} : Set ↥L))
  have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle
  omega

@[expose] def D42T2NoNine : Prop :=
  ∀ g ∈ CFSG.Sporadic.Schreier.centralizerIn CFSG.EvenSmallLie.OmegaEight.omegaT
    CFSG.HardMathSupport.Dickson.Bal207.D42Tri.t2Perm, g ^ 9 = 1 → g ^ 3 = 1

theorem pow_three_eq_one_of_noNine {G : Type*} [Group G] {C : Subgroup G}
    (h : ∀ g ∈ C, g ^ 9 = 1 → g ^ 3 = 1) {g : G} (hg : g ∈ C) :
    ∀ k : ℕ, g ^ 3 ^ k = 1 → g ^ 3 = 1 := by
  have key : ∀ k : ℕ, g ^ 3 ^ (k + 1) = 1 → g ^ 3 = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      apply ih
      have h1 : (g ^ 3 ^ k) ^ 9 = 1 := by
        rw [← pow_mul, show 3 ^ k * 9 = 3 ^ (k + 1 + 1) by ring]
        exact hk
      have h2 := h _ (C.pow_mem hg _) h1
      rwa [← pow_mul, ← pow_succ] at h2
  intro k hk
  cases k with
  | zero => rw [pow_zero, pow_one] at hk; rw [hk, one_pow]
  | succ k => exact key k hk

theorem input29_5'LieD42_of_t2
    (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4) (hT : D42T2NoNine) :
    Input29_5'LieD42 := by
  intro X _ _ L hLn hq hK hC d he h42 hrk x hx hC4 hrk3 hsolv Q hQ
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hLn
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_cent hC
  have hD42 : catalogIs (↥L ⧸ Subgroup.center ↥L) CFSG.LocalAnalysis.GLTheoremA.S9.isD4two :=
    ⟨_, h42, he⟩
  have hL42 := catalogIs_of_center_eq_bot hZ hD42
  have hxL : x ∉ L := not_mem_of_d42 hD4 hq hK hD42 hx hrk3
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  set τ : MulAut ↥L := MulAut.conjNormal x with hτ
  have h3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, hx3, map_one]
  have hout : ∀ l : ↥L, MulAut.conj l ≠ τ := by
    intro l hl
    apply hxL
    have hc : ∀ m ∈ L, ((l : X)⁻¹ * x) * m = m * ((l : X)⁻¹ * x) := by
      intro m hm
      have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨m, hm⟩ : ↥L) : X)) hl
      simp only [hτ, MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc (l : X)⁻¹ * x * m = (l : X)⁻¹ * (x * m * x⁻¹) * x := by group
        _ = (l : X)⁻¹ * ((l : X) * m * (l : X)⁻¹) * x := by rw [h1]
        _ = m * ((l : X)⁻¹ * x) := by group
    have h1 := hC _ hc
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact l.2
  have hS := CFSG.LocalAnalysis.GLTheoremA.D4XF.statedModel_of_d4two hL42
  obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT (X := ↥L)
    (Or.inl ⟨by decide, hS⟩)
  obtain ⟨a, haA, ha3, haO, hact⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.D42Tri.exists_autT_of_mulAut e h3 hout
  obtain ⟨y, hy, g, hg, hc⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.D42Tri.exists_conj_rho_or_t2 haA ha3 haO
  have hmap := CFSG.HardMathSupport.Dickson.Bal207.D42Tri.map_conjEmb_fixSubgroup e hact hy hg
  have hinj := CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb_injective e g
  have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup τ =
      (L ⊓ Subgroup.centralizer ({x} : Set X)).subgroupOf L := by
    ext s
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hs
      refine ⟨s.2, ?_⟩
      have h1 := congrArg Subtype.val hs
      simp only [hτ, MulAut.conjNormal_apply] at h1
      calc (s : X) * x = x * s * x⁻¹ * x := by rw [h1]
        _ = x * s := by group
    · rintro ⟨-, hs⟩
      apply Subtype.ext
      simp only [hτ, MulAut.conjNormal_apply]
      rw [← hs]
      group
  rcases hc with hc | hc
  ·
    exfalso
    rw [hc] at hmap
    have hrange : CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub ≤
        (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g).range := by
      refine CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub_le.trans ?_
      rw [← hmap]
      exact Subgroup.map_le_range _ _
    have hT1 : (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub.comap
        (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g)).map
        (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g) =
        CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub := by
      rw [Subgroup.map_comap_eq, inf_of_le_right hrange]
    have hT2 : CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub.comap
        (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g) ≤
        CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup τ := by
      intro t ht
      have h1 : CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g t ∈
          (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup τ).map
            (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g) := by
        rw [hmap]
        exact CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub_le ht
      obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.1 h1
      rwa [← hinj hst]
    have hTC : (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub.comap
        (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g)).map L.subtype ≤
        Subgroup.centralizer ({x} : Set X) := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hz
      have h1 := hT2 ht
      rw [hfix, Subgroup.mem_subgroupOf] at h1
      exact h1.2
    let f : ↥((CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub.comap
        (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g)).map L.subtype) ≃*
        ↥CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub :=
      ((CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub.comap
        (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g)).equivMapOfInjective L.subtype
        L.subtype_injective).symm.trans
        (((CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub.comap
          (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g)).equivMapOfInjective _
          hinj).trans (MulEquiv.subgroupCongr hT1))
    haveI := CFSG.HardMathSupport.Dickson.Bal207.D42Tri.isSimpleGroup_l0Sub
    have hsT := f.isSimpleGroup
    have hcT : Nat.card ↥((CFSG.HardMathSupport.Dickson.Bal207.D42Tri.l0Sub.comap
        (CFSG.HardMathSupport.Dickson.Bal207.D42Tri.conjEmb e g)).map L.subtype) = 6048 := by
      rw [Nat.card_congr f.toEquiv, CFSG.HardMathSupport.Dickson.Bal207.D42Tri.card_l0Sub]
    obtain ⟨a₁, a₂, ha⟩ := exists_noncomm_of_isSimpleGroup hsT (by rw [hcT]; norm_num)
    exact CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hsT
      (fun ⟨hcomm⟩ => ha (hcomm.comm a₁ a₂)) (by rw [hcT]; norm_num)
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hsolv hTC)
  ·
    rw [hc] at hmap
    obtain ⟨hQH, hQp, hQmax⟩ := hQ
    let ε : ↥(L ⊓ Subgroup.centralizer ({x} : Set X)) ≃*
        ↥(CFSG.Sporadic.Schreier.centralizerIn CFSG.EvenSmallLie.OmegaEight.omegaT
          CFSG.HardMathSupport.Dickson.Bal207.D42Tri.t2Perm) :=
      (Subgroup.subgroupOfEquivOfLe inf_le_left).symm.trans
        ((MulEquiv.subgroupCongr hfix.symm).trans
          (((CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup τ).equivMapOfInjective _
            hinj).trans (MulEquiv.subgroupCongr hmap)))
    have hQ3 : ∀ q ∈ Q, q ^ 3 = 1 := by
      intro q hq
      obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
      have hk' : (⟨q, hQH hq⟩ : ↥(L ⊓ Subgroup.centralizer ({x} : Set X))) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      have h1 : ((ε ⟨q, hQH hq⟩ : ↥(CFSG.Sporadic.Schreier.centralizerIn
          CFSG.EvenSmallLie.OmegaEight.omegaT CFSG.HardMathSupport.Dickson.Bal207.D42Tri.t2Perm)) :
          Equiv.Perm (Fin 360)) ^ 3 ^ k = 1 := by
        rw [← Subgroup.coe_pow, ← map_pow, hk', map_one, Subgroup.coe_one]
      have h2 := pow_three_eq_one_of_noNine hT (ε ⟨q, hQH hq⟩).2 k h1
      have h3 : ε (⟨q, hQH hq⟩ ^ 3) = 1 := by
        rw [map_pow]
        exact Subtype.ext (by simpa using h2)
      rw [map_eq_one_iff ε ε.injective] at h3
      simpa using congrArg Subtype.val h3
    refine ⟨hQ3, ?_⟩
    have hCc := CFSG.HardMathSupport.Dickson.Bal207.D42Tri.card_centralizer_t2
    have hHc : Nat.card ↥(L ⊓ Subgroup.centralizer ({x} : Set X)) = 216 := by
      rw [Nat.card_congr ε.toEquiv, hCc]
    have hf : (216 : ℕ).factorization 3 = 3 := by
      rw [show (216 : ℕ) = 3 ^ 3 * 8 by norm_num, Nat.factorization_mul (by norm_num)
        (by norm_num), Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
        Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    let S₁ : Sylow 3 ↥(L ⊓ Subgroup.centralizer ({x} : Set X)) :=
      { toSubgroup := Q.subgroupOf (L ⊓ Subgroup.centralizer ({x} : Set X))
        isPGroup' := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
        is_maximal' := fun {Q'} hQ'p hle => by
          have hR := hQmax (Q'.map (L ⊓ Subgroup.centralizer ({x} : Set X)).subtype)
            (Subgroup.map_subtype_le Q') (hQ'p.map _) (fun q hq =>
              ⟨⟨q, hQH hq⟩, hle (Subgroup.mem_subgroupOf.2 hq), rfl⟩)
          rw [← hR]
          exact (Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) Q').symm }
    have hQc : Nat.card Q = 27 := by
      have h1 := Sylow.card_eq_multiplicity S₁
      rw [hHc, hf] at h1
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv]
      exact h1.trans (by norm_num)
    by_contra hab
    push Not at hab
    have hQa : CFSG.Open.IsElemAbelian 3 Q :=
      ⟨⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩, hQ3⟩
    have hxa : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hcomm : ∀ a ∈ Q, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact ((Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1
        (hQH ha).2) i))
    have hA := CFSG.Open.IsElemAbelian.sup_of_commute hQa hxa hcomm
    have hAC : Q ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set X) :=
      sup_le (hQH.trans inf_le_right) (by
        rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 rfl)
    have hAp : IsPGroup 3 ↥(Q ⊔ Subgroup.zpowers x) := fun a =>
      ⟨1, Subtype.ext (by simpa using hA.2 a a.2)⟩
    obtain ⟨m, hm⟩ := hAp.exists_card_eq
    have hlt : Nat.card Q < Nat.card ↥(Q ⊔ Subgroup.zpowers x) := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun heq => hxL ?_)
      have : x ∈ Q := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      exact (hQH this).1
    rw [hQc, hm] at hlt
    have hm4 : 4 ≤ m := by
      by_contra h
      push Not at h
      interval_cases m <;> norm_num at hlt
    have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hAC hA hm
    omega

theorem input29_5'Lie_of_id
    (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4)
    (hId : Input29_5'LieId) : InputsMisc8.Input29_5'Lie := by
  intro X _ _ L hLn hq hK hC d he hchev hrk x hx hC4 hrk3 hsolv
  obtain ⟨hD42, hSyl⟩ := hId X L hLn hq hK hC d he hchev hrk x hx hC4 hrk3 hsolv
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hLn
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_cent hC
  have hL42 : catalogIs ↥L CFSG.LocalAnalysis.GLTheoremA.S9.isD4two :=
    catalogIs_of_center_eq_bot hZ hD42
  refine ⟨not_mem_of_d42 hD4 hq hK hD42 hx hrk3, ?_, hSyl, ?_⟩
  ·
    refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) fun E _ hE => ?_
    have hψi : Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      rw [MonoidHom.mem_ker] at hg
      rw [Subgroup.mem_bot]
      refine hC g fun l hl => ?_
      have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : X)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc g * l = g * l * g⁻¹ * g := by group
        _ = l * g := by rw [h1]
    have hPa : CFSG.Open.IsElemAbelian 3 (E.map (MulAut.conjNormal : X →* MulAut ↥L)) :=
      CFSG.SectionRank.isElemAbelian_map hE _
    rw [← Subgroup.card_map_of_injective hψi]
    by_cases hPi : E.map (MulAut.conjNormal : X →* MulAut ↥L) ≤
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L
    · have hconj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro l hl
        rw [MonoidHom.mem_ker] at hl
        have hlZ : l ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.2 fun g => by
          have h1 := congrArg (fun φ : MulAut ↥L => φ g) hl
          simp only [MulAut.conj_apply, MulAut.one_apply] at h1
          calc g * l = l * g * l⁻¹ * l := by rw [h1]
            _ = l * g := by group
        rw [hZ] at hlZ
        exact hlZ
      have hFm : ((E.map (MulAut.conjNormal : X →* MulAut ↥L)).comap
          (MulAut.conj : ↥L →* MulAut ↥L)).map MulAut.conj =
          E.map (MulAut.conjNormal : X →* MulAut ↥L) := by
        rw [Subgroup.map_comap_eq]
        exact inf_of_le_right hPi
      rw [← hFm, Subgroup.card_map_of_injective hconj]
      exact (CFSG.LocalAnalysis.GLTheoremA.CatB.card_le_81_d4 hL42
        (isElemAbelian_comap hconj hPa)).trans (by norm_num)
    · exact (CFSG.LocalAnalysis.GLTheoremA.D4XF.d4two_aut_le hL42 _ hPa hPi).trans
        (by norm_num)
  ·
    intro D hDL hDa hD9
    have hD'c : Nat.card (D.comap L.subtype) = 9 := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective, Subgroup.map_comap_eq,
        Subgroup.range_subtype, inf_of_le_right hDL, hD9]
    have hLie : CFSG.Blueprint.LieModel ↥L .POmegaPlus 4 2 1 :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        CFSG.LocalAnalysis.GLTheoremA.D4XF.statedModel_of_d4two hL42⟩
    obtain ⟨E, hEa, hE81, hDE⟩ := CFSG.RankThree.PartTwo.Sec4.Item434O8pOuter.exists_e81_of_e9_o8p
      hLie (isElemAbelian_comap L.subtype_injective hDa) hD'c
    have hEle := CFSG.LocalAnalysis.GLTheoremA.CatB.card_le_81_d4 hL42 hEa
    refine ⟨E.map L.subtype, fun y hy => ⟨⟨y, hDL hy⟩, hDE hy, rfl⟩, Subgroup.map_subtype_le E,
      CFSG.SectionRank.isElemAbelian_map hEa _, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective]
    norm_num
    omega

end Lie

section SporAssembly

theorem no295Spor_all (hbr : SporadicBridges) (hord : SporadicOrdersTable) :
    ∀ s : TauCeti.SporadicName, No295Spor s := by
  intro s
  cases s with
  | M11 => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | M12 => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | M22 => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | M23 => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | M24 => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | J1 => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | J2 => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | J3 => exact no295Spor_of_carrier hbr .J3 (fun {_} => no295_J3)
  | J4 => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd, CFSG.Open.orderJ4])
  | HS => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | McL => exact no295Spor_of_carrier hbr .McL (fun {_} => no295_McL)
  | He => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd])
  | Ru => exact no295Spor_of_sporOrd hord (by norm_num [sporOrd, CFSG.Open.orderRu])
  | Suz => exact no295Spor_of_carrier hbr .Suz (fun {_} => no295_Suz)
  | ONan => exact no295Spor_of_sporOrd_five hord (by norm_num [sporOrd, CFSG.Open.orderON])
  | Co1 => exact no295Spor_of_carrier hbr .Co1 (fun {_} => no295_Co1)
  | Co2 => exact no295Spor_of_carrier hbr .Co2 (fun {_} => no295_Co2)
  | Co3 => exact no295Spor_of_carrier hbr .Co3 (fun {_} => no295_Co3)
  | Fi22 => exact no295Spor_of_carrier hbr .Fi22 (fun {_} => no295_Fi22)
  | Fi23 => exact no295Spor_of_carrier hbr .Fi23 (fun {_} => no295_Fi23)
  | Fi24Prime => exact no295Spor_of_carrier hbr .Fi24Prime (fun {_} => no295_Fi24)
  | HN => exact no295Spor_of_carrier hbr .HN (fun {_} => no295_HN)
  | Ly => exact no295Spor_of_carrier hbr .Ly (fun {_} => no295_Ly)
  | Th => exact no295Spor_of_carrier hbr .Th (fun {_} => no295_Th)
  | B => exact no295Spor_of_carrier hbr .B (fun {_} => no295_B)
  | M => exact no295Spor_of_carrier hbr .M (fun {_} => no295_M)

theorem input29_5'Spor_holds (hout : SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hord : SporadicOrdersTable) : InputsMisc8.Input29_5'Spor :=
  input29_5'Spor_of hout (no295Spor_all hbr hord)

end SporAssembly

section RestAssembly

theorem input29_5'Rest_of_lieId (hout : SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hord : SporadicOrdersTable)
    (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4)
    (hId : Input29_5'LieId) : InputsMisc8.Input29_5'Rest :=
  ⟨input29_5'Spor_holds hout hbr hord, input29_5'Lie_of_id hD4 hId⟩

theorem input29_5'Rest_of_split (hout : SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hord : SporadicOrdersTable)
    (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4)
    (hN : Input29_5'LieNotD42) (hD : Input29_5'LieD42) : InputsMisc8.Input29_5'Rest :=
  input29_5'Rest_of_lieId hout hbr hord hD4 (input29_5'LieId_of_split hN hD)

theorem input29_5'Rest_of_residuals (hout : SporadicOuterLeTwo) (hbr : SporadicBridges)
    (hord : SporadicOrdersTable)
    (hD4 : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.InputD4)
    (hN : Input29_5'LieNotD42) (hT : D42T2NoNine) : InputsMisc8.Input29_5'Rest :=
  input29_5'Rest_of_split hout hbr hord hD4 hN (input29_5'LieD42_of_t2 hD4 hT)

@[expose] def Input29_5'LieRest : Prop :=
  Input29_5'LieNotD42 ∧ D42T2NoNine

end RestAssembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295
