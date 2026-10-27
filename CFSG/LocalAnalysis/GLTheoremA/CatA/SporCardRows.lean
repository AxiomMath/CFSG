module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K14Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Dickson.I271 (ShapeRkAt CentShapeRk)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (NoCardComp noCardComp_of_mulEquiv noCardComp_conj
  noCardComp_of_shapeRkAt noCardComp_of_pConstrained)


section Shape

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c

theorem cardRow_fi22'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (h : n ≠ 3265920) : CardRow n .Fi22 := by
  have hc : Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 :=
    CFSG.Sporadic.Fi22.card_Fi22
  haveI : Finite (NativeSporadic.Carrier .Fi22) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Fi22) := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  refine cardRow_of_centShapeRk (s := .Fi22) hOut (hbr .Fi22).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    fi22CentShapeRk_native ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀] at hcT
  exact h hcT.symm

theorem cardRow_th'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (h : n ≠ 4245696) : CardRow n .Th := by
  have hc : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.PartOne.CTP.card_Th
  haveI : Finite (NativeSporadic.Carrier .Th) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Th) :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_Th
      CFSG.Sporadic.Th.th_kernel_facts
  refine cardRow_of_centShapeRk (s := .Th) hOut (hbr .Th).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    thCentShapeRk_native ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.GH74.QTGen4.Recog.G23.ghat_card] at hcT
  exact h hcT.symm

theorem cardRow_fi23'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (h : n ≠ 4585351680) : CardRow n .Fi23 := by
  have hc : Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  haveI : Finite (NativeSporadic.Carrier .Fi23) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Fi23) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  refine cardRow_of_centShapeRk (s := .Fi23) hOut (hbr .Fi23).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    fi23CentShapeRk_native ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.HardMathSupport.Dickson.I271.tabFi23_card_om] at hcT
  exact h hcT.symm

theorem cardRow_fi24'
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {n : ℕ}
    (h1 : n ≠ 4952179814400) (h2 : n ≠ 4245696) : CardRow n .Fi24Prime := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows.fi24_model hbr
  have hC := CFSG.HardMathSupport.Dickson.I271.TabFi24.centShapeRk_J_good
    (Good := fun T _ => Nat.card T ≠ n)
    (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
    (fun _ _ _ _ hT => by rw [hT]; exact Ne.symm h1)
    (fun _ _ _ _ hT => by rw [hT]; exact Ne.symm h2)
  exact @cardRow_of_centShapeRk n .Fi24Prime _ _ hfin hs hOut b hnc _ _ hC (fun _ _ h => h)

theorem cardRow_on'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (h : n ≠ 360) : CardRow n .ONan := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    Finite.of_equiv _ CFSG.ONSchreier.onEquivPv.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  refine cardRow_of_centShapeRk (s := .ONan) hOut (hbr .ONan).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    CFSG.HardMathSupport.Dickson.I271.onThree_centShapeRk ?_
  intro T _ hT hcT
  obtain ⟨-, ⟨e⟩⟩ := hT
  rw [Nat.card_congr e.toEquiv, I1431Z.card_alt_six_eq] at hcT
  exact h hcT.symm

theorem cardRow_ly'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (h : n ≠ 898128000) : CardRow n .Ly := by
  have hc : Nat.card (NativeSporadic.Carrier .Ly) = 51765179004000000 := CFSG.Sporadic.Ly.card_Ly'
  haveI : Finite (NativeSporadic.Carrier .Ly) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Ly) := CFSG.Sporadic.Ly.isSimpleGroup_Ly
  refine cardRow_of_centShapeRk (s := .Ly) hOut (hbr .Ly).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    lyShape_three ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.McL.card_McL] at hcT
  exact h hcT.symm

theorem cardRow_mcl'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) (n : ℕ) :
    CardRow n .McL := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 :=
    CFSG.Sporadic.McL.card_McL
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hsh := CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL
  refine cardRow_of_model (s := .McL) hOut (hbr .McL).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    fun k hk => ?_
  have hk1 : k ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hk; norm_num at hk
  exact noCardComp_of_pConstrained (hsh k hk1 (by rw [← hk]; exact pow_orderOf_eq_one k))

end Shape

section Suz

open Subgroup CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Dickson.I271.TabSuzA
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)

theorem noCardComp_suzM'
    {n : ℕ} (h1 : n ≠ 3265920) (h2 : ¬ n ∣ 3240) (k : ↥suzM)
    (hk : orderOf k = 3) : NoCardComp n k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 1782)) = 3 := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := suz_exists_conj_classes k.2 hs3
  let H : ↥suzM := ⟨h, hh⟩
  let y : ↥suzM := H⁻¹ * k * H
  have hy : (y : Equiv.Perm (Fin 1782)) = c ^ e := by
    show h⁻¹ * (k : Equiv.Perm (Fin 1782)) * h = c ^ e
    rw [← hcon]
    group
  have hY : NoCardComp n y := by
    rcases hc with rfl | rfl | rfl
    · refine noCardComp_of_centralizer_eq (b := ⟨fuseXA, fuseXA_mem⟩)
        (I1431Z.centralizer_sub_eq suzM ?_) ?_
      · rw [hy]
        exact CFSG.Quasithin.Kleidman.centralizer_pow_eq fuseXA_pow he
      · obtain ⟨hq, hcen, ⟨eT⟩⟩ := aSub_quasisimple
        set k' : ↥suzM := ⟨fuseXA, fuseXA_mem⟩ with hk'
        have hmap : (Subgroup.centralizer ({k'} : Set ↥suzM)).map suzM.subtype = aSub := by
          rw [map_centralizer_subtype' suzM k']
          exact aSub_eq.symm
        let e' : ↥(Subgroup.centralizer ({k'} : Set ↥suzM)) ≃* ↥aSub :=
          ((Subgroup.centralizer ({k'} : Set ↥suzM)).equivMapOfInjective suzM.subtype
            suzM.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
        have hz3 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ^ 3 = 1 := Subtype.ext (by simpa using fuseXA_pow)
        have hz1 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ≠ 1 :=
          fun h => fuseXA_ne_one (congrArg Subtype.val h)
        have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := orderOf_eq_prime hz3 hz1
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        refine noCardComp_of_centralizer_equiv e' hq ?_ (by rw [card_aSub]; norm_num) ?_
        · have h3 : IsPGroup 3 ↥(Subgroup.zpowers (⟨fuseXA, aX_mem⟩ : ↥aSub)) :=
            IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
          exact h3.of_equiv (MulEquiv.subgroupCongr hcen.symm)
        · rw [Nat.card_congr eT.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀]
          exact Ne.symm h1
    · obtain ⟨hcard, -, hle, hnorm, hcent⟩ := TabSuzB.caseB_spec
      refine noCardComp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective suzM.subtype suzM.subtype_injective ?_
      rw [map_centralizer_subtype', hy,
        CFSG.Quasithin.Kleidman.centralizer_pow_eq (c := fuseXB) xBPerm_pow he]
      show CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
        (centralizer {xBPerm} ⊓ suzM)
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨hC, hCcard⟩ := Cy_eq
      refine noCardComp_of_not_dvd ?_
      rw [I1431Z.card_centralizer_sub, hy,
        CFSG.Quasithin.Kleidman.centralizer_pow_eq yPerm_pow he, ← hC, hCcard]
      exact h2
  have h' := noCardComp_conj hY H
  have hk' : H * y * H⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h'

theorem cardRow_suz'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (h1 : n ≠ 3265920) (h2 : ¬ n ∣ 3240) : CardRow n .Suz := by
  have e : NativeSporadic.Carrier .Suz ≃* ↥suzM := suzEquivM
  have hc : Nat.card ↥suzM = 448345497600 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz
  haveI : IsSimpleGroup ↥suzM :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e.symm
  exact cardRow_of_model (s := .Suz) (Q := ↥suzM) hOut (e.symm.trans (hbr .Suz).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noCardComp_suzM' h1 h2)

end Suz

section Co3

open Subgroup CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.Co3Cent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.Sporadic.Schreier.Co3

theorem noCardComp_co3P'
    {n : ℕ} (h : ¬ n ∣ 4536) (k : ↥co3P) (hk : orderOf k = 3) :
    NoCardComp n k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 276)) = 3 := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  obtain ⟨h0, hh, c, hc, e, he, hcon⟩ := exists_conj_classes k.2 hs3
  let H : ↥co3P := ⟨h0, hh⟩
  let y : ↥co3P := H⁻¹ * k * H
  have hy : (y : Equiv.Perm (Fin 276)) = c ^ e := by
    show h0⁻¹ * (k : Equiv.Perm (Fin 276)) * h0 = c ^ e
    rw [← hcon]
    group
  have hY : NoCardComp n y := by
    rcases hc with rfl | rfl | rfl
    · obtain ⟨hX3, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
      refine noCardComp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
      rw [map_centralizer_subtype', hy, CFSG.Quasithin.Kleidman.centralizer_pow_eq hX3 he]
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨hX3, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
      refine noCardComp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
      rw [map_centralizer_subtype', hy, CFSG.Quasithin.Kleidman.centralizer_pow_eq hX3 he]
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨⟨hC, hCcard⟩, -⟩ := caseC_spec
      refine noCardComp_of_not_dvd ?_
      rw [I1431Z.card_centralizer_sub, hy,
        CFSG.Quasithin.Kleidman.centralizer_pow_eq yPerm_pow he, ← hC, hCcard]
      exact h
  have h' := noCardComp_conj hY H
  have hk' : H * y * H⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h'

theorem cardRow_co3'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (h : ¬ n ∣ 4536) : CardRow n .Co3 := by
  have e : NativeSporadic.Carrier .Co3 ≃* ↥co3P := co3PermEquiv
  have hc : Nat.card ↥co3P = 495766656000 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co3.card_Co3
  haveI : IsSimpleGroup ↥co3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e.symm
  exact cardRow_of_model (s := .Co3) (Q := ↥co3P) hOut (e.symm.trans (hbr .Co3).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noCardComp_co3P' h)

end Co3

section J3

open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.Sporadic.Schreier

theorem noCardComp_j3P
    {n : ℕ} (h1 : ¬ n ∣ 1080) (h2 : ¬ n ∣ 243) (k : ↥j3P)
    (hk : orderOf k = 3) : NoCardComp n k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 6156)) = 3 := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  obtain ⟨k₀, hk₀, c, hc, e, he, hkeq⟩ := j3t_fusion k.2 hs3
  let K₀ : ↥j3P := ⟨k₀, hk₀⟩
  let y : ↥j3P := K₀⁻¹ * k * K₀
  have hy : (y : Equiv.Perm (Fin 6156)) = c ^ e := by
    show k₀⁻¹ * (k : Equiv.Perm (Fin 6156)) * k₀ = c ^ e
    rw [hkeq]
    group
  have hY : NoCardComp n y := by
    refine noCardComp_of_not_dvd ?_
    rw [I1431Z.card_centralizer_sub, hy]
    rcases hc with rfl | rfl
    · rw [CFSG.Quasithin.Kleidman.centralizer_pow_eq (c := j3tXA)
        (j3tReps_spec (c := 0) (by norm_num)).2 he,
        CFSG.AGLEmbeddingD2.Wilson.Census228Spor.card_centralizer_XA]
      exact h1
    · rw [CFSG.Quasithin.Kleidman.centralizer_pow_eq (c := j3tXB)
        (j3tReps_spec (c := 1) (by norm_num)).2 he,
        CFSG.AGLEmbeddingD2.Wilson.Census228Spor.card_centralizer_XB]
      exact h2
  have h := noCardComp_conj hY K₀
  have hk' : K₀ * y * K₀⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h

theorem cardRow_j3'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (h1 : ¬ n ∣ 1080) (h2 : ¬ n ∣ 243) : CardRow n .J3 := by
  have e : NativeSporadic.Carrier .J3 ≃* ↥j3P :=
    CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.j3CarrierEquiv
  have hc : Nat.card ↥j3P = 50232960 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  haveI : IsSimpleGroup ↥j3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J3.isSimpleGroup_J3 e.symm
  exact cardRow_of_model (s := .J3) (Q := ↥j3P) hOut (e.symm.trans (hbr .J3).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noCardComp_j3P h1 h2)

end J3

section Co2

open Subgroup CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.Co2Cent CFSG.HardMathSupport.Dickson.I271.U42Presentation

theorem co2_centShapeRk_card
    {n : ℕ} (hn : n ≠ 25920) :
    CentShapeRk 3 (fun T _ => Nat.card T ≠ n) (fun _ _ => True) ↥co2P := by
  have hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Nat.card T ≠ n →
      Nat.card T' ≠ n := fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc)
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨hXA3, -, hXAm, -⟩ := co2CaseA_spec
  obtain ⟨hXB3, -, hXBm, -⟩ := co2CaseB_spec
  have hA : ShapeRkAt 3 (fun T _ => Nat.card T ≠ n) (fun _ _ => True)
      (⟨co2XA, hXAm⟩ : ↥co2P) := by
    left
    refine pConstrainedShape_of_map_injective co2P.subtype co2P.subtype_injective ?_
    rw [map_centralizer_subtype']
    obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := co2CaseA_spec
    exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_forall_conj hnorm)
      (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent
  have hB : ShapeRkAt 3 (fun T _ => Nat.card T ≠ n) (fun _ _ => True)
      (⟨co2XB, hXBm⟩ : ↥co2P) := by
    obtain ⟨-, -, -, hcard, hLC, hLn, hcent, hrels⟩ := co2CaseB_spec
    obtain ⟨e⟩ := nonempty_mulEquiv_QP45_of_rels uvGen hrels hcard
    exact shapeRkAt_of_subgroup_data_nq Nat.prime_three hGood hRk co2P ⟨co2XB, hXBm⟩ Lsub hLC hLn
      (isSimpleGroup_of_equiv_QP45 e) (nonabelian_of_equiv_QP45 e)
      (three_dvd_card_of_equiv_QP45 e) hcent
      (by
        have hL : Nat.card ↥Lsub = 25920 := (Nat.card_congr e.toEquiv).trans card_QP45_eq
        rw [hL]
        exact Ne.symm hn) trivial
  intro k hk1 hkp
  have hs3 : orderOf (k : Equiv.Perm (Fin 2300)) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : (k : Equiv.Perm (Fin 2300)) ^ 3 = 1 := by
      have := congrArg Subtype.val hkp
      simpa using this
    have h2 : (k : Equiv.Perm (Fin 2300)) ≠ 1 := fun h => hk1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := co2_exists_conj_classes k.2 hs3
  have hrep : ∃ c' : ↥co2P, (c' : Equiv.Perm (Fin 2300)) = c ∧ c' ^ 3 = 1 ∧
      ShapeRkAt 3 (fun T _ => Nat.card T ≠ n) (fun _ _ => True) c' := by
    rcases hc with rfl | rfl
    · exact ⟨⟨co2XA, hXAm⟩, rfl, Subtype.ext (by simpa using hXA3), hA⟩
    · exact ⟨⟨co2XB, hXBm⟩, rfl, Subtype.ext (by simpa using hXB3), hB⟩
  obtain ⟨c', hc'val, hc'3, hshape⟩ := hrep
  have hshape' : ShapeRkAt 3 (fun T _ => Nat.card T ≠ n) (fun _ _ => True) (c' ^ e) :=
    ShapeRkAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc'3 he).symm hshape
  have hconj := ShapeRkAt.of_equiv Nat.prime_three hGood hRk
    (MulAut.conj (⟨h, hh⟩ : ↥co2P)) hshape'
  have hk : (MulAut.conj (⟨h, hh⟩ : ↥co2P)) (c' ^ e) = k := by
    apply Subtype.ext
    rw [← hcon, ← hc'val]
    simp [MulAut.conj_apply]
  rw [hk] at hconj
  exact hconj

theorem cardRow_co2'
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (hn : n ≠ 25920) : CardRow n .Co2 := by
  have e : CFSG.Blueprint.NativeSporadic.Co2 ≃* ↥co2P := co2PermEquiv
  haveI : IsSimpleGroup ↥co2P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 e.symm
  have hc : Nat.card ↥co2P = 42305421312000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Co2.card_Co2
  have b : ↥co2P ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group := e.symm.trans (hbr .Co2).some
  exact cardRow_of_centShapeRk hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (co2_centShapeRk_card hn) fun _ _ h => h

end Co2

end CFSG.LocalAnalysis.GLTheoremA.K14Spor

end
