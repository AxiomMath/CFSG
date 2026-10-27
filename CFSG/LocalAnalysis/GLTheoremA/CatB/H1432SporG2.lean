module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432G2Type
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeB3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeM3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.SporG2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Dickson.I271 (ShapeRkAt)
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (NoCardComp noCardComp_of_mulEquiv noCardComp_conj
  noCardComp_of_shapeRkAt noCardComp_of_pConstrained)
open CFSG.LocalAnalysis.GLTheoremA.K14Spor


section Suz

open Subgroup CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Dickson.I271.TabSuzA
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)

theorem noCardComp_suzM_g2
    (k : ↥suzM) (hk : orderOf k = 3) : NoCardComp 4245696 k := by
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
  have hY : NoCardComp 4245696 y := by
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
          norm_num
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
      norm_num
  have h' := noCardComp_conj hY H
  have hk' : H * y * H⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h'

theorem cardRow_suz_g2
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : CardRow 4245696 .Suz := by
  have e : NativeSporadic.Carrier .Suz ≃* ↥suzM := suzEquivM
  have hc : Nat.card ↥suzM = 448345497600 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz
  haveI : IsSimpleGroup ↥suzM :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e.symm
  exact cardRow_of_model (s := .Suz) (Q := ↥suzM) hOut (e.symm.trans (hbr .Suz).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    noCardComp_suzM_g2

end Suz

section Shape

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c

theorem cardRow_shape_g2
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    CardRow 4245696 .Fi22 ∧ CardRow 4245696 .Fi23 ∧ CardRow 4245696 .Co1 := by
  refine ⟨?_, ?_, ?_⟩
  · have hc : Nat.card (NativeSporadic.Carrier .Fi22) = 64561751654400 :=
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
    norm_num at hcT
  · have hc : Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
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
    norm_num at hcT
  · obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := CFSG.HardMathSupport.Dickson.I271.TabCo1.co1_model_five hbr
    have hC := CFSG.HardMathSupport.Dickson.I271.TabCo1.tabCo1_centShapeRk_three_good
      (Good := fun T _ => Nat.card T ≠ 4245696)
      (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
      (fun T _ e hc => by
        have h1 : Nat.card T = 3265920 := (Nat.card_congr e.toEquiv).trans
          CFSG.LieType.Multipliers.U43.card_X₀
        rw [h1] at hc
        norm_num at hc)
      (by
        show Nat.card ↥(alternatingGroup (Fin 9)) ≠ 4245696
        rw [CFSG.HardMathSupport.Dickson.I271.TabCo1.card_alt_nine]
        norm_num)
      (fun _ _ hc _ => by
        show _ ≠ 4245696
        rw [hc]
        norm_num)
      (hbr .Suz)
    exact @cardRow_of_centShapeRk 4245696 .Co1 _ _ hfin hs hOut b hnc _ _ hC (fun _ _ h => h)

end Shape

theorem names_of_dvd_g2
    (s : TauCeti.SporadicName) (h : 4245696 ∣ sporOrd s) :
    s = .Suz ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Co1 ∨ s = .Fi24Prime ∨ s = .Th ∨ s = .B ∨ s = .M := by
  revert h
  cases s <;> decide +kernel

theorem i1432SporG2S_holds
    : ClsRed.I1432SporG2S := by
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOrd := CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
  intro S _ _ s e β hβ3 hβ1 J hJ hT
  obtain ⟨e'⟩ := e
  have hcJ : Nat.card (PSimple 3 J) = 4245696 :=
    ClsRed.card_g2three CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hT
  have hd : 4245696 ∣ sporOrd s := by
    rw [← hcJ, ← (Nat.card_congr e'.toEquiv).trans (hOrd s)]
    have h2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
    have h3 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
    exact h2.trans (h3.trans (Subgroup.card_subgroup_dvd_card J))
  obtain ⟨hF22, hF23, hC1⟩ := cardRow_shape_g2 hOut hbr
  rcases names_of_dvd_g2 s hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (cardRow_suz_g2 hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hcJ).elim
  · exact (hF22 S ⟨e'⟩ β hβ3 hβ1 J hJ hcJ).elim
  · exact (hF23 S ⟨e'⟩ β hβ3 hβ1 J hJ hcJ).elim
  · exact (hC1 S ⟨e'⟩ β hβ3 hβ1 J hJ hcJ).elim
  · exact Or.inr rfl
  · exact Or.inl rfl
  · exact (BMType.typeRow3_B typeHyp3_g2three 5 Nat.prime_five (by norm_num) (by norm_num)
      S ⟨e'⟩ β hβ3 hβ1 J hJ hT).elim
  · exact (BMType.typeRow3_M typeHyp3_g2three 5 Nat.prime_five (by norm_num) (by norm_num)
      5 Nat.prime_five (by norm_num) (by norm_num) S ⟨e'⟩ β hβ3 hβ1 J hJ hT).elim

end CFSG.LocalAnalysis.GLTheoremA.H1420.SporG2

end
