module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.RowModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModelClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Abstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitCountLe
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeIITrue
public import Certificates.Certificate441694
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIP

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def tab6C (i : Fin 8) : ↥P1408 := (tab6Row i).rowP wordAZ

theorem natCard_elem2 (n : ℕ) : Nat.card (Elem2 n) = 2 ^ n := by
  rw [Elem2, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]

theorem natCard_d8_sym3 : Nat.card (DihedralGroup 4 × Sym 3) = 48 := by
  rw [Nat.card_prod, DihedralGroup.nat_card, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]

theorem natCard_elem2_d8 : Nat.card (Elem2 2 × DihedralGroup 4) = 32 := by
  rw [Nat.card_prod, natCard_elem2, DihedralGroup.nat_card]
  norm_num

theorem natCard_z2_d10 : Nat.card (Z 2 × DihedralGroup 5) = 20 := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, DihedralGroup.nat_card]

theorem natCard_z2_d8 : Nat.card (Z 2 × DihedralGroup 4) = 16 := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, DihedralGroup.nat_card]

theorem nonempty_mulEquiv_of_sub {ws : List (List ℕ)} {r : OrbRow} {T : Type} [Group T]
    (hsub : closure (elemW '' {w | w ∈ ws}) ≤
      P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({r.repElem wordAZ} : Set (Equiv.Perm (Fin 1408))))
    (e : Nonempty (↥(closure (elemW '' {w | w ∈ ws})) ≃* T))
    (hT : Nat.card T = Nat.card ↥(Gx (wordP wordAZ) ⊓ Gx (r.rowP wordAZ))) :
    Nonempty (↥(Gx (wordP wordAZ) ⊓ Gx (r.rowP wordAZ)) ≃* T) := by
  obtain ⟨e⟩ := e
  have hc : Nat.card ↥(P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({r.repElem wordAZ} : Set (Equiv.Perm (Fin 1408)))) ≤
      Nat.card ↥(closure (elemW '' {w | w ∈ ws})) := by
    rw [Nat.card_congr e.toEquiv, hT, natCard_inf_Gx_subtype P1408 (wordP wordAZ) (r.rowP wordAZ)]
    rfl
  have hS := Subgroup.eq_of_le_of_card_ge hsub hc
  exact ⟨(infGxSubtypeEquiv P1408 (wordP wordAZ) (r.rowP wordAZ)).trans
    ((MulEquiv.subgroupCongr hS).symm.trans e)⟩

section Cert

theorem wordP_wordAZ : wordP wordAZ = pA * pZ := Subtype.ext elemW_wordAZ

private theorem tab6_facts (hP : Nat.card ↥P1408 = 177408000) : Tab6Facts :=
  Certificates.certificate441694 hP

private theorem tab6C_mem_base (hP : Nat.card ↥P1408 = 177408000) (i : Fin 8) :
    tab6C i ∈ tab6Base pA pZ (pA * pZ) := by
  refine ⟨?_, ?_⟩
  · have h := isConj_wordP_rowP wordAZ (tab6Row i)
    rwa [wordP_wordAZ] at h
  · have h := (tab6_facts hP).ne i
    rwa [wordP_wordAZ] at h

private theorem isShapeFiveC_of_conj (hP : Nat.card ↥P1408 = 177408000) {x : ↥P1408}
    (h : IsConj (repP fix5C) x) : IsShapeCentralizerFiveC ↥(Gx x) := by
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj h
  exact IsShapeCentralizerFiveC.of_mulEquiv e (isShape_repP_five_C hP)

private theorem isShapeFiveB_of_conj (hP : Nat.card ↥P1408 = 177408000) {x : ↥P1408}
    (h : IsConj (repP fix5B) x) : IsShapeCentralizerFiveB ↥(Gx x) := by
  obtain ⟨e⟩ := nonempty_centralizer_mulEquiv_of_isConj h
  exact IsShapeCentralizerFiveB.of_mulEquiv e (isShape_repP_five_B hP)

theorem tab6C_mem_set (hP : Nat.card ↥P1408 = 177408000) (i : Fin 8) :
    tab6C i ∈ tab6Set pA pZ pB pZ₁ (pA * pZ) i := by
  have F := tab6_facts hP
  have h0 := F.row0
  have h1 := F.row1
  have h2 := F.row2
  have h3 := F.row3
  have h4 := F.row4
  have h5 := F.row5
  have h6 := F.row6
  have h7 := F.row7
  rw [wordP_wordAZ] at h0 h1 h2 h3 h4 h5 h6 h7
  fin_cases i
  · exact ⟨tab6C_mem_base hP 0, Or.inr (Or.inl h0)⟩
  · exact ⟨tab6C_mem_base hP 1, Or.inl h1⟩
  · exact ⟨tab6C_mem_base hP 2, h2⟩
  · exact ⟨tab6C_mem_base hP 3, h3.1, Or.inl h3.2⟩
  · exact ⟨tab6C_mem_base hP 4, h4.1, Or.inr (Or.inl h4.2)⟩
  · exact ⟨tab6C_mem_base hP 5, h5.1, isShapeFiveC_of_conj hP h5.2⟩
  · exact ⟨tab6C_mem_base hP 6, h6.1, isShapeFiveB_of_conj hP h6.2⟩
  · exact ⟨tab6C_mem_base hP 7, h7.1, Or.inr (Or.inl h7.2)⟩

theorem tab6_base_ncard (hP : Nat.card ↥P1408 = 177408000) :
    (tab6Base pA pZ (pA * pZ)).ncard = 5774 := by
  have hcl : {c : ↥P1408 | IsConj (pA * pZ) c}.ncard = 5775 := by
    rw [ncard_isConj_subtype P1408 (pA * pZ)]
    exact (invClasses_classSpec hP).2.1.class_ncard
  have hset : tab6Base pA pZ (pA * pZ) = {c | IsConj (pA * pZ) c} \ {pA * pZ} := by
    ext c
    simp only [tab6Base, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  have hmem : pA * pZ ∈ {c : ↥P1408 | IsConj (pA * pZ) c} := IsConj.refl _
  rw [hset, Set.ncard_diff_singleton_of_mem hmem, hcl]

private theorem tab6_ord : orderOf pA = 2 ∧ orderOf pZ = 2 ∧ orderOf pB = 2 ∧ orderOf pZ₁ = 2 := by
  obtain ⟨hA, hZ, hB, hZ₁, -⟩ := twoHSBasic_spec
  exact ⟨(Subgroup.orderOf_coe pA).symm.trans hA, (Subgroup.orderOf_coe pZ).symm.trans hZ,
    (Subgroup.orderOf_coe pB).symm.trans hB, (Subgroup.orderOf_coe pZ₁).symm.trans hZ₁⟩

theorem tab6_card_stab (hP : Nat.card ↥P1408 = 177408000) (i : Fin 8) :
    Nat.card ↥(Gx (pA * pZ) ⊓ Gx (tab6C i)) = ![384, 1024, 48, 64, 32, 240, 20, 16] i := by
  have hK : Nat.card ↥(Gx (pA * pZ)) = 30720 := natCard_centralizer_pAZ hP
  refine stab_eq_of_le (Gx (pA * pZ)) (tab6Base pA pZ (pA * pZ)) (tab6Set pA pZ pB pZ₁ (pA * pZ))
    tab6C ![384, 1024, 48, 64, 32, 240, 20, 16]
    (by intro i x hx; fin_cases i <;> exact hx.1)
    (fun i j hij => tab6Set_disjoint pA_mem_center' tab6_ord (not_isConj_inv hP) i j hij)
    (by
      intro i k hk x hx
      have hky : k * (pA * pZ) * k⁻¹ = pA * pZ := by rw [← mem_Gx.mp hk]; group
      have := (mem_tab6Set_conj pA_mem_center' pZ pB pZ₁ (pA * pZ) x k i).mpr hx
      rwa [hky] at this)
    (tab6C_mem_set hP)
    (fun i => by
      have h := (tab6_facts hP).stab_le i
      rwa [wordP_wordAZ] at h)
    (by rw [hK]; intro i; fin_cases i <;> decide)
    (by rw [hK, tab6_base_ncard hP]; decide) i

private theorem tab6_card_stab' (hP : Nat.card ↥P1408 = 177408000) (i : Fin 8) :
    Nat.card ↥(Gx (wordP wordAZ) ⊓ Gx ((tab6Row i).rowP wordAZ)) =
      ![384, 1024, 48, 64, 32, 240, 20, 16] i := by
  rw [wordP_wordAZ]
  exact tab6_card_stab hP i

theorem tab6_shape_3A (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeD8TimesS3 ↥(Gx (pA * pZ) ⊓ Gx (tab6C 2)) := by
  have h := nonempty_mulEquiv_of_sub (tab6_facts hP).sub2 (tab6_facts hP).shape2
    (natCard_d8_sym3.trans (tab6_card_stab' hP 2).symm)
  rw [wordP_wordAZ] at h
  exact h

theorem tab6_shape_4B (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeTwoTwoTimesD8 ↥(Gx (pA * pZ) ⊓ Gx (tab6C 4)) := by
  have h := nonempty_mulEquiv_of_sub (tab6_facts hP).sub4 (tab6_facts hP).shape4
    (natCard_elem2_d8.trans (tab6_card_stab' hP 4).symm)
  rw [wordP_wordAZ] at h
  exact h

theorem tab6_shape_5E (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeZ2TimesD10 ↥(Gx (pA * pZ) ⊓ Gx (tab6C 6)) := by
  have h := nonempty_mulEquiv_of_sub (tab6_facts hP).sub6 (tab6_facts hP).shape6
    (natCard_z2_d10.trans (tab6_card_stab' hP 6).symm)
  rw [wordP_wordAZ] at h
  exact h

theorem tab6_shape_6A (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeZ2TimesD8 ↥(Gx (pA * pZ) ⊓ Gx (tab6C 7)) := by
  have h := nonempty_mulEquiv_of_sub (tab6_facts hP).sub7 (tab6_facts hP).shape7
    (natCard_z2_d8.trans (tab6_card_stab' hP 7).symm)
  rw [wordP_wordAZ] at h
  exact h

theorem tableVI_P (hP : Nat.card ↥P1408 = 177408000) : TableVIData pA pZ pB pZ₁ (pA * pZ) :=
  tableVI_of_reps pA_mem_center' tab6_ord (IsConj.refl (pA * pZ)) (not_isConj_inv hP)
    (natCard_centralizer_pAZ hP) (tab6_base_ncard hP) tab6C (tab6C_mem_set hP) (tab6_card_stab hP)
    (tab6_shape_3A hP) (tab6_shape_4B hP) (tab6_shape_5E hP) (tab6_shape_6A hP)

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
