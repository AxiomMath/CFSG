module

public import CFSG.CGT.PushingUpLit.K1R.SporBase
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicLarge

public section

namespace CFSG.CGT.PushingUpLit.K1R

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem co1_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Co1 := by
  have hSL := sl2_fails_card_quotient_center_mem (N := {251596800}) fun n hn h =>
    sl2Order_ne_of_check (B := 28) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  exact sporadicInner_of_comps (isoInvariant_card_quotient_center _) hSL (fun G _ _ ⟨e⟩ t ht B hB =>
    Set.mem_singleton_iff.2 (co1LocalComponentsInput_holds G e t ht B hB).1)

theorem co2_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Co2 :=
  sporadicInner_of_comps (Qi := fun _ _ => False) (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ ⟨e⟩ t ht B hB =>
      CFSG.Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e t ht B hB)

theorem co3_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Co3 := by
  have hSL := sl2_fails_card_quotient_center_mem (N := co3Orders) fun n hn h => by
    simp only [co3Orders, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact sl2Order_ne_of_check (B := 21) (by norm_num) (by decide) n hn h
    · exact sl2Order_ne_of_check (B := 17) (by norm_num) (by decide) n hn h
  exact sporadicInner_of_comps (isoInvariant_card_quotient_center _) hSL
    (fun _ _ _ ⟨e⟩ t ht => co3_inner_comps e t ht)

theorem fi22_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Fi22 := by
  have hSLi := sl2_fails_card_quotient_center_mem (N := {9196830720}) fun n hn h =>
    sl2Order_ne_of_check (B := 34) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  exact sporadicInner_of_comps (isoInvariant_card_quotient_center _) hSLi
    (fun _ _ _ ⟨e⟩ t ht B hB => Set.mem_singleton_iff.2
      (CFSG.Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order
        e t ht B hB))

theorem fi23_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Fi23 := by
  have hSL := sl2_fails_card_quotient_center_mem (N := {64561751654400, 9196830720})
    fun n hn h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · exact sl2Order_ne_of_check (B := 46) (by norm_num) (by decide) n hn h
      · exact sl2Order_ne_of_check (B := 34) (by norm_num) (by decide) n hn h
  exact sporadicInner_of_comps (isoInvariant_card_quotient_center _) hSL
    (fun _ _ _ ⟨e⟩ t ht => fi23_inner_comps e t ht)

open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven) in
theorem fi24prime_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Fi24Prime := by
  have hSLi := sl2_fails_card_quotient_center_mem (N := {64561751654400}) fun n hn h =>
    sl2Order_ne_of_check (B := 46) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  exact sporadicInner_of_comps (isoInvariant_card_quotient_center _) hSLi
    (fun _ _ _ ⟨e⟩ t ht B hB => Set.mem_singleton_iff.2
      (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
        e t ht B hB).1)

theorem hn_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .HN := by
  have hSLi := sl2_fails_card_quotient_center_mem (N := {44352000}) fun n hn h =>
    sl2Order_ne_of_check (B := 26) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  exact sporadicInner_of_comps (isoInvariant_card_quotient_center _) hSLi
    (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (hnLocalComponentsInput_holds G e t ht B hB))

theorem ly_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Ly := by
  have hSL := sl2_fails_card_quotient_center_mem (N := {19958400}) fun n hn h =>
    sl2Order_ne_of_check (B := 25) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  refine sporadicInner_of_comps (isoInvariant_card_quotient_center _) hSL (fun G _ _ hG t ht => ?_)
  obtain ⟨hq, -, ⟨eA⟩⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple hG t ht
  have hcard : Nat.card (centralizer ({t} : Set G) ⧸ center (centralizer ({t} : Set G))) =
      19958400 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    norm_num [Nat.factorial]
  exact compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400}) hcard

theorem th_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .Th :=
  sporadicInner_of_comps (Qi := fun _ _ => False) (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ h => h) (fun G _ _ hG t ht => compsSatisfy_of_charP
      ((CFSG.Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G
        hG).1 t ht).1 _)

theorem b_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .B := by
  have hSL := sl2_fails_card_quotient_center_mem
    (N := {76532479683774853939200, 3311126603366400}) fun n hn h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · exact sl2Order_ne_of_check (B := 77) (by norm_num) (by decide) n hn h
      · exact sl2Order_ne_of_check (B := 52) (by norm_num) (by decide) n hn h
  refine sporadicInner_of_comps (isoInvariant_card_quotient_center _) hSL
    (fun G _ _ ⟨e⟩ t ht K hK => ?_)
  obtain ⟨-, hiso, -⟩ :=
    CFSG.Monster.B.CTIB.involution_local_components_simple_quotient_divisible_by_seventeen ⟨e⟩ t
      ht K hK
  rcases hiso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · left
    rw [Nat.card_congr φ.toEquiv, CFSG.LieType.Chevalley.C2E6Std.card_stdGroup]
  · right
    obtain ⟨ψ⟩ := CFSG.Monster.B.E6.StdF4Radical.nonempty_groupJ_mulEquiv_F4
    rw [Set.mem_singleton_iff, Nat.card_congr φ.toEquiv, ← Nat.card_congr ψ.toEquiv,
      CFSG.Monster.B.E6.FieldInvF4.card_groupJ]

theorem m_innerKernel :
    InnerKernelSelector fun D _ => NativeSporadic.IsSporadic D .M := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ hD hs n hn K _ _ hK α hα hin S hSα hSn hSK _
  obtain ⟨t, ht, rfl, hcomp, -, -, hcard, hZ⟩ := innerRoot_setup hD hn hK hα hin hSα hSn hSK
  have hCt : (MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id D) = centralizer ({t} : Set D) :=
    Sporadic.eqLocus_conj t
  have hSt : S ≤ centralizer ({t} : Set D) := hCt ▸ hSα
  have h2 := CFSG.ComponentClassification.CatLeafProof.monsterLocalComponentsInput D hD hs t ht
    (S.subgroupOf (centralizer ({t} : Set D))) hcomp
  have hcardq : Nat.card ((S.subgroupOf (centralizer ({t} : Set D))) ⧸
      center (S.subgroupOf (centralizer ({t} : Set D)))) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [card_quotient_center_congr (Subgroup.subgroupOfEquivOfLe hSt), ← hcard]
    exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv
  rw [hcardq] at h2
  have hn1 : 1 ≤ n := by omega
  have h41 : n = 41 := by
    have := (two_pow_dvd_sl2Order_iff hn1).1 h2.1
    have := mt (two_pow_dvd_sl2Order_iff (a := 42) hn1).2 h2.2
    omega
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple hs.some
  have hD' : Nat.card D = CFSG.Open.monsterOrder := by
    rw [Nat.card_congr e.toEquiv, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
  have hdvd : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card D := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card S
  rw [hD', h41] at hdvd
  norm_num [CFSG.Open.monsterOrder] at hdvd

end CFSG.CGT.PushingUpLit.K1R
