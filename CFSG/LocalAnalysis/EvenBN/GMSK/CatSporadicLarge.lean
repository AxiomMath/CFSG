module

public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBase
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.YGroups.Y443.Tri.Finiteness
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseBabySchreier
public import CFSG.Monster.B.CTIB.ComponentsSeventeen

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem co1_fixedRootFree :
    SporadicFixedRootFree .Co1 := by
  have hSL := sl2_fails_card_quotient_center_mem (N := {251596800}) fun n hn h =>
    sl2Order_ne_of_check (B := 28) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hSL hSL (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (co1LocalComponentsInput_holds G e t ht B hB).1)
    (outer_comps_of_forall_inner (s := .Co1) (fun β => ?_) _)
  obtain ⟨g, hg⟩ := CFSG.Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
    CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner β
  exact ⟨g, hg.symm⟩

theorem co2_fixedRootFree :
    SporadicFixedRootFree .Co2 :=
  sporadicFixedRootFree_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ h => h) (fun _ _ _ ⟨e⟩ t ht B hB =>
      CFSG.Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e t ht B hB)
    (outer_comps_of_forall_inner (s := .Co2) (mem_inner_of_mulEquiv
      CFSG.Sporadic.Co2Cert.co2PermEquiv
      CFSG.Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner) _)

theorem co3_fixedRootFree :
    SporadicFixedRootFree .Co3 := by
  have hSL := sl2_fails_card_quotient_center_mem (N := co3Orders) fun n hn h => by
    simp only [co3Orders, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact sl2Order_ne_of_check (B := 21) (by norm_num) (by decide) n hn h
    · exact sl2Order_ne_of_check (B := 17) (by norm_num) (by decide) n hn h
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hSL hSL (fun G _ _ ⟨e⟩ t ht => co3_inner_comps e t ht)
    (outer_comps_of_forall_inner (s := .Co3) (fun β => ?_) _)
  obtain ⟨g, hg⟩ := CFSG.Sporadic.SmallOddCore.ctuc_co3_all_automorphisms_inner.{0}.2.1.1 β
  exact ⟨g, hg.symm⟩

theorem fi22_fixedRootFree :
    SporadicFixedRootFree .Fi22 := by
  have hSLi := sl2_fails_card_quotient_center_mem (N := {9196830720}) fun n hn h =>
    sl2Order_ne_of_check (B := 34) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  have hSLo := sl2_fails_card_quotient_center_mem (N := {174182400, 1451520}) fun n hn h => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact sl2Order_ne_of_check (B := 28) (by norm_num) (by decide) n hn h
    · exact sl2Order_ne_of_check (B := 21) (by norm_num) (by decide) n hn h
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hSLi hSLo (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2
        (CFSG.Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order
          e t ht B hB)) (fun G _ _ _ hG β hβ2 hβ B hB => ?_)
  rcases CFSG.Sporadic.FischerOddCore.fi22OuterComponentsInput_holds G hG β
      (mul_self_eq_one_of_orderOf_eq_two hβ2) hβ B hB with h | h <;> simp [h]

theorem fi23_fixedRootFree :
    SporadicFixedRootFree .Fi23 := by
  have hSL := sl2_fails_card_quotient_center_mem (N := {64561751654400, 9196830720})
    fun n hn h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · exact sl2Order_ne_of_check (B := 46) (by norm_num) (by decide) n hn h
      · exact sl2Order_ne_of_check (B := 34) (by norm_num) (by decide) n hn h
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hSL hSL (fun G _ _ ⟨e⟩ t ht => fi23_inner_comps e t ht)
    (outer_comps_of_forall_inner (s := .Fi23) (fun β => ?_) _)
  change β ∈ inner NativeSporadic.Fi23
  rw [CFSG.Sporadic.FischerOddCore.CTUC_Fi23_all_automorphisms_inner.1]
  trivial

open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven) in
theorem fi24prime_fixedRootFree :
    SporadicFixedRootFree .Fi24Prime := by
  have hSLi := sl2_fails_card_quotient_center_mem (N := {64561751654400}) fun n hn h =>
    sl2Order_ne_of_check (B := 46) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  have hSLo := sl2_fails_card_quotient_center_mem (N := {4089470473293004800, 9196830720})
    fun n hn h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · exact sl2Order_ne_of_check (B := 62) (by norm_num) (by decide) n hn h
      · exact sl2Order_ne_of_check (B := 34) (by norm_num) (by decide) n hn h
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hSLi hSLo (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2
        (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
          e t ht B hB).1) (fun G _ _ _ hG β hβ2 hβ B hB => ?_)
  rcases CFSG.Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds G hG β
      (mul_self_eq_one_of_orderOf_eq_two hβ2) hβ B hB with h | h <;> simp [h]

theorem hn_fixedRootFree :
    SporadicFixedRootFree .HN := by
  have hSLi := sl2_fails_card_quotient_center_mem (N := {44352000}) fun n hn h =>
    sl2Order_ne_of_check (B := 26) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  have hSLo := sl2_fails_card_quotient_center_mem (N := {1814400}) fun n hn h =>
    sl2Order_ne_of_check (B := 21) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hSLi hSLo (fun G _ _ ⟨e⟩ t ht B hB =>
      Set.mem_singleton_iff.2 (hnLocalComponentsInput_holds G e t ht B hB))
    (fun G _ _ _ ⟨e⟩ β hβ2 hβ => ?_)
  obtain ⟨eS⟩ := CFSG.Sporadic.HNOddCore.hn_outer_involution_fixSub e β hβ2 hβ
  exact CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center _) eS compsSatisfy_perm_ten

theorem ly_fixedRootFree :
    SporadicFixedRootFree .Ly := by
  have hSL := sl2_fails_card_quotient_center_mem (N := {19958400}) fun n hn h =>
    sl2Order_ne_of_check (B := 25) (by norm_num) (by decide) n hn (Set.mem_singleton_iff.1 h)
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hSL hSL (fun G _ _ hG t ht => ?_)
    (outer_comps_of_forall_inner (s := .Ly) (fun β => ?_) _)
  · obtain ⟨hq, -, ⟨eA⟩⟩ := CFSG.Sporadic.LySchreier.involution_centralizers_quasisimple hG t ht
    have hcard : Nat.card (centralizer ({t} : Set G) ⧸ center (centralizer ({t} : Set G))) =
        19958400 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    exact compsSatisfy_of_isQuasisimple hq (isoInvariant_card_quotient_center {19958400}) hcard
  · change β ∈ inner NativeSporadic.Ly
    rw [lyOuterTrivialInput]
    trivial

theorem th_fixedRootFree :
    SporadicFixedRootFree .Th :=
  sporadicFixedRootFree_of_comps (Qi := fun _ _ => False) (Qo := fun _ _ => False)
    (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h)
    (fun _ _ _ _ _ _ h => h) (fun G _ _ hG t ht => compsSatisfy_of_charP
      ((CFSG.Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G
        hG).1 t ht).1 _)
    (outer_comps_of_forall_inner (s := .Th) (fun β => by
      have h : inner (NativeSporadic.Carrier .Th) = ⊤ := CFSG.Sporadic.ThSchreier.inner_Th
      rw [h]
      trivial) _)

theorem b_fixedRootFree :
    SporadicFixedRootFree .B := by
  have hSL := sl2_fails_card_quotient_center_mem
    (N := {76532479683774853939200, 3311126603366400}) fun n hn h => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with h | h
      · exact sl2Order_ne_of_check (B := 77) (by norm_num) (by decide) n hn h
      · exact sl2Order_ne_of_check (B := 52) (by norm_num) (by decide) n hn h
  refine sporadicFixedRootFree_of_comps (isoInvariant_card_quotient_center _)
    (isoInvariant_card_quotient_center _) hSL hSL (fun G _ _ ⟨e⟩ t ht K hK => ?_)
    (outer_comps_of_forall_inner (s := .B) ?_ _)
  swap
  · have hB : ∀ β : MulAut (NativeSporadic.Carrier .B), β ∈ inner (NativeSporadic.Carrier .B) :=
      CFSG.ComponentClassification.BMCase.inner_of_mulEquiv_pinnedB NativeSporadic.B
        ⟨MulEquiv.refl NativeSporadic.B⟩
    exact hB
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

theorem two_pow_dvd_sl2Order_iff {n a : ℕ} (hn : 1 ≤ n) :
    2 ^ a ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) ↔ a ≤ n := by
  have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by
      have : 2 ≤ 2 ^ n :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      nlinarith
    have he : Even ((2 ^ n) ^ 2) := by
      rw [← pow_mul]
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
    obtain ⟨k, hk⟩ := he
    exact ⟨k - 1, by omega⟩
  have hcop : Nat.Coprime (2 ^ a) ((2 ^ n) ^ 2 - 1) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hodd)
  rw [hcop.dvd_mul_right, Nat.pow_dvd_pow_iff_le_right (by norm_num)]

theorem m_fixedRootFree
    :
    SporadicFixedRootFree .M := by
  intro D _ _ hD hs n α S h
  have hα : α ∈ inner D := CFSG.ComponentClassification.CatLeafProof.monsterInnerInput D hD hs α
  obtain ⟨t, ht, hαt⟩ :=
    exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD) h.2.1 hα
  have hcomp := h.isComponent
  have hCt : α.toMonoidHom.eqLocus (MonoidHom.id D) = centralizer ({t} : Set D) := by
    rw [← hαt]
    exact eqLocus_conj t
  set C := α.toMonoidHom.eqLocus (MonoidHom.id D)
  have h2 := CFSG.ComponentClassification.CatLeafProof.monsterLocalComponentsInput D hD hs t ht
    ((S.subgroupOf C).map (MulEquiv.subgroupCongr hCt).toMonoidHom)
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulEquiv.subgroupCongr hCt) hcomp)
  have hcardq : Nat.card (((S.subgroupOf C).map (MulEquiv.subgroupCongr hCt).toMonoidHom) ⧸
      center ((S.subgroupOf C).map (MulEquiv.subgroupCongr hCt).toMonoidHom)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [card_quotient_center_congr
      (((S.subgroupOf C).equivMapOfInjective _ (MulEquiv.subgroupCongr hCt).injective).symm.trans
        (Subgroup.subgroupOfEquivOfLe h.2.2.1))]
    exact h.card_quotient_center
  rw [hcardq] at h2
  have hn1 : 1 ≤ n := by have := h.1; omega
  have h41 : n = 41 := by
    have := (two_pow_dvd_sl2Order_iff hn1).1 h2.1
    have := mt (two_pow_dvd_sl2Order_iff (a := 42) hn1).2 h2.2
    omega
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple hs.some
  have hD' : Nat.card D = CFSG.Open.monsterOrder := by
    rw [Nat.card_congr e.toEquiv, CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder]
  have hdvd := h.sl2Order_dvd_card
  rw [hD', h41] at hdvd
  norm_num [CFSG.Open.monsterOrder] at hdvd

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
