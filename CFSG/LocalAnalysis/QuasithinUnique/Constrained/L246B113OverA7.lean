module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverLift
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeEmbedding

public section

namespace CFSG.QuasithinUnique.Bridge.Over

namespace A7

open scoped commutatorElement
open Equiv CFSG.QuasithinUnique.Unc25K1.Six CFSG.Assembly.LowTwoRank
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.A312L.Seven CFSG.QuasithinUnique.Unc25G2.A312Sub

@[expose] def Concl {X : Type} [Group X] (B : Subgroup X) : Prop :=
  IsAlt 5 ↥B ∨ IsPSL 3 2 1 ↥B ∨ IsAlt 6 ↥B

theorem Concl.of_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {B : Subgroup X}
    (h : Concl (B.map e.toMonoidHom)) : Concl B := by
  rcases h with h | h | h
  · obtain ⟨f⟩ : Nonempty (↥(B.map e.toMonoidHom) ≃* alternatingGroup (Fin 5)) := h
    exact Or.inl ⟨(mapEquiv e B).symm.trans f⟩
  · exact Or.inr (Or.inl (IsPSL.of_mulEquiv (mapEquiv e B) h))
  · obtain ⟨f⟩ : Nonempty (↥(B.map e.toMonoidHom) ≃* alternatingGroup (Fin 6)) := h
    exact Or.inr (Or.inr ⟨(mapEquiv e B).symm.trans f⟩)

theorem isPSL_of_case_L3 {B : Subgroup ↥A7s} (hB : B ∈ lFamily T7)
    (eM : ↥(B ⊔ T7) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : IsPSL 3 2 1 ↥B := by
  have := slThree_isSimple
  have hperfM : ⁅B ⊔ T7, B ⊔ T7⁆ = B ⊔ T7 := perfect_of_equiv_simple slThree_nonabelian eM
  have hpc : perfectCore (B ⊔ T7) = B ⊔ T7 := perfectCore_eq_self_of_perfect hperfM
  obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB slThree_nonabelian
    ((MulEquiv.subgroupCongr hpc).trans eM)
  exact isPSL_three_two eB

theorem isAlt_six_of_case_A6 {B : Subgroup ↥A7s} (hB : B ∈ lFamily T7)
    (eM : ↥(B ⊔ T7) ≃* alternatingGroup (Fin 6)) : IsAlt 6 ↥B := by
  have := alt6_simple
  have hperfM : ⁅B ⊔ T7, B ⊔ T7⁆ = B ⊔ T7 := perfect_of_equiv_simple alt6_nonabelian eM
  have hpc : perfectCore (B ⊔ T7) = B ⊔ T7 := perfectCore_eq_self_of_perfect hperfM
  obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB alt6_nonabelian
    ((MulEquiv.subgroupCongr hpc).trans eM)
  exact ⟨eB⟩

theorem concl_of_lFamily
    (hq : CFSG.IsQuasisimple ↥A7s) {B : Subgroup ↥A7s}
    (hB : B ∈ lFamily T7) (hBtop : B ≠ ⊤) : Concl B := by
  have hB' : B ∈ cComp (B ⊔ T7) := hB
  have hMne : B ⊔ T7 ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hMns : ¬ Group.IsSolvable ↥(B ⊔ T7) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ T7))
        (Subgroup.inclusion_injective _))
  obtain ⟨i, hi, hMi⟩ := overgroup_Z (le_sup_right : T7 ≤ B ⊔ T7)
  have hcardM : Nat.card ↥(B ⊔ T7) =
      [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520].getD i 0 := by
    rw [← card_map_subtype, hMi]
    exact card_Z hi
  interval_cases i
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 0) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 1) (by rw [hcardM]; decide)) hMns
  · exact absurd (isSolvable_of_card_two_three (a := 3) (b := 2) (by rw [hcardM]; decide)) hMns
  ·
    have := alt5_simple
    have hle : rng5 ≤ B ⊔ T7 := by
      intro k hk
      obtain ⟨h4, h5⟩ := (mem_rng5 k).mp hk
      exact (mem_of_map_eq hMi k).mpr
        ((mem_Z7 (Equiv.Perm.mem_alternatingGroup.mp k.2)).mpr ⟨Or.inl h4, Or.inr h5⟩)
    have hperf5 : ⁅rng5, rng5⁆ = rng5 := perfect_of_equiv_simple alt5_nonabelian rng5Equiv
    have hpc : perfectCore (B ⊔ T7) = rng5 :=
      le_antisymm ((perfectCore_le_commutator (B ⊔ T7)).trans (commutator_le_rng5 hMi))
        (le_perfectCore_of_perfect hle hperf5)
    obtain ⟨eB⟩ := lFamily_equiv_of_perfectCore_equiv hB alt5_nonabelian
      ((MulEquiv.subgroupCongr hpc).trans rng5Equiv)
    exact Or.inl ⟨eB⟩
  ·
    exact Or.inr (Or.inl (isPSL_of_case_L3 hB
      (((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMi).trans z8Equiv.symm))))
  ·
    exact Or.inr (Or.inl (isPSL_of_case_L3 hB
      (((B ⊔ T7).equivMapOfInjective A7s.subtype A7s.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMi).trans z9Equiv.symm))))
  ·
    exact Or.inr (Or.inr (isAlt_six_of_case_A6 hB
      ((MulEquiv.subgroupCongr (eq_rng6 hMi)).trans rng6Equiv)))
  · exfalso
    apply hMne
    apply Subgroup.eq_top_of_card_eq
    rw [hcardM, card_A7s]
    decide

theorem isQuasisimple_alt7 : CFSG.IsQuasisimple ↥A7s := by
  have := Bridge.alt_isSimple (m := 7) (by norm_num)
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (Bridge.alt_exists_noncomm (m := 7) (by norm_num))).1

theorem over_alt7 :
    Over ↥A7s (fun B => Concl B) :=
  Over.of_sylow (fun e _ h => Concl.of_map e h) T7 isSylowTwoOf_T7 fun _ hB hBtop =>
    concl_of_lFamily isQuasisimple_alt7 hB hBtop

theorem over_of_equiv
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* alternatingGroup (Fin 7)) :
    Over Y (fun B => Concl B) :=
  Over.of_mulEquiv e (fun _ h => Concl.of_map e h) over_alt7

theorem isAlt_three_of_card_three {K : Type} [Group K] (h : Nat.card K = 3) : IsAlt 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hA : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have : IsCyclic K := isCyclic_of_prime_card h
  have : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hA
  exact ⟨mulEquivOfCyclicCardEq (by rw [h, hA])⟩

theorem concl_of_alt7
    {Ω : Type} [Group Ω] [Finite Ω] {L T X K : Subgroup Ω}
    (e : ↥L ≃* alternatingGroup (Fin 7)) (hT : IsSylowTwoOf T L) (hTX : T ≤ X) (hXL : X ≤ L)
    (hXne : X ≠ L) (hKX : K ≤ X) (hsub : IsSubnormal K X)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) :
    (∃ n, n ≤ 7 ∧ IsAlt n ↥K) ∨ IsPSL 3 2 1 ↥K := by
  rcases hK with hq | h3
  · obtain ⟨hT', hTX', hXne', hKX', hsub'⟩ := lift_to_subgroup hT hTX hXL hXne hKX hsub
    have hKL : K ≤ L := hKX.trans hXL
    have hq' : CFSG.IsQuasisimple ↥(K.subgroupOf L) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKL).symm hq
    have hKT : IsSubnormal (K.subgroupOf L) (K.subgroupOf L ⊔ T.subgroupOf L) :=
      A3.subnormal_of_le_of_le hsub' le_sup_left (sup_le hKX' hTX')
    have hcomp : IsComponentIn (K.subgroupOf L) (K.subgroupOf L ⊔ T.subgroupOf L) :=
      ⟨le_sup_left, CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_left :
          K.subgroupOf L ≤ K.subgroupOf L ⊔ T.subgroupOf L)).symm hq',
        (isSubnormal_iff_subgroupOf le_sup_left).1 hKT⟩
    have hlf : K.subgroupOf L ∈ lFamily (T.subgroupOf L) :=
      Vol2Native.mem_cComp_of_isComponentIn hcomp
    have hne : K.subgroupOf L ≠ ⊤ := fun h => hXne' (top_le_iff.1 (h ▸ hKX'))
    have hc : Concl (K.subgroupOf L) := over_of_equiv e _ hT' _ hlf hne
    let eK := Subgroup.subgroupOfEquivOfLe hKL
    rcases hc with h | h | h
    · obtain ⟨f⟩ : Nonempty (↥(K.subgroupOf L) ≃* alternatingGroup (Fin 5)) := h
      exact Or.inl ⟨5, by norm_num, ⟨eK.symm.trans f⟩⟩
    · exact Or.inr (IsPSL.of_mulEquiv eK h)
    · obtain ⟨f⟩ : Nonempty (↥(K.subgroupOf L) ≃* alternatingGroup (Fin 6)) := h
      exact Or.inl ⟨6, by norm_num, ⟨eK.symm.trans f⟩⟩
  · exact Or.inl ⟨3, by norm_num, isAlt_three_of_card_three h3⟩

end A7

end CFSG.QuasithinUnique.Bridge.Over
