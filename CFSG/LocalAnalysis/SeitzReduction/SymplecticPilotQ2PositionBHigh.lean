module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionB
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBFacts
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Rows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.E6Pilot (IsAutConjIn)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {K : Type} [Field K]

section OTwo

theorem isSimpleGroup_statedSp_two [CharP K 2] (hK : Nat.card K = 2) {m : ℕ} (hm : 3 ≤ m) :
    IsSimpleGroup (StatedSp m K) := by
  have : NeZero m := ⟨by omega⟩
  have : IsSimpleGroup (StatedProj (StatedSp m K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K m (by omega)
      (Or.inr (Or.inr ⟨hK, hm⟩))
  exact (MulEquiv.ofBijective _
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    ).isSimpleGroup_congr.2 this

theorem eq_bot_of_normal_of_isPGroup_of_orderOf_three {S : Type*} [Group S] [IsSimpleGroup S]
    {y : S} (hy : orderOf y = 3) (N : Subgroup S) (hN : N.Normal) (h2 : IsPGroup 2 N) :
    N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := N) with h | h
  · exact h
  · exfalso
    have hyN : y ∈ N := h ▸ mem_top y
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h2) ⟨y, hyN⟩
    rw [Subgroup.orderOf_mk, hy] at hk
    rcases k with _ | _ | k
    · simp at hk
    · simp at hk
    · have : 4 ≤ 2 ^ (k + 2) := by
        rw [pow_add]
        have := Nat.one_le_two_pow (n := k)
        omega
      omega

theorem eq_bot_of_normal_of_isPGroup_of_mulEquiv_two [CharP K 2] (hK : Nat.card K = 2) {m : ℕ}
    (hm : 3 ≤ m) {M : Type*} [Group M] (e : M ≃* StatedSp m K) (N : Subgroup M) (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N = ⊥ := by
  have : IsSimpleGroup (StatedSp m K) := isSimpleGroup_statedSp_two hK hm
  have : IsSimpleGroup M := e.isSimpleGroup_congr.2 this
  have hy : orderOf (e.symm (nsElt (K := K) (⟨0, by omega⟩ : Fin m))) = 3 := by
    rw [MulEquiv.orderOf_eq, orderOf_nsElt]
  exact eq_bot_of_normal_of_isPGroup_of_orderOf_three hy N hN h2

end OTwo

section Mixed

variable {n : ℕ}

theorem spCompl12_le_complSp_one : spCompl12 K n ≤ complSp K (1 : Fin (n + 3)) := by
  rw [spCompl12_eq_suppGroup]
  intro x hx
  exact isSupp_mono (fun t ht => ht.1) hx

theorem siegDiag_two_not_mem_spCompl12 :
    siegDiag K (2 : Fin (n + 3)) 1 ∉ spCompl12 K n := by
  rw [spCompl12_eq_suppGroup]
  intro h
  have h0 := h (Sum.inl 2) (Sum.inr 2) fun h' => h'.1.2 (inl_mem_coords 2)
  rw [mat_siegDiag, fromBlocks_apply₁₂, Matrix.one_apply_ne Sum.inl_ne_inr] at h0
  simp at h0

theorem card_spCoreLeviTwo_lt [Finite K] {κ : SpTwoCentral} (hκ : κ ≠ .b1) :
    Nat.card (spCoreLeviTwo K n κ) < Nat.card (complSp K (1 : Fin (n + 3))) := by
  have : Finite (StatedSp (n + 3) K) := by
    have : Finite (GL (Fin (n + 3) ⊕ Fin (n + 3)) K) := inferInstance
    exact Subtype.finite
  have h12 : (1 : Fin (n + 3)) ≠ 2 := one_ne_two_fin
  have hlt : spCompl12 K n < complSp K (1 : Fin (n + 3)) :=
    lt_of_le_of_ne spCompl12_le_complSp_one fun h => siegDiag_two_not_mem_spCompl12 (h ▸
      longRootSp2_le_complSp h12 (siegDiag_mem_longRootSp2 2 1))
  have hle : spCoreLeviTwo K n κ ≤ spCompl12 K n := by
    cases κ
    · exact absurd rfl hκ
    · exact Subgroup.commutator_le_self _
    · exact Subgroup.commutator_le_self _
  exact lt_of_le_of_lt (Subgroup.card_le_of_le hle) (Subgroup.card_lt_of_lt hlt)

theorem isEmpty_mulEquiv_complSp_spCoreLeviTwo [Finite K] {κ : SpTwoCentral} (hκ : κ ≠ .b1) :
    IsEmpty (complSp K (1 : Fin (n + 3)) ≃* spCoreLeviTwo K n κ) :=
  ⟨fun ι => (card_spCoreLeviTwo_lt hκ).ne (Nat.card_congr ι.toEquiv).symm⟩

theorem isEmpty_mulEquiv_spCoreLeviTwo_complSp [Finite K] {κ : SpTwoCentral} (hκ : κ ≠ .b1) :
    IsEmpty (spCoreLeviTwo K n κ ≃* complSp K (1 : Fin (n + 3))) :=
  ⟨fun ι => (card_spCoreLeviTwo_lt hκ).ne (Nat.card_congr ι.toEquiv)⟩

end Mixed

section High

variable {n : ℕ} [Finite K] [CharP K 2]

omit [Finite K] in
theorem forall_normal_isPGroup_complSp_one_two (hK : Nat.card K = 2) (hn : 1 ≤ n)
    (N : Subgroup (complSp K (1 : Fin (n + 3)))) (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ :=
  eq_bot_of_normal_of_isPGroup_of_mulEquiv_two hK (m := n + 2) (by omega)
    (complSpEquiv (K := K) (1 : Fin (n + 3))).symm N hN h2

omit [Finite K] [CharP K 2] in
theorem spCoreLeviTwo_a2_eq (hK : Nat.card K = 2) (hn : 2 ≤ n) :
    spCoreLeviTwo K n .a2 = spCompl12 K n :=
  commutator_spCompl12_two hK hn

theorem spTwoLemmaBFacts_of_two_le (hK : Nat.card K = 2) (hn : 2 ≤ n) : SpTwoLemmaBFacts K n := by
  have h10 : (1 : Fin (n + 3)) ≠ 0 := one_ne_zero_fin3
  have hS := spCoreLeviTwo_a2_eq hK hn
  have hJS : longRootSp2 K (n + 3) 0 ≤ spCoreLeviTwo K n .a2 := hS ▸ longRootSp2_le_spCompl12 n
  have hAS : IsAutConjIn (spCoreLeviTwo K n .a2) (longRootSp2 K (n + 3) 0) :=
    hS ▸ isAutConjIn_spCompl12_longRootSp2 n hn
  have hJ1 : longRootSp2 K (n + 3) 0 ≤ complSp K (1 : Fin (n + 3)) := longRootSp2_le_complSp h10
  have hA1 : IsAutConjIn (complSp K (1 : Fin (n + 3))) (longRootSp2 K (n + 3) 0) :=
    isAutConjIn_complSp_longRootSp2 (by omega)
  have hMS : ∀ N : Subgroup (spCoreLeviTwo K n .a2), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN h2
    exact eq_bot_of_normal_of_isPGroup_of_mulEquiv_two hK (m := n + 1) (by omega)
      ((MulEquiv.subgroupCongr hS).trans (spCompl12Equiv K n).symm) N hN h2
  refine ⟨fun κ => ?_, fun κ => ?_, fun κ => ?_, fun κ κ' β _ ι _ => ?_⟩
  · cases κ
    · exact perfectCore_centralizer_spRep_b1_two hK (by omega)
    · change _ = wRadical K (1 : Fin (n + 3)) 2 ⊔ spCoreLeviTwo K n .a2
      rw [hS, spRep_a2_eq]
      exact perfectCore_centralizer_twoCentralElt_two hK hn (Or.inl rfl)
    · change _ = wRadical K (1 : Fin (n + 3)) 2 ⊔ spCoreLeviTwo K n .a2
      rw [hS, spRep_c2_eq]
      exact perfectCore_centralizer_twoCentralElt_two hK hn (Or.inr rfl)
  · cases κ
    · exact forall_normal_isPGroup_complSp_one_two hK (by omega)
    · exact hMS
    · exact hMS
  · have hX : nsTorusSp K (0 : Fin (n + 3)) ≤ longRootSp2 K (n + 3) 0 := nsTorusSp_le_longRootSp2 0
    cases κ
    · exact hX.trans hJ1
    · exact hX.trans hJS
    · exact hX.trans hJS
  · cases κ <;> cases κ'
    · exact nonempty_perfectCore_centralizer_of_isAutConjIn hK (by omega) hA1 hJ1 ι
    · exact ((isEmpty_mulEquiv_complSp_spCoreLeviTwo (K := K) (n := n) (κ := .a2)
        SpTwoCentral.noConfusion).false ι).elim
    · exact ((isEmpty_mulEquiv_complSp_spCoreLeviTwo (K := K) (n := n) (κ := .c2)
        SpTwoCentral.noConfusion).false ι).elim
    · exact ((isEmpty_mulEquiv_spCoreLeviTwo_complSp (K := K) (n := n) (κ := .a2)
        SpTwoCentral.noConfusion).false ι).elim
    · exact nonempty_perfectCore_centralizer_of_isAutConjIn hK (by omega) hAS hJS ι
    · exact nonempty_perfectCore_centralizer_of_isAutConjIn hK (by omega) hAS hJS ι
    · exact ((isEmpty_mulEquiv_spCoreLeviTwo_complSp (K := K) (n := n) (κ := .c2)
        SpTwoCentral.noConfusion).false ι).elim
    · exact nonempty_perfectCore_centralizer_of_isAutConjIn hK (by omega) hAS hJS ι
    · exact nonempty_perfectCore_centralizer_of_isAutConjIn hK (by omega) hAS hJS ι

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_nsTorusSp_of_two_le (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    (hn : 2 ≤ n) (e : L ≃* StatedSp (n + 3) K) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) :
    ¬ (((modelToG e (complSp K (0 : Fin (n + 3)))).subgroupOf
        (centralizer (modelToG e (nsTorusSp K (0 : Fin (n + 3))) : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (nsTorusSp K (0 : Fin (n + 3))) : Set G))))).Normal :=
  not_normal_neighbour_nsTorusSp_of_facts hset hK (by omega) (spTwoLemmaBFacts_of_two_le hK hn) e
    ht htC

end High

@[expose] def SpEightTwoLemmaBFacts : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → SpTwoLemmaBFacts K 1

theorem spTwoPositionInput_of_eight (h8 : SpEightTwoLemmaBFacts) : SpTwoPositionInput := by
  intro G _ _ L hset n K _ _ _ hK hn e t ht htC
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm
  · exact not_normal_neighbour_nsTorusSp_of_facts hset hK le_rfl (h8 K hK) e ht htC
  · exact not_normal_neighbour_nsTorusSp_of_two_le hset hK hm e ht htC

end CFSG.SeitzReduction.SymplecticPilot
