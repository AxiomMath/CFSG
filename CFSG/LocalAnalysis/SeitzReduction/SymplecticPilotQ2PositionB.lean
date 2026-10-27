module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBSkeleton
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Fusion
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Neighbour
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCoresModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.LocalAnalysis.ComponentInitial CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.SeitzReduction.E6Pilot (IsAutConjIn)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

variable {K : Type} [Field K] {n : ℕ}

section Data

variable (K n) in
@[expose] def spCoreRadicalTwo : SpTwoCentral → Subgroup (StatedSp (n + 3) K)
  | .b1 => transvRadical K (1 : Fin (n + 3))
  | .a2 => wRadical K (1 : Fin (n + 3)) 2
  | .c2 => wRadical K (1 : Fin (n + 3)) 2

variable (K n) in
@[expose] noncomputable def spCoreLeviTwo : SpTwoCentral → Subgroup (StatedSp (n + 3) K)
  | .b1 => complSp K (1 : Fin (n + 3))
  | .a2 => ⁅spCompl12 K n, spCompl12 K n⁆
  | .c2 => ⁅spCompl12 K n, spCompl12 K n⁆

theorem isPGroup_spCoreRadicalTwo [CharP K 2] (κ : SpTwoCentral) :
    IsPGroup 2 (spCoreRadicalTwo K n κ) := by
  cases κ
  · exact isPGroup_transvRadical
  · exact isPGroup_wRadical one_ne_two_fin
  · exact isPGroup_wRadical one_ne_two_fin

theorem commutator_spCompl12_le_range_leviHom :
    ⁅spCompl12 K n, spCompl12 K n⁆ ≤
      (leviHom (one_ne_two_fin (n := n)) 1 (one_ne_zero (α := K))).range :=
  (Subgroup.commutator_le_self _).trans (spCompl12_le_range_leviHom one_ne_zero)

theorem spCoreLeviTwo_le_normalizer [CharP K 2] (κ : SpTwoCentral) :
    spCoreLeviTwo K n κ ≤ normalizer (spCoreRadicalTwo K n κ : Set (StatedSp (n + 3) K)) := by
  cases κ
  · exact complSp_le_normalizer_transvRadical
  · exact commutator_spCompl12_le_range_leviHom.trans
      (range_leviHom_le_normalizer_wRadical one_ne_two_fin one_ne_zero)
  · exact commutator_spCompl12_le_range_leviHom.trans
      (range_leviHom_le_normalizer_wRadical one_ne_two_fin one_ne_zero)

theorem disjoint_spCoreRadicalTwo_spCoreLeviTwo [CharP K 2] (κ : SpTwoCentral) :
    Disjoint (spCoreRadicalTwo K n κ) (spCoreLeviTwo K n κ) := by
  cases κ
  · exact disjoint_transvRadical_complSp
  · exact (disjoint_wRadical_range_leviHom one_ne_two_fin one_ne_zero).mono_right
      commutator_spCompl12_le_range_leviHom
  · exact (disjoint_wRadical_range_leviHom one_ne_two_fin one_ne_zero).mono_right
      commutator_spCompl12_le_range_leviHom

theorem siegDiag_mem_transvRadical {m : ℕ} (p : Fin m) (c : K) :
    siegDiag K p c ∈ transvRadical K p := by
  refine ⟨fun r => ?_, fun t ht r hr => ?_⟩
  · rw [mat_siegDiag]
    rcases r with x | x <;> simp [Matrix.one_apply]
  · rw [mat_siegDiag]
    rcases r with x | x <;> rcases t with y | y
    · simp [Matrix.one_apply]
    · have hy : y ≠ p := fun h => ht (h ▸ inr_mem_coords p)
      simp [Ne.symm hy]
    · simp
    · simp [Matrix.one_apply]

theorem spRep_mem_spCoreRadicalTwo (κ : SpTwoCentral) :
    spRep (K := K) n κ ∈ spCoreRadicalTwo K n κ := by
  cases κ
  · rw [spRep_b1_eq_siegDiag]
    exact siegDiag_mem_transvRadical 1 1
  · exact twoCentralElt_mem_wRadical 0 1
  · exact twoCentralElt_mem_wRadical 1 1

end Data

section FromFacts

variable (K n) in
@[expose] def SpTwoLemmaBFacts [CharP K 2] : Prop :=
  (∀ κ : SpTwoCentral, perfectCore (centralizer ({spRep n κ} : Set (StatedSp (n + 3) K))) =
      spCoreRadicalTwo K n κ ⊔ spCoreLeviTwo K n κ) ∧
    (∀ κ : SpTwoCentral, ∀ N : Subgroup (spCoreLeviTwo K n κ), N.Normal → IsPGroup 2 N →
      N = ⊥) ∧
    (∀ κ : SpTwoCentral, nsTorusSp K (0 : Fin (n + 3)) ≤ spCoreLeviTwo K n κ) ∧
    ∀ (κ κ' : SpTwoCentral)
      (β : (spCoreRadicalTwo K n κ ⊔ spCoreLeviTwo K n κ : Subgroup (StatedSp (n + 3) K)) ≃*
        (spCoreRadicalTwo K n κ' ⊔ spCoreLeviTwo K n κ' : Subgroup (StatedSp (n + 3) K))),
      (∀ y : (spCoreRadicalTwo K n κ ⊔ spCoreLeviTwo K n κ : Subgroup (StatedSp (n + 3) K)),
        ((β y : StatedSp (n + 3) K) ∈ spCoreRadicalTwo K n κ' ↔
          (y : StatedSp (n + 3) K) ∈ spCoreRadicalTwo K n κ)) →
      ∀ ι : spCoreLeviTwo K n κ ≃* spCoreLeviTwo K n κ',
      (∀ m : spCoreLeviTwo K n κ, ((ι m : StatedSp (n + 3) K))⁻¹ *
        (β (inclusion le_sup_right m) : StatedSp (n + 3) K) ∈ spCoreRadicalTwo K n κ') →
      Nonempty (perfectCore (centralizer
        (((((nsTorusSp K (0 : Fin (n + 3))).subgroupOf (spCoreLeviTwo K n κ)).map
          ι.toMonoidHom).map (spCoreLeviTwo K n κ').subtype : Subgroup (StatedSp (n + 3) K)) :
            Set (StatedSp (n + 3) K))) ≃* complSp K (0 : Fin (n + 3)))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem not_normal_neighbour_nsTorusSp_of_facts [Finite K] [CharP K 2] (hset : SeitzSetting G L)
    (hK : Nat.card K = 2) (hn : 1 ≤ n) (hF : SpTwoLemmaBFacts K n)
    (e : L ≃* StatedSp (n + 3) K) {t : G} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) :
    ¬ (((modelToG e (complSp K (0 : Fin (n + 3)))).subgroupOf
        (centralizer (modelToG e (nsTorusSp K (0 : Fin (n + 3))) : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (nsTorusSp K (0 : Fin (n + 3))) : Set G))))).Normal := by
  obtain ⟨hF3, hM, hJ, hF56⟩ := hF
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have hKt := inf_centralizer_eq_zpowers_of_mulEquiv hset hK1 (by omega) e htC ht
  have hrep : ∀ κ : SpTwoCentral, spRep (K := K) n κ ∈
      perfectCore (centralizer ({spRep n κ} : Set (StatedSp (n + 3) K))) := fun κ => by
    rw [hF3 κ]
    exact mem_sup_left (spRep_mem_spCoreRadicalTwo κ)
  obtain ⟨x, z, ⟨hzL, hzLx⟩, hxt, hz1, hzU, hzU', hact⟩ :=
    exists_conj_eq_mul_twoCentral_twoSided_of_rep hset hrep e ht hKt
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by omega) e)
  obtain ⟨-, htX, -, -, hXodd, -, hDXt, hDq, -, hZD, hOutD⟩ :=
    neighbour_data_nsTorusSp (n := n + 2) hK (by omega) e 0 htC (X := modelToG e
      (nsTorusSp K (0 : Fin (n + 3)))) rfl (D := modelToG e (complSp K (0 : Fin (n + 3)))) rfl
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_nsTorusSp (n := n + 2)
    hset.standardSetting.standard htC ht hKt hK (by omega) e 0 rfl htX rfl
  exact not_normal_map_oddCore_of_twoSided_compat hset.standardSetting hOut e htC ht hzL hzLx
    hxt hz1 hzU hzU' hact (spRep n) (fun U w hw hw1 => exists_conj_eq_spRep hw1 hw)
    (spCoreRadicalTwo K n) (spCoreLeviTwo K n) hF3 isPGroup_spCoreRadicalTwo
    spCoreLeviTwo_le_normalizer disjoint_spCoreRadicalTwo_spCoreLeviTwo hM hJ
    (spRep_mem_complSp n) hF56 hXodd le_rfl htX (hDXt.trans inf_le_left) hDq hZD hOutD hsyl

end FromFacts

end CFSG.SeitzReduction.SymplecticPilot
