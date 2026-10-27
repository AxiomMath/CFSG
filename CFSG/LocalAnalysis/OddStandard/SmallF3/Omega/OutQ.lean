module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inputs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQSolv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQTrans
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQData
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQBal
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG CFSG.GH74.GLS
open scoped MatrixGroups

theorem aor_two_element_of_mem_pCore {G : Type} [Group G] {K : Subgroup G} {q : G}
    (hq : q ∈ CFSG.inSubgroup (CFSG.pCore 2) K) : q ∈ K ∧ ∃ k : ℕ, q ^ (2 ^ k) = 1 := by
  simp only [CFSG.inSubgroup, Subgroup.mem_map] at hq
  obtain ⟨k, hk, hkq⟩ := hq
  rw [← hkq]
  refine ⟨k.2, ?_⟩
  have h2 : IsPGroup 2 (CFSG.pCore 2 ↥K) := aor_pCore_isPGroup 2
  obtain ⟨n, hn⟩ := h2.exists_pow_pow_eq_one (⟨k, hk⟩ : ↥(CFSG.pCore 2 ↥K))
  refine ⟨n, ?_⟩
  have hval : ((⟨k, hk⟩ : ↥(CFSG.pCore 2 ↥K)) : ↥K) ^ 2 ^ n = 1 := by
    simpa using congrArg (Subtype.val) hn
  have hval2 : (k : G) ^ 2 ^ n = 1 := by
    simpa using congrArg (Subtype.val) hval
  exact hval2

theorem aor_commutator_eq_bot_of_subgroupOf {G : Type} [Group G] {B Q I : Subgroup G}
    (hQB : Q ≤ B) (hIB : I ≤ B) {P : Subgroup ↥B} (hQP : Q.subgroupOf B ≤ P)
    (h : ⁅P, I.subgroupOf B⁆ = ⊥) : ⁅Q, I⁆ = ⊥ := by
  have hle : ⁅Q.subgroupOf B, I.subgroupOf B⁆ ≤ ⁅P, I.subgroupOf B⁆ :=
    Subgroup.commutator_mono hQP le_rfl
  have hbot : ⁅Q.subgroupOf B, I.subgroupOf B⁆ = ⊥ := by
    rw [h] at hle
    exact le_bot_iff.mp hle
  have hinf : ⁅Q, I ⊓ B⁆ = ⊥ :=
    CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hQB hbot
  rwa [inf_eq_left.mpr hIB] at hinf

theorem asc82Thm2Q_holds : Asc82Thm2Q := by
  intro G _ _ t L hS x X y K u I hD
  have hu : orderOf u = 2 := hD.involution_u
  have hx : orderOf x = 2 := hD.pocket.involution_x
  have hxu : x * u = u * x := aor_l34_comm hD
  let B : Subgroup G := centralizer ({u} : Set G)
  have hxB : x ∈ B := by
    have h' : x ∈ centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hxu.symm
    exact h'
  let s : ↥B := ⟨x, hxB⟩
  have hsval : (s : G) = x := rfl
  have hs : orderOf s = 2 := by
    change orderOf (⟨x, hxB⟩ : ↥B) = 2
    rw [Subgroup.orderOf_mk]
    exact hx
  have hKD : K ≤ centralizer ({x, u} : Set G) := aor_l34_le_centralizer_pair hD
  have hDB : centralizer ({x, u} : Set G) ≤ B :=
    Subgroup.centralizer_le (Set.subset_insert x {u})
  have hKB : K ≤ B := hKD.trans hDB
  let K' : Subgroup ↥B := K.subgroupOf B
  have hK'c : K' ≤ centralizer ({s} : Set ↥B) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    apply Subtype.ext
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hcomm : x * (k : G) = (k : G) * x :=
      (Subgroup.mem_centralizer_iff.mp (hKD hkK)) x (Set.mem_insert x {u})
    simpa only [Subgroup.coe_mul, hsval] using hcomm
  have hK's : (K'.subgroupOf (centralizer ({s} : Set ↥B))).IsSubnormal := by
    have hpair : (centralizer ({(s : G), u} : Set G)).subgroupOf B = centralizer ({s} : Set ↥B) :=
      aor_centralizer_pair_subgroupOf u s
    rw [← hpair]
    exact aor_subnormal_subgroupOf_subgroupOf hDB hKD (aor_l34_subnormal hD)
  have hχ : ∃ χ : ↥K' →* SL(2, ZMod 3), Function.Surjective χ ∧ Odd (Nat.card χ.ker) :=
    aor_exists_hom_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKB)
      (aor_exists_hom_of_isSL23Mod hD.pocket.pocket.2.2.2)
  have hbal := aor_balance_two_elements s hs K' hK'c hK's hχ
  let Q : Subgroup G := CFSG.inSubgroup (CFSG.pCore 2) K
  have hQK : Q ≤ K := by
    show CFSG.inSubgroup (CFSG.pCore 2) K ≤ K
    exact Subgroup.map_subtype_le (CFSG.pCore 2 ↥K)
  have hQB : Q ≤ B := hQK.trans hKB
  have hQ2 : ∀ q ∈ Q.subgroupOf B, q ∈ K' ∧ ∃ k : ℕ, q ^ (2 ^ k) = 1 := by
    intro q hq
    have hqG : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
    obtain ⟨hqK, k, hk⟩ := aor_two_element_of_mem_pCore hqG
    refine ⟨Subgroup.mem_subgroupOf.mpr hqK, k, ?_⟩
    apply Subtype.ext
    simpa using hk
  let I' : Subgroup ↥B := I.subgroupOf B
  have hI' : IsComponent I' := hD.component.2
  have hIB : I ≤ B := hD.component.1
  rcases hbal with h | ⟨J, hJp, _hJs, hJK⟩
  · left
    have hQsub : Q.subgroupOf B ≤ pPrimePCore 2 ↥B := by
      intro q hq
      exact h q (hQ2 q hq).1 (hQ2 q hq).2
    exact aor_commutator_eq_bot_of_subgroupOf hQB hIB hQsub
      (aor_commutator_pPrimePCore_eq_bot hI')
  · have hJc : IsComponent J := hS.a1 u hu J hJp
    have hQJ : Q.subgroupOf B ≤ J := by
      intro q hq
      exact hJK q (hQ2 q hq).1 (hQ2 q hq).2
    rcases CFSG.LocalCores.distinct_components_commute hJc hI' with hJI | hJI
    · right
      refine CFSG.LocalCores.le_of_subgroupOf_le hQB ?_
      rw [hJI] at hQJ
      exact hQJ
    · left
      exact aor_commutator_eq_bot_of_subgroupOf hQB hIB hQJ hJI

end CFSG.OddStandard.SmallF3.Omega
