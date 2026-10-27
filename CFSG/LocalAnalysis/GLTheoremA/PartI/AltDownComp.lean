module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.GLTheoremA.AltDown

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G]

theorem glaPComponent_commute_of_normal_isPGroup [Finite G] {p : ℕ} (hp : p.Prime)
    {X J N : Subgroup G} (hJ : GLAPComponent p X J) (hNX : N ≤ X)
    (hNn : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hNp : IsPGroup p N) :
    ∀ j ∈ J, ∀ n ∈ N, j * n = n * j := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hJX, hL⟩ :=
    (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).1 hJ
  have hPn : (N.subgroupOf X).Normal :=
    ⟨fun n hn g => hNn g g.2 n hn⟩
  have hP : IsPGroup p ↥(N.subgroupOf X) :=
    hNp.comap_of_injective X.subtype X.subtype_injective
  have h := CFSG.ComponentClassification.CatalogueBPrimeJoin.p_component_normal_p_centralizer
    hL hPn hP
  intro j hj n hn
  have hc : ⁅(⟨j, hJX hj⟩ : ↥X), (⟨n, hNX hn⟩ : ↥X)⁆ ∈ ⁅J.subgroupOf X, N.subgroupOf X⁆ :=
    Subgroup.commutator_mem_commutator hj hn
  rw [h, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.1 hc)

theorem eq_of_isSubnormal_of_isSimpleGroup {F I : Subgroup G} [IsSimpleGroup ↥F]
    (hsn : IsSubnormal I F) (hI : I ≠ ⊥) : I = F := by
  by_contra hne
  obtain ⟨M, hIM, hMF, hMne, hMn, -⟩ := isSubnormal_exists_normal hsn hne
  haveI := hMn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf F) with h | h
  · apply hI
    rw [eq_bot_iff]
    intro i hi
    have hiM : (⟨i, hMF (hIM hi)⟩ : ↥F) ∈ M.subgroupOf F := hIM hi
    rw [h, Subgroup.mem_bot] at hiM
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val hiM)
  · exact hMne (le_antisymm hMF (Subgroup.subgroupOf_eq_top.1 h))

variable [Finite G]

theorem not_coprime_card_of_glaPComponent {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : ¬ Nat.Coprime p (Nat.card J) := by
  intro hcop
  have hnt : Nontrivial (PQuot p J) :=
    isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hJ)
  have htop : GLAPPrimeCore p ↥J = ⊤ := by
    refine eq_top_iff.2 (le_sSup ⟨inferInstance, ?_⟩)
    rwa [Subgroup.card_top]
  have hss : Subsingleton (PQuot p J) := by
    unfold PQuot
    rw [QuotientGroup.subsingleton_iff]
    exact htop
  exact (not_subsingleton_iff_nontrivial.2 hnt) hss

theorem nontrivial_of_glaPComponent {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : Nontrivial ↥J := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply not_coprime_card_of_glaPComponent hp hJ
  rw [Nat.card_eq_one_iff_unique.2 ⟨h, ⟨1⟩⟩]
  exact Nat.coprime_one_right p

theorem nonempty_pSimple_equiv {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : Subgroup.center S = ⊥) (e : ↥J ≃* S) : Nonempty (PSimple p J ≃* S) := by
  haveI : IsSimpleGroup ↥J := e.isSimpleGroup
  have hnt : Nontrivial (PQuot p J) :=
    isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hJ)
  have hcore : GLAPPrimeCore p ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore p ↥J) with h | h
    · exact h
    · exfalso
      have hss : Subsingleton (PQuot p J) := by
        unfold PQuot
        rw [QuotientGroup.subsingleton_iff]
        exact h
      exact (not_subsingleton_iff_nontrivial.2 hnt) hss
  let e1 : PQuot p J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let e2 : PQuot p J ≃* S := e1.trans e
  exact ⟨(QuotientGroup.congr (Subgroup.center (PQuot p J)) (Subgroup.center S) e2
    (Subgroup.map_center_eq e2)).trans
    ((QuotientGroup.quotientMulEquivOfEq hS).trans QuotientGroup.quotientBot)⟩

theorem false_of_isPerfect_of_card_dvd_twentyFour {H : Type*} [Group H] [Finite H] [Nontrivial H]
    [Group.IsPerfect H] (h : Nat.card H ∣ 24) : False := by
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.1 (show Nat.card H ∣ 2 ^ 3 * 3 ^ 1 by simpa using h)
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz
  have hcard : Fintype.card H = 2 ^ i * 3 ^ j := by rw [← Nat.card_eq_fintype_card, ← hyz]
  exact Group.IsPerfect.not_isSolvable H
    (CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) hcard)

end CFSG.LocalAnalysis.GLTheoremA.AltDown
