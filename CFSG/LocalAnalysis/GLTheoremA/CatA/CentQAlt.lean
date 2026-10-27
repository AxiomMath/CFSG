module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQLift
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.GLTheoremA.AltDown
open scoped commutatorElement

theorem cq_commute_coe {α : Type*} [Fintype α] [DecidableEq α] {g h : alternatingGroup α}
    (hgh : Commute g h) : Commute (g : Equiv.Perm α) (h : Equiv.Perm α) :=
  congrArg Subtype.val hgh.eq

theorem false_of_perfect_card_dvd {P : Type*} [Group P] [Finite P] [Nontrivial P]
    [Group.IsPerfect P] {N : ℕ} (hN : N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 18 ∨ N = 30 ∨ N = 36)
    (h : Nat.card P ∣ N) : False := by
  have hsolv : Group.IsSolvable P := by
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl
    · have : IsZGroup P := IsZGroup.of_squarefree
        (Squarefree.squarefree_of_dvd h (by decide +kernel))
      infer_instance
    · have : IsZGroup P := IsZGroup.of_squarefree
        (Squarefree.squarefree_of_dvd h (by decide +kernel))
      infer_instance
    · have : IsZGroup P := IsZGroup.of_squarefree
        (Squarefree.squarefree_of_dvd h (by decide +kernel))
      infer_instance
    · haveI : Fintype P := Fintype.ofFinite P
      obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.1 (show Nat.card P ∣ 2 ^ 1 * 3 ^ 2 by simpa using h)
      obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hyz])
    · have : IsZGroup P := IsZGroup.of_squarefree
        (Squarefree.squarefree_of_dvd h (by decide +kernel))
      infer_instance
    · haveI : Fintype P := Fintype.ofFinite P
      obtain ⟨y, z, hy, hz, hyz⟩ := Nat.dvd_mul.1 (show Nat.card P ∣ 2 ^ 2 * 3 ^ 2 by simpa using h)
      obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hy
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hz
      exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
        Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hyz])
  exact Group.IsPerfect.not_isSolvable P hsolv

theorem cq_cycleType_of_prime_order {n : ℕ} (σ : Equiv.Perm (Fin n)) {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) : ∃ k : ℕ, σ.cycleType = Multiset.replicate k p ∧ k * p ≤ n := by
  have hall : ∀ c ∈ σ.cycleType, c = p := fun c hc => by
    have h1 : c ∣ p := by
      have h := Multiset.dvd_lcm hc
      rwa [Equiv.Perm.lcm_cycleType, hσ] at h
    rcases (Nat.dvd_prime hp).1 h1 with h | h
    · have := Equiv.Perm.two_le_of_mem_cycleType hc
      omega
    · exact h
  obtain ⟨k, hk⟩ : ∃ k, σ.cycleType = Multiset.replicate k p :=
    ⟨σ.cycleType.card, Multiset.eq_replicate.2 ⟨rfl, hall⟩⟩
  refine ⟨k, hk, ?_⟩
  have hsum := Equiv.Perm.sum_cycleType_le σ
  rw [hk, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

theorem cq_card_centralizer_dvd_alt {n : ℕ} (t : alternatingGroup (Fin n)) :
    Nat.card (Subgroup.centralizer {t}) ∣
      Nat.card (Subgroup.centralizer {((t : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))}) := by
  rw [← Subgroup.card_map_of_injective (f := (alternatingGroup (Fin n)).subtype)
    (fun a b h => Subtype.ext h)]
  apply Subgroup.card_dvd_of_le
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := congrArg (fun y : alternatingGroup (Fin n) => (y : Equiv.Perm (Fin n))) hx'
  simpa using h

theorem cq_card_centralizer_replicate {n q k : ℕ} (σ : Equiv.Perm (Fin n)) (hk1 : 1 ≤ k)
    (hk : σ.cycleType = Multiset.replicate k q) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) =
      (n - k * q).factorial * q ^ k * k.factorial := by
  have hne : k ≠ 0 := by omega
  rw [Equiv.Perm.nat_card_centralizer, hk, Fintype.card_fin, Multiset.sum_replicate,
    Multiset.prod_replicate, smul_eq_mul, Multiset.toFinset_replicate, if_neg hne,
    Finset.prod_singleton, Multiset.count_replicate_self]

theorem centCompQuasi_alt_eight_three_cycle {x : alternatingGroup (Fin 8)}
    (hσ : (x : Equiv.Perm (Fin 8)).cycleType = {3}) (r : ℕ) (hr : r.Prime) :
    CentCompQuasi (alternatingGroup (Fin 8)) x r := by
  intro J hJ
  set σ : Equiv.Perm (Fin 8) := (x : Equiv.Perm (Fin 8)) with hσdef
  have hcyc : σ.IsCycle := Equiv.Perm.card_cycleType_eq_one.1 (by rw [hσ]; rfl)
  have hfac : σ.cycleFactorsFinset = {σ} := hcyc.cycleFactorsFinset_eq_singleton
  have hJC : J ≤ Subgroup.centralizer {x} := hJ.1
  have hcomm : ∀ a ∈ J, Commute (a : Equiv.Perm (Fin 8)) σ := fun a ha =>
    cq_commute_coe (Subgroup.mem_centralizer_singleton_iff.1 (hJC ha))
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJF : J ≤ (alternatingGroup.ofSubtype σ.supportᶜ).range := by
    calc J = ⁅J, J⁆ := hJperf.symm
      _ ≤ _ := by
        refine Subgroup.commutator_le.2 fun a ha b hb => ?_
        rw [mem_range_ofSubtype_compl_iff]
        intro u hu
        have h := commutator_apply_of_mem_support (hcomm a ha) (hcomm b hb)
          (fun c hc => by rw [hfac, Finset.mem_singleton] at hc; rw [hc]; exact hcomm a ha)
          (fun c hc => by rw [hfac, Finset.mem_singleton] at hc; rw [hc]; exact hcomm b hb) hu
        simpa [commutatorElement_def] using h
  have hFC : (alternatingGroup.ofSubtype σ.supportᶜ).range ≤ Subgroup.centralizer {x} :=
    fun k hk => Subgroup.mem_centralizer_singleton_iff.2
      (Subtype.ext (commute_of_mem_range_ofSubtype_compl hk).eq)
  have hcard5 : (σ.supportᶜ).card = 5 := by
    have h1 : σ.support.card = 3 := by rw [← Equiv.Perm.sum_cycleType, hσ]; rfl
    rw [Finset.card_compl, h1]
    simp
  obtain ⟨e⟩ := nonempty_range_ofSubtype_equiv σ.supportᶜ 5 hcard5
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI : IsSimpleGroup ↥(alternatingGroup.ofSubtype σ.supportᶜ).range := e.isSimpleGroup
  have hJeq : J = (alternatingGroup.ofSubtype σ.supportᶜ).range :=
    eq_of_isSubnormal_of_isSimpleGroup (glaPComponent_of_le hr hJ hJF hFC).2.1
      (cq_glaPComponent_ne_bot hJ)
  subst hJeq
  haveI : Nontrivial ↥(alternatingGroup.ofSubtype σ.supportᶜ).range :=
    (Subgroup.nontrivial_iff_ne_bot _).2 (cq_glaPComponent_ne_bot hJ)
  haveI : Group.IsPerfect ↥(alternatingGroup.ofSubtype σ.supportᶜ).range :=
    Subgroup.isPerfect_iff.2 hJperf
  refine b3Lie_isQuasisimple_of_simple ?_
  by_contra hcomm'
  push Not at hcomm'
  exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hcomm' a b⟩⟩

theorem centCompQuasi_alt (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 8) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {x : alternatingGroup (Fin n)} (hx : x ^ q = 1) (hx1 : x ≠ 1) (r : ℕ) (hr : r.Prime) :
    CentCompQuasi (alternatingGroup (Fin n)) x r := by
  intro J hJ
  have hσq : (x : Equiv.Perm (Fin n)) ^ q = 1 := by simpa using congrArg Subtype.val hx
  have hσ1 : (x : Equiv.Perm (Fin n)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  haveI : Fact q.Prime := ⟨hq⟩
  have hord : orderOf (x : Equiv.Perm (Fin n)) = q := orderOf_eq_prime hσq hσ1
  obtain ⟨k, hk, hkn⟩ := cq_cycleType_of_prime_order (x : Equiv.Perm (Fin n)) hq hord
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      apply hσ1
      rw [h0] at hk
      exact Equiv.Perm.cycleType_eq_zero.1 (by rw [hk]; rfl)
    · exact h0
  by_cases hspec : n = 8 ∧ q = 3 ∧ k = 1
  · obtain ⟨rfl, rfl, rfl⟩ := hspec
    exact centCompQuasi_alt_eight_three_cycle (by simpa using hk) r hr J hJ
  · exfalso
    have hJC : J ≤ Subgroup.centralizer {x} := hJ.1
    have hdiv : Nat.card J ∣ (n - k * q).factorial * q ^ k * k.factorial := by
      rw [← cq_card_centralizer_replicate (x : Equiv.Perm (Fin n)) hk1 hk]
      exact (Subgroup.card_dvd_of_le hJC).trans (cq_card_centralizer_dvd_alt x)
    haveI : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).2 (cq_glaPComponent_ne_bot hJ)
    haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
    have hq3 : 3 ≤ q := by
      have := hq.two_le
      omega
    have hqn : q ≤ n := by nlinarith
    have hq357 : q = 3 ∨ q = 5 ∨ q = 7 := by
      have hq8 : q ≤ 8 := by rcases hn with rfl | rfl | rfl <;> omega
      interval_cases q <;> first | omega | (exfalso; revert hq; norm_num)
    have hkle : k ≤ 2 := by rcases hq357 with rfl | rfl | rfl <;> omega
    rcases hn with rfl | rfl | rfl <;> rcases hq357 with rfl | rfl | rfl <;> interval_cases k <;>
      first
        | omega
        | (norm_num [Nat.factorial] at hdiv
           exact false_of_perfect_card_dvd (by norm_num) hdiv)

end CFSG.LocalAnalysis.GLTheoremA
