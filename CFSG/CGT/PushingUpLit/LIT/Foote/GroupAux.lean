module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.BurnsideNormalComplement
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open scoped commutatorElement

theorem not_odd_card_of_perfect {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    [Group.IsPerfect Q] : ¬ Odd (Nat.card Q) :=
  fun h => Group.IsPerfect.not_isSolvable Q (CFSG.FeitThompson.isSolvable_of_odd_natCard _ h)

theorem four_dvd_card_of_perfect {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    [Group.IsPerfect Q] : 4 ∣ Nat.card Q := by
  classical
  by_contra h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 Q) := inferInstance
  have hP : Nat.card P = 2 ^ (Nat.card Q).factorization 2 := Sylow.card_eq_multiplicity P
  have hv : (Nat.card Q).factorization 2 < 2 := by
    by_contra hcon
    push Not at hcon
    exact h4 ((pow_dvd_pow 2 hcon).trans (Nat.ordProj_dvd _ _))
  have hQne : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  rcases Nat.lt_succ_iff.mp hv |>.eq_or_lt with h1 | h0
  ·
    have hP2 : Nat.card P = 2 := by rw [hP, h1]; norm_num
    have hnorm : Subgroup.normalizer (P : Set Q) ≤ Subgroup.centralizer (P : Set Q) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      by_cases h1' : h = 1
      · simp [h1']
      · have hmem : g * h * g⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hg h).1 hh
        have hne : g * h * g⁻¹ ≠ 1 := by
          intro e
          apply h1'
          simpa using e
        have hcard : Nat.card (P : Subgroup Q) = 2 := hP2
        obtain ⟨a, ha⟩ := (Nat.card_eq_two_iff' (1 : P)).1 hcard
        have e1 : (⟨h, hh⟩ : P) = a := ha.2 _ (fun e => h1' (congrArg Subtype.val e))
        have e2 : (⟨g * h * g⁻¹, hmem⟩ : P) = a := ha.2 _ (fun e => hne (congrArg Subtype.val e))
        have : g * h * g⁻¹ = h := congrArg Subtype.val (e2.trans e1.symm)
        calc h * g = (g * h * g⁻¹) * g := by rw [this]
          _ = g * h := by group
    obtain ⟨K, hK, -, hidx, -, -, -, -, -, -, hab⟩ :=
      CFSG.GroupTheory.burnside_normal_complement P hnorm
    have hcomm : commutator Q ≤ K := by
      show ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ K
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      have h1 : QuotientGroup.mk' K ⁅a, b⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hab _ _)
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hKtop : K = ⊤ := by
      rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := Q)]
      exact hcomm
    rw [hKtop, Subgroup.index_top, hP2] at hidx
    omega
  ·
    have h0' : (Nat.card Q).factorization 2 = 0 := by omega
    have hodd : Odd (Nat.card Q) := by
      rw [Nat.odd_iff]
      by_contra hne
      have h2 : 2 ∣ Nat.card Q := by omega
      have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hQne).1 h2
      omega
    exact not_odd_card_of_perfect hodd

theorem eq_of_forall_isTwoElement_mem {G : Type*} [Group G] [Finite G] {K N : Subgroup G}
    (hperf : ⁅K, K⁆ = K) (hNK : N ≤ K) (hN : ∀ g ∈ K, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (h2 : ∀ g ∈ K, (∃ k : ℕ, g ^ 2 ^ k = 1) → g ∈ N) : N = K := by
  classical
  have hnormM : (N.subgroupOf K).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hN g g.2 n hn⟩
  set M := N.subgroupOf K with hM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hperf
  obtain ⟨B⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  have hBM : (B : Subgroup ↥K) ≤ M := by
    intro b hb
    obtain ⟨k, hk⟩ := B.isPGroup' ⟨b, hb⟩
    have e1 : b ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hbk : (b : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val e1
    exact h2 b b.2 ⟨k, hbk⟩
  have hBcard : Nat.card B = 2 ^ (Nat.card ↥K).factorization 2 := Sylow.card_eq_multiplicity B
  have hdvd : 2 ^ (Nat.card ↥K).factorization 2 ∣ Nat.card M := by
    rw [← hBcard]
    exact Subgroup.card_dvd_of_le hBM
  have hodd : Odd M.index := by
    rw [Nat.odd_iff]
    by_contra hne
    have h2i : 2 ∣ M.index := by omega
    have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
    apply Nat.pow_succ_factorization_not_dvd hK0 Nat.prime_two
    have h3 : 2 ^ ((Nat.card ↥K).factorization 2 + 1) ∣ Nat.card M * M.index := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul hdvd h2i
    rwa [Subgroup.card_mul_index] at h3
  have hQodd : Odd (Nat.card (↥K ⧸ M)) := hodd
  by_contra hne
  have hMtop : M ≠ ⊤ := by
    intro h
    apply hne
    refine le_antisymm hNK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ M := by rw [h]; trivial
    exact this
  have : Nontrivial (↥K ⧸ M) := by
    have h1 : M.index ≠ 1 := fun h => hMtop (Subgroup.index_eq_one.1 h)
    have h2 : 1 < Nat.card (↥K ⧸ M) := by
      have := Nat.card_pos (α := ↥K ⧸ M)
      have h3 : Nat.card (↥K ⧸ M) = M.index := rfl
      omega
    exact Finite.one_lt_card_iff_nontrivial.1 h2
  exact Group.IsPerfect.not_isSolvable (↥K ⧸ M) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hQodd)

theorem hom_eq_one_of_perfect_of_solvable {P S : Type*} [Group P] [Group S] [Group.IsPerfect P]
    [Group.IsSolvable S] (f : P →* S) (x : P) : f x = 1 := by
  have hp : Group.IsPerfect f.range := Group.IsPerfect.range f
  by_contra hne
  have : Nontrivial f.range :=
    ⟨⟨⟨f x, x, rfl⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
  exact Group.IsPerfect.not_isSolvable f.range inferInstance

end CFSG.CGT.PushingUpLit.LIT.Foote
