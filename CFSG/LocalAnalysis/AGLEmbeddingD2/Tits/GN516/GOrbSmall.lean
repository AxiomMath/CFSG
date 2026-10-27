module

public import Mathlib.GroupTheory.PGroup
import CFSG.Assembly.OrderReductions.PermutationReduction
import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Small

open CFSG.OrderReductions.PermutationReduction

private theorem factorization_eq_of_pow_dvd_not {N p k : ℕ} (hp : p.Prime) (hN : N ≠ 0)
    (hk1 : p ^ k ∣ N) (hk2 : ¬ p ^ (k + 1) ∣ N) : N.factorization p = k := by
  have low : k ≤ N.factorization p := (hp.pow_dvd_iff_le_factorization hN).mp hk1
  have high : ¬ k + 1 ≤ N.factorization p := fun h =>
    hk2 ((hp.pow_dvd_iff_le_factorization hN).mpr h)
  omega

private theorem sylow_count_data {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (noncomm : ¬ IsMulCommutative S) {p : ℕ} (hp : p.Prime) (k N : ℕ) (hN : Nat.card S = N)
    (hk1 : p ^ k ∣ N) (hk2 : ¬ p ^ (k + 1) ∣ N) (hk0 : 0 < k) :
    5 ≤ Nat.card (Sylow p S) ∧ Nat.card (Sylow p S) ≤ N ∧
      Nat.card (Sylow p S) * p ^ k ∣ N ∧ Nat.card (Sylow p S) % p = 1 % p := by
  haveI : Fact p.Prime := ⟨hp⟩
  subst hN
  have hdvd : p ∣ Nat.card S := (dvd_pow_self p hk0.ne').trans hk1
  obtain ⟨c1, c2, c3⟩ := simple_noncommutative_sylow_card_constraints S noncomm p hdvd
  have fac := factorization_eq_of_pow_dvd_not hp (Nat.card_pos : 0 < Nat.card S).ne' hk1 hk2
  rw [fac] at c2
  have bound := Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card S) c2
  exact ⟨c1, (le_mul_of_one_le_right (Nat.zero_le _) (pow_pos hp.pos k)).trans bound, c2, c3⟩

private theorem false_of_sylow_count_small {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (noncomm : ¬ IsMulCommutative S) {p : ℕ} (hp : p.Prime) (k N : ℕ) (hN : Nat.card S = N)
    (hk1 : p ^ k ∣ N) (hk2 : ¬ p ^ (k + 1) ∣ N) (hk0 : 0 < k)
    (hnum : ∀ n ≤ N, 5 ≤ n → n * p ^ k ∣ N → n % p ≠ 1 % p) : False := by
  obtain ⟨c1, c2, c3, c4⟩ := sylow_count_data noncomm hp k N hN hk1 hk2 hk0
  exact hnum _ c2 c1 c3 c4

private theorem card_dvd_half_factorial_of_sylow_le {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (noncomm : ¬ IsMulCommutative S) {p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ Nat.card S) (d : ℕ) (hd : 5 ≤ d) (hcount : Nat.card (Sylow p S) ≤ d) :
    Nat.card S ∣ Nat.factorial d / 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p S) := inferInstance
  have proper := simple_noncommutative_sylow_normalizer_ne_top S noncomm p hdvd P
  have index_le : (Subgroup.normalizer (P : Set S)).index ≤ d := by
    rw [← P.card_eq_index_normalizer]
    exact hcount
  exact simple_noncommutative_card_dvd_alternating_order_of_index_bound S noncomm _ proper d hd
    index_le

private theorem card_eq_sixty_or_360_of_index_le_six {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (noncomm : ¬ IsMulCommutative S) (H : Subgroup S) (proper : H ≠ ⊤)
    (small : H.index ≤ 6) : Nat.card S = 60 ∨ Nat.card S = 360 := by
  classical
  let _ : Fintype (S ⧸ H) := Fintype.ofFinite _
  haveI := CFSG.OrderReductions.Helpers.simple_noncommutative_isPerfect S noncomm
  have coset_bound : Fintype.card (S ⧸ H) ≤ Fintype.card (Fin 6) := by
    simpa only [H.index_eq_card, Nat.card_eq_fintype_card, Fintype.card_fin] using small
  obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le coset_bound
  let permutation_hom := (Equiv.Perm.viaEmbeddingHom embedding).comp
    (MulAction.toPermHom S (S ⧸ H))
  have permutation_injective : Function.Injective permutation_hom :=
    (Equiv.Perm.viaEmbeddingHom_injective embedding).comp
      (simple_coset_action_injective S H proper)
  let alternating_hom := permutation_hom.codRestrict (alternatingGroup (Fin 6))
    (perfect_perm_hom_mem_alternating S (Fin 6) permutation_hom)
  have alternating_injective : Function.Injective alternating_hom := by
    intro first second equal_images
    exact permutation_injective (congrArg Subtype.val equal_images)
  exact simple_card_sixty_or_360_of_embedding_alternating_six S noncomm alternating_hom
    alternating_injective

private theorem eight_dvd_of_nonabelian_two_group (G : Type*) [Group G] [Finite G]
    (hG : IsPGroup 2 G) (noncomm : ¬ IsMulCommutative G) : 8 ∣ Nat.card G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hG
  have three_le : 3 ≤ n := by
    by_contra small
    have lt : n < 3 := by omega
    interval_cases n
    · rw [pow_zero] at hn
      haveI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hn).1
      exact noncomm inferInstance
    · rw [pow_one] at hn
      haveI : IsCyclic G := isCyclic_of_prime_card hn
      exact noncomm inferInstance
    · exact noncomm (IsPGroup.isMulCommutative_of_card_eq_prime_sq hn)
  have eight : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [hn, eight]
  exact pow_dvd_pow 2 three_le

theorem card_gt_120_of_nonabelian_two_subgroup {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (hQ : ∃ Q : Subgroup S, IsPGroup 2 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) :
    120 < Nat.card S := by
  obtain ⟨Q, hQ2, a, ha, b, hb, hab⟩ := hQ
  have noncomm : ¬ IsMulCommutative S := by
    intro commutative
    exact hab (commutative.is_comm.comm a b)
  have noncommQ : ¬ IsMulCommutative Q := by
    intro commutative
    apply hab
    exact congrArg Subtype.val (commutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have eight_dvd : 8 ∣ Nat.card S :=
    (eight_dvd_of_nonabelian_two_group Q hQ2 noncommQ).trans (Subgroup.card_subgroup_dvd_card Q)
  by_contra small
  have pos : 0 < Nat.card S := Nat.card_pos
  obtain ⟨m, hm⟩ := eight_dvd
  have m_le : m ≤ 15 := by omega
  interval_cases m
  · omega
  ·
    exact false_of_sylow_count_small noncomm Nat.prime_two 3 8 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    exact false_of_sylow_count_small noncomm Nat.prime_two 4 16 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    exact false_of_sylow_count_small noncomm Nat.prime_two 3 24 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    exact false_of_sylow_count_small noncomm Nat.prime_two 5 32 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    exact false_of_sylow_count_small noncomm (by norm_num : Nat.Prime 5) 1 40 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    exact false_of_sylow_count_small noncomm Nat.prime_two 4 48 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    have hN : Nat.card S = 56 := by omega
    have prime7 : Nat.Prime 7 := by norm_num
    haveI : Fact (Nat.Prime 7) := ⟨prime7⟩
    have hdvd : 7 ∣ Nat.card S := by rw [hN]; decide
    obtain ⟨c1, c2, c3, c4⟩ :=
      sylow_count_data noncomm prime7 1 56 hN (by decide) (by decide) (by decide)
    have count8 : Nat.card (Sylow 7 S) = 8 := by
      have key : ∀ n ≤ 56, 5 ≤ n → n * 7 ^ 1 ∣ 56 → n % 7 = 1 % 7 → n = 8 := by decide
      exact key _ c2 c1 c3 c4
    obtain ⟨P⟩ : Nonempty (Sylow 7 S) := inferInstance
    have index8 : (Subgroup.normalizer (P : Set S)).index = 8 := by
      rw [← P.card_eq_index_normalizer]
      exact count8
    have fac : (Nat.card S).factorization 7 = 1 :=
      factorization_eq_of_pow_dvd_not prime7 (by omega) (by rw [hN]; decide)
        (by rw [hN]; decide)
    have card_P : Nat.card (P : Subgroup S) = 7 := by
      rw [P.card_eq_multiplicity, fac, pow_one]
    have card_N : Nat.card (Subgroup.normalizer (P : Set S)) = 7 := by
      have h := (Subgroup.normalizer (P : Set S)).card_mul_index
      rw [index8, hN] at h
      omega
    have le_norm : (P : Subgroup S) ≤ Subgroup.normalizer (P : Set S) := Subgroup.le_normalizer
    have eq_norm : Subgroup.normalizer (P : Set S) = (P : Subgroup S) :=
      (Subgroup.eq_of_le_of_card_ge le_norm (by omega)).symm
    haveI : IsCyclic (P : Subgroup S) := isCyclic_of_prime_card card_P
    have hcomm : IsMulCommutative (P : Subgroup S) := inferInstance
    have hP : Subgroup.normalizer (P : Set S) ≤ Subgroup.centralizer (P : Set S) := by
      intro x hx
      rw [eq_norm] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨h, hh⟩ ⟨x, hx⟩)
    obtain ⟨K, K_normal, -, K_index, -⟩ :=
      CFSG.GroupTheory.burnside_normal_complement P hP
    rcases CFSG.eq_bot_or_eq_top_of_normal K K_normal with rfl | rfl
    · rw [Subgroup.index_bot, hN, card_P] at K_index
      omega
    · rw [Subgroup.index_top, card_P] at K_index
      omega
  ·
    exact false_of_sylow_count_small noncomm Nat.prime_two 6 64 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    exact false_of_sylow_count_small noncomm (by norm_num : Nat.Prime 3) 2 72 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    have hN : Nat.card S = 80 := by omega
    have hdvd : 2 ∣ Nat.card S := by rw [hN]; decide
    obtain ⟨c1, c2, c3, c4⟩ :=
      sylow_count_data noncomm Nat.prime_two 4 80 hN (by decide) (by decide) (by decide)
    have le5 : Nat.card (Sylow 2 S) ≤ 5 := by
      have key : ∀ n ≤ 80, 5 ≤ n → n * 2 ^ 4 ∣ 80 → n ≤ 5 := by decide
      exact key _ c2 c1 c3
    have h := card_dvd_half_factorial_of_sylow_le noncomm Nat.prime_two hdvd 5 (by norm_num) le5
    rw [hN] at h
    exact absurd h (by decide)
  ·
    exact false_of_sylow_count_small noncomm (by norm_num : Nat.Prime 11) 1 88 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    exact false_of_sylow_count_small noncomm Nat.prime_two 5 96 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    exact false_of_sylow_count_small noncomm (by norm_num : Nat.Prime 13) 1 104 (by omega)
      (by decide) (by decide) (by decide) (by decide)
  ·
    have hN : Nat.card S = 112 := by omega
    have hdvd : 2 ∣ Nat.card S := by rw [hN]; decide
    obtain ⟨c1, c2, c3, c4⟩ :=
      sylow_count_data noncomm Nat.prime_two 4 112 hN (by decide) (by decide) (by decide)
    have le7 : Nat.card (Sylow 2 S) ≤ 7 := by
      have key : ∀ n ≤ 112, 5 ≤ n → n * 2 ^ 4 ∣ 112 → n ≤ 7 := by decide
      exact key _ c2 c1 c3
    have h := card_dvd_half_factorial_of_sylow_le noncomm Nat.prime_two hdvd 7 (by norm_num) le7
    rw [hN] at h
    exact absurd h (by decide)
  ·
    have hN : Nat.card S = 120 := by omega
    have prime5 : Nat.Prime 5 := by norm_num
    haveI : Fact (Nat.Prime 5) := ⟨prime5⟩
    have hdvd : 5 ∣ Nat.card S := by rw [hN]; decide
    obtain ⟨c1, c2, c3, c4⟩ :=
      sylow_count_data noncomm prime5 1 120 hN (by decide) (by decide) (by decide)
    have count6 : Nat.card (Sylow 5 S) = 6 := by
      have key : ∀ n ≤ 120, 5 ≤ n → n * 5 ^ 1 ∣ 120 → n % 5 = 1 % 5 → n = 6 := by decide
      exact key _ c2 c1 c3 c4
    obtain ⟨P⟩ : Nonempty (Sylow 5 S) := inferInstance
    have index6 : (Subgroup.normalizer (P : Set S)).index = 6 := by
      rw [← P.card_eq_index_normalizer]
      exact count6
    have proper := simple_noncommutative_sylow_normalizer_ne_top S noncomm 5 hdvd P
    rcases card_eq_sixty_or_360_of_index_le_six noncomm _ proper index6.le with h | h <;> omega

end CFSG.AGLEmbeddingD2.Tits.GN516.Small
