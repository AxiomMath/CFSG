module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.CharacterTheory.Burnside
import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

theorem exists_prime_ge_five_dvd_card_of_not_isSolvable {Y : Type*} [Group Y] [Finite Y]
    (h : ¬ Group.IsSolvable Y) : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card Y := by
  by_contra hcon
  push Not at hcon
  apply h
  have hn : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hpf : ∀ r : ℕ, r.Prime → r ∣ Nat.card Y → r = 2 ∨ r = 3 := by
    intro r hr hrd
    by_contra hne
    push Not at hne
    have h5 : 5 ≤ r := by
      have h2 := hr.two_le
      have h4 : r ≠ 4 := by
        rintro rfl
        exact absurd hr (by norm_num)
      omega
    exact hcon r hr h5 hrd
  have hcard : Nat.card Y =
      2 ^ (Nat.card Y).factorization 2 * 3 ^ (Nat.card Y).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod_of_support_subset _ (s := {2, 3}) ?_ _ (fun _ _ => pow_zero _),
      Finset.prod_pair (by norm_num)]
    intro r hr
    rw [Nat.support_factorization] at hr
    have := hpf r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
    simpa using this
  have := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

section SigmaA

variable {G : Type} [Group G] [Finite G]

theorem rankThreeLocalRank_lt_three_of_sigmaA_three (hrank : evenRank G = 3)
    (h3 : 3 ∈ rankThreeSigmaA G) {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) :
    rankThreeLocalRank q G < 3 := by
  classical
  by_contra hlt
  push Not at hlt
  have hupper := rankThreeLocalRank_le_evenRank (G := G) q hq (by omega)
  have hupper3 := rankThreeLocalRank_le_evenRank (G := G) 3 Nat.prime_three (by norm_num)
  have hq_eq : rankThreeLocalRank q G = 3 := by omega
  obtain ⟨H, -, hHrank⟩ := rankThreeLocalRank_attained (G := G) q (by omega)
  have hqdvd : q ∣ Nat.card G := prime_dvd_card_of_pRank_pos q H (by omega)
  have hS3 : ({p : ℕ | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧ rankThreeLocalRank p G = 3}).Nonempty :=
    ⟨q, hq, hq3, hqdvd, hq_eq⟩
  dsimp only [rankThreeSigmaA] at h3
  split_ifs at h3
  · exact absurd h3.2.2.2 (by omega)
  · exact absurd h3.2.1 (by norm_num)
  · exact absurd h3.2.1 (by norm_num)

end SigmaA

section Conjugates

variable {Y : Type*} [Group Y]

theorem injective_map_conj_pow_three {A : Subgroup Y} {u : Y} (hu : u ^ 3 = 1)
    (hn : u ∉ Subgroup.normalizer (A : Set Y)) :
    Function.Injective fun j : Fin 3 => A.map (MulAut.conj (u ^ (j : ℕ))).toMonoidHom := by
  have hstep : ∀ i j : ℕ, i < j → A.map (MulAut.conj (u ^ i)).toMonoidHom =
      A.map (MulAut.conj (u ^ j)).toMonoidHom → u ^ (j - i) ∈ Subgroup.normalizer (A : Set Y) := by
    intro i j hij hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hj : u ^ j = u ^ i * u ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [hj, map_conj_mul_eq] at hh
    exact (Subgroup.map_injective (MulAut.conj (u ^ i)).injective hh).symm
  have hkey : ∀ i j : ℕ, i < j → j < 3 → A.map (MulAut.conj (u ^ i)).toMonoidHom =
      A.map (MulAut.conj (u ^ j)).toMonoidHom → False := by
    intro i j hij hj3 hh
    have h1 := hstep i j hij hh
    apply hn
    rcases (by omega : j - i = 1 ∨ j - i = 2) with hd | hd
    · simpa [hd] using h1
    · rw [hd] at h1
      have h2 : u = (u ^ 2) ^ 2 := by
        calc u = u ^ 3 * u := by rw [hu, one_mul]
          _ = (u ^ 2) ^ 2 := by group
      rw [h2]
      exact Subgroup.pow_mem _ h1 2
  intro i j hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact hkey i j hlt j.2 hij
  · exact hkey j i hlt i.2 hij.symm

end Conjugates

section ThreeBlocks

variable {G : Type} [Group G] [Finite G]

theorem false_of_not_mem_normalizer_of_pow_three3 (hrank : evenRank G = 3)
    (h3 : 3 ∈ rankThreeSigmaA G) {M L : Subgroup G} (hM : IsTwoLocal M)
    (hL : IsTwoPrimeComponent M L) {s : G} (hsM : s ∈ M) (hs3 : s ^ 3 = 1)
    (hsL : s ∉ Subgroup.normalizer (L : Set G)) : False := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hLb : IsComponentOf (barM M L) ⊤ := hL.component
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
    hLb.2.2
  have : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hLb.2.2.2
  have hnsol : ¬ Group.IsSolvable (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := fun hs => by
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)
  obtain ⟨q, hq, hq5, hqd⟩ := exists_prime_ge_five_dvd_card_of_not_isSolvable hnsol
  obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqd
  set u : ↥M ⧸ CFSG.pCore 2 ↥M := mk ⟨s, hsM⟩ with hu
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← map_pow, show (⟨s, hsM⟩ : M) ^ 3 = 1 from Subtype.ext hs3, map_one]
  have hun : u ∉ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hs => by
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
    apply hsL
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (hL.map_conj hsM).eq_of_barM_eq hL (by rw [barM_map_conj hsM]; exact h1)
  have hinj := injective_map_conj_pow_three hu3 hun
  have hLbM : barM M L ≤ barM M M := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  have hg : ∀ j : Fin 3, u ^ (j : ℕ) ∈ barM M M := fun j =>
    ⟨(⟨s, hsM⟩ : M) ^ (j : ℕ), Subgroup.mem_subgroupOf.mpr ((⟨s, hsM⟩ : M) ^ (j : ℕ)).2,
      map_pow mk _ _⟩
  have h3le := le_pRank_of_injective_conj stmtComponentRank stmtBarPRankLift (le_refl M) hq
    (by omega) hLb hLbM hyL hyq hlL hyl (fun j : Fin 3 => u ^ (j : ℕ)) hg hinj
  have h1 := local_pRank_le_localRank q hq.one_lt M hM
  have h2 := rankThreeLocalRank_lt_three_of_sigmaA_three hrank h3 hq (by omega)
  omega

end ThreeBlocks

end CFSG.LocalAnalysis.RankThreeTheoremC
