module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3A9Rank
import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

section Conjugates

variable {Y : Type*} [Group Y]

theorem injective_map_conj_pow_prime_mem {p : ℕ} (hp : p.Prime) {A : Subgroup Y} {u : Y}
    (hu : u ^ p ∈ Subgroup.normalizer (A : Set Y)) (hn : u ∉ Subgroup.normalizer (A : Set Y)) :
    Function.Injective fun j : Fin p => A.map (MulAut.conj (u ^ (j : ℕ))).toMonoidHom := by
  have hstep : ∀ i j : ℕ, i < j → A.map (MulAut.conj (u ^ i)).toMonoidHom =
      A.map (MulAut.conj (u ^ j)).toMonoidHom → u ^ (j - i) ∈ Subgroup.normalizer (A : Set Y) := by
    intro i j hij hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hj : u ^ j = u ^ i * u ^ (j - i) := by rw [← pow_add]; congr 1; omega
    rw [hj, map_conj_mul_eq] at hh
    exact (Subgroup.map_injective (MulAut.conj (u ^ i)).injective hh).symm
  have hkey : ∀ i j : ℕ, i < j → j < p → A.map (MulAut.conj (u ^ i)).toMonoidHom =
      A.map (MulAut.conj (u ^ j)).toMonoidHom → False := by
    intro i j hij hjp hh
    have h1 := hstep i j hij hh
    apply hn
    have hcop : Nat.Coprime p (j - i) := (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd =>
      absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have hab' : (p : ℤ) * a + ((j - i : ℕ) : ℤ) * b = 1 := by rw [← hab]; ring
    have hu_eq : u = (u ^ p) ^ a * (u ^ (j - i)) ^ b := by
      rw [← zpow_natCast u p, ← zpow_natCast u (j - i), ← zpow_mul, ← zpow_mul, ← zpow_add, hab',
        zpow_one]
    rw [hu_eq]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hu a) (Subgroup.zpow_mem _ h1 b)
  intro i j hij
  by_contra hne
  have hne' : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · exact hkey i j hlt j.2 hij
  · exact hkey j i hlt i.2 hij.symm

end Conjugates

variable {G : Type} [Group G] [Finite G]

theorem false_of_not_mem_normalizer_of_pow_prime_mem {p : ℕ} (hp : p.Prime)
    (hbound : ∀ q : ℕ, q.Prime → 5 ≤ q → rankThreeLocalRank q G < p) {M L : Subgroup G}
    (hM : IsTwoLocal M) (hL : IsTwoPrimeComponent M L) {s : G} (hsM : s ∈ M)
    (hs : s ^ p ∈ Subgroup.normalizer (L : Set G))
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
  have hspM : s ^ p ∈ M := M.pow_mem hsM p
  have hup : u ^ p ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have hup' : u ^ p = mk ⟨s ^ p, hspM⟩ := by
      rw [hu, ← map_pow]
      rfl
    rw [hup', Subgroup.mem_normalizer_iff_map_conj_eq]
    have h1 := barM_map_conj hspM L
    have h2 : L.map (MulAut.conj (s ^ p)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
    rw [h2] at h1
    exact h1.symm
  have hun : u ∉ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hs => by
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
    apply hsL
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (hL.map_conj hsM).eq_of_barM_eq hL (by rw [barM_map_conj hsM]; exact h1)
  have hinj := injective_map_conj_pow_prime_mem hp hup hun
  have hLbM : barM M L ≤ barM M M := by
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr a.2, rfl⟩
  have hg : ∀ j : Fin p, u ^ (j : ℕ) ∈ barM M M := fun j =>
    ⟨(⟨s, hsM⟩ : M) ^ (j : ℕ), Subgroup.mem_subgroupOf.mpr ((⟨s, hsM⟩ : M) ^ (j : ℕ)).2,
      map_pow mk _ _⟩
  have hple := le_pRank_of_injective_conj stmtComponentRank stmtBarPRankLift (le_refl M) hq
    (by omega) hLb hLbM hyL hyq hlL hyl (fun j : Fin p => u ^ (j : ℕ)) hg hinj
  have h1 := local_pRank_le_localRank q hq.one_lt M hM
  have h2 := hbound q hq hq5
  omega

theorem le_normalizer_of_isPGroup_prime {p : ℕ} (hp : p.Prime)
    (hbound : ∀ q : ℕ, q.Prime → 5 ≤ q → rankThreeLocalRank q G < p) {M L : Subgroup G}
    (hM : IsTwoLocal M) (hL : IsTwoPrimeComponent M L) {P : Subgroup G} (hP : IsPGroup p P)
    (hPM : P ≤ M) : P ≤ Subgroup.normalizer (L : Set G) := by
  classical
  intro x hxP
  by_contra hx
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hex : ∃ j : ℕ, x ^ p ^ j ∈ Subgroup.normalizer (L : Set G) :=
    ⟨k, by rw [hk']; exact Subgroup.one_mem _⟩
  set j := Nat.find hex with hj
  have hjmem : x ^ p ^ j ∈ Subgroup.normalizer (L : Set G) := Nat.find_spec hex
  have hj0 : j ≠ 0 := fun h0 => hx (by simpa [h0] using hjmem)
  obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hnot : x ^ p ^ i ∉ Subgroup.normalizer (L : Set G) :=
    Nat.find_min hex (by omega : i < j)
  refine false_of_not_mem_normalizer_of_pow_prime_mem hp hbound hM hL
    (s := x ^ p ^ i) (hPM (P.pow_mem hxP _)) ?_ hnot
  rw [← pow_mul, ← pow_succ]
  rw [hi] at hjmem
  exact hjmem

theorem le_normalizer_of_isPGroup_three3 (hrank : evenRank G = 3) (h3 : 3 ∈ rankThreeSigmaA G)
    {M L : Subgroup G} (hM : IsTwoLocal M) (hL : IsTwoPrimeComponent M L) {P : Subgroup G}
    (hP : IsPGroup 3 P) (hPM : P ≤ M) : P ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_isPGroup_prime Nat.prime_three
    (fun _ hq hq5 => rankThreeLocalRank_lt_three_of_sigmaA_three hrank h3 hq (by omega)) hM hL hP
    hPM

theorem le_normalizer_of_isPGroup_ge_five (hrank : evenRank G = 3) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {M L : Subgroup G} (hM : IsTwoLocal M) (hL : IsTwoPrimeComponent M L)
    {P : Subgroup G} (hP : IsPGroup p P) (hPM : P ≤ M) :
    P ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_isPGroup_prime hp
    (fun q hq hq5 => lt_of_le_of_lt (hrank ▸ rankThreeLocalRank_le_evenRank (G := G) q hq
      (by omega)) (by omega)) hM hL hP hPM

end CFSG.LocalAnalysis.RankThreeTheoremC
