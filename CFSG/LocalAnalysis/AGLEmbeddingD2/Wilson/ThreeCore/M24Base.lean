
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24Check
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Spec
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.Certificates.Kernel.Spor.RawTreeDefs

@[expose] public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.RankThree.LocalRank CFSG.Blueprint CFSG.Sporadic.Mathieu

def gg (l : ℕ) : Equiv.Perm (Fin 24) := if l = 0 then m24gA else m24gB

theorem gA_mem : m24gA ∈ NativeSporadic.M24 := subset_closure (Set.mem_insert _ _)

theorem gB_mem : m24gB ∈ NativeSporadic.M24 := subset_closure (Set.mem_insert_of_mem _ rfl)

theorem letG_mem (l : ℤ) : letG l ∈ NativeSporadic.M24 := by
  unfold letG
  split_ifs
  · exact gA_mem
  · exact inv_mem gA_mem
  · exact gB_mem
  · exact inv_mem gB_mem

theorem wordG_mem (w : List ℤ) : wordG letG w ∈ NativeSporadic.M24 := by
  unfold wordG
  refine NativeSporadic.M24.list_prod_mem fun g hg => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hg
  exact letG_mem l

theorem rep_wT (w : List ℤ) : Rep 24 (wT w) (wordG letG w) :=
  Rep.wordT (by norm_num) w fun l _ => rep_toTable (by norm_num) (letG l)

theorem m24_groupData : GroupDataSound 24 NativeSporadic.M24 m24Pg gg m24Sift where
  lt := by norm_num
  rep := by
    intro l hl
    have hl2 : l < 2 := by simpa [m24Pg] using hl
    interval_cases l
    · exact rep_toTable (by norm_num) m24gA
    · exact rep_toTable (by norm_num) m24gB
  gen := by
    show closure {m24gA, m24gB} = _
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_ofPred_eq]
    have hsz : m24Pg.size = 2 := rfl
    rw [hsz]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      interval_cases l
      · exact Or.inl rfl
      · exact Or.inr rfl
  sift := by
    intro T g hT h
    unfold m24Sift at h
    rw [List.any_eq_true] at h
    obtain ⟨w, -, hw⟩ := h
    rw [rep_unique hT (rep_of_tblEq (rep_wT w) hw)]
    exact wordG_mem w

theorem tp_wT (w : List ℤ) : tp 24 (wT w) = wordG letG w := by
  have h := co2Rep_natArr_iff.2 (rep_wT w)
  exact rep_unique (rep_tp (CFSG.KS.Raw.isInvA_of_rep h (CFSG.KS.Raw.rep_invCand h))) (rep_wT w)

theorem tp_image_pair (u v : List ℤ) :
    tp 24 '' {x | x ∈ ([wT u, wT v] : List Table).toArray} = {wordG letG u, wordG letG v} := by
  ext g
  constructor
  · rintro ⟨T, hT, rfl⟩
    simp only [Set.mem_ofPred_eq, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at hT
    rcases hT with rfl | rfl
    · exact Or.inl (tp_wT u)
    · exact Or.inr (tp_wT v)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨wT u, by simp, tp_wT u⟩
    · exact ⟨wT v, by simp, tp_wT v⟩

theorem xW_pow : wordG letG xW ^ 3 = 1 := by decide +kernel

theorem xW_ne : wordG letG xW ≠ 1 := by decide +kernel

theorem x2W_pow : wordG letG x2W ^ 3 = 1 := by decide +kernel

theorem x2W_ne : wordG letG x2W ≠ 1 := by decide +kernel

theorem theta_of_words (K : Subgroup (Equiv.Perm (Fin 24))) (ps : List (List ℤ × List ℤ))
    (hcov : ∀ y ∈ K, (orderOf y).Prime → orderOf y ≠ 3 →
      ∃ r ∈ ps.map Prod.fst, ∃ c ∈ K, y = c * wordG letG r * c⁻¹)
    (hwit : ∀ p ∈ ps, wordG letG p.2 ∈ K ∧
      3 ∣ orderOf (wordG letG p.1 * (wordG letG p.2 * wordG letG p.1 * (wordG letG p.2)⁻¹))) :
    aschbacherSolvableCore 3 ↥K = ⊥ := by
  refine aschbacherSolvableCore_eq_bot_of_witnesses K (ps.map fun p => wordG letG p.1) ?_ ?_
  · intro y hy hq hq3
    obtain ⟨r, hr, c, hc, rfl⟩ := hcov y hy hq hq3
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, c, hc, rfl⟩
  · intro x hx N _ hN hxN
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hh, h3⟩ := hwit p hp
    exact ⟨_, N.mul_mem hxN (hN _ hh _ hxN), h3⟩

theorem m24_primes : ∀ r ∈ [m24Row3A, m24Row3B], ∀ q : ℕ, q.Prime → q ∣ r.centOrder → q ≠ 3 →
    q ∈ r.oddPrimes := by
  intro r hr q hq hdvd hq3
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change q ∣ 1080 at hdvd
    change q ∈ [2, 5]
    rw [show (1080 : ℕ) = 2 ^ 3 * 3 ^ 3 * 5 by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h5
    · rcases (Nat.Prime.dvd_mul hq).1 h with h2 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2)
        simp [this]
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
          (hq.dvd_of_dvd_pow h3)) hq3
    · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 5)).1 h5
      simp [this]
  · change q ∣ 504 at hdvd
    change q ∈ [2, 7]
    rw [show (504 : ℕ) = 2 ^ 3 * 3 ^ 2 * 7 by norm_num] at hdvd
    rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h7
    · rcases (Nat.Prime.dvd_mul hq).1 h with h2 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h2)
        simp [this]
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1
          (hq.dvd_of_dvd_pow h3)) hq3
    · have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).1 h7
      simp [this]

theorem m24_sylow : (27 : ℕ) = 3 ^ (244823040 : ℕ).factorization 3 := by
  rw [show (244823040 : ℕ) = 3 ^ 3 * 9067520 by norm_num,
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  norm_num

end CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24
