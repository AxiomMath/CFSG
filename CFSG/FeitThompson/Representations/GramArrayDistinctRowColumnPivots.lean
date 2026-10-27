module

public import Mathlib.Data.Set.Card
public import CFSG.FeitThompson.Representations.GramArrayLineNoOppositeSigns
public import CFSG.FeitThompson.Representations.IntegerVectorSquaredLengthThree
import CFSG.FeitThompson.Representations.GramArraySameLineIntersection
import CFSG.FeitThompson.Representations.LongColumnExclusivePivot
import CFSG.FeitThompson.Representations.PairwiseIntersectingPairsCommonElement
import Mathlib.Data.Int.Order.Units
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

variable {ι : Type*}

theorem eq_single_of_support_eq [DecidableEq ι] {v : ι → ℤ} {p : ι}
    (h : Function.support v = {p}) : v = Pi.single p (v p) := by
  funext k
  by_cases hk : k = p
  · subst hk; simp
  · have hv : v k = 0 := by
      by_contra hv
      exact hk (by simpa [h] using Function.mem_support.mpr hv)
    simp [hk, hv]

theorem apply_eq_zero_of_support_eq_singleton {v : ι → ℤ} {p x : ι}
    (h : Function.support v = {p}) (hx : x ≠ p) : v x = 0 := by
  have hnot : x ∉ Function.support v := by rw [h]; simpa using hx
  simpa [Function.mem_support] using hnot

variable [Fintype ι]

theorem ne_of_dotProduct_ne_zero_of_dotProduct_eq_zero {v w x : ι → ℤ} {q q' : ι}
    (hv : Function.support v = {q}) (hw : Function.support w = {q'})
    (hxv : x ⬝ᵥ v ≠ 0) (hxw : x ⬝ᵥ w = 0) : q ≠ q' := by
  classical
  rintro rfl
  rw [eq_single_of_support_eq hv, dotProduct_single] at hxv
  rw [eq_single_of_support_eq hw, dotProduct_single] at hxw
  have hwq : w q ≠ 0 := by
    have hmem : q ∈ Function.support w := by rw [hw]; rfl
    exact hmem
  rcases mul_eq_zero.mp hxw with h | h
  · exact hxv (by rw [h, zero_mul])
  · exact hwq h

theorem IsSignedCoordVec.support_ne_of_dotProduct [DecidableEq ι] {v w x : ι → ℤ}
    (hv : IsSignedCoordVec v) (hw : IsSignedCoordVec w) (hxv : x ⬝ᵥ v ≠ 0) (hxw : x ⬝ᵥ w = 0) :
    Function.support v ≠ Function.support w := by
  obtain ⟨q, hq, -⟩ := hv.exists_support_eq
  obtain ⟨q', hq', -⟩ := hw.exists_support_eq
  rw [hq, hq']
  simpa using ne_of_dotProduct_ne_zero_of_dotProduct_eq_zero hq hq' hxv hxw

theorem eq_one_or_neg_one_of_dotProduct_self_eq_two {u : ι → ℤ} (hu : u ⬝ᵥ u = 2) {i : ι}
    (hi : u i ≠ 0) : u i = 1 ∨ u i = -1 :=
  sq_eq_one_iff.mp (Int.sq_eq_one_of_sq_le_three
    (le_trans (hu ▸ sq_le_dotProduct_self u i) (by omega)) hi)

theorem card_support_eq_two_of_dotProduct_self_eq_two {u : ι → ℤ} (hu : u ⬝ᵥ u = 2) :
    #{i | u i ≠ 0} = 2 := by
  classical
  have key : ∀ i ∈ ({i | u i ≠ 0} : Finset ι), u i * u i = 1 := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases eq_one_or_neg_one_of_dotProduct_self_eq_two hu hi with h | h <;> simp [h]
  have h2 := hu
  rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ ({i | u i ≠ 0} : Finset ι))
    (fun i _ hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      simp [hi]), Finset.sum_congr rfl key, Finset.sum_const] at h2
  simp only [nsmul_eq_mul, mul_one] at h2
  exact_mod_cast h2

theorem ncard_support_eq_two_of_dotProduct_self_eq_two {u : ι → ℤ} (hu : u ⬝ᵥ u = 2) :
    (Function.support u).ncard = 2 := by
  classical
  have h : Function.support u = ↑({i | u i ≠ 0} : Finset ι) := by
    ext i; simp [Function.mem_support]
  rw [h, Set.ncard_coe_finset, card_support_eq_two_of_dotProduct_self_eq_two hu]

theorem exists_support_inter_eq_singleton_of_dotProduct_two {u v : ι → ℤ}
    (hu : u ⬝ᵥ u = 2) (hv : v ⬝ᵥ v = 2) (huv : u ⬝ᵥ v = 1) :
    ∃ a, Function.support u ∩ Function.support v = {a} ∧ u a = v a ∧ (u a = 1 ∨ u a = -1) := by
  classical
  set T : Finset ι := {k | u k * v k ≠ 0} with hT
  have hmem : ∀ k, k ∈ T ↔ (u k ≠ 0 ∧ v k ≠ 0) := by intro k; simp [hT]
  have hpm : ∀ k ∈ T, u k * v k = 1 ∨ u k * v k = -1 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
    rcases eq_one_or_neg_one_of_dotProduct_self_eq_two hu hk1 with h | h <;>
      rcases eq_one_or_neg_one_of_dotProduct_self_eq_two hv hk2 with h' | h' <;>
      simp [h, h']
  have hsum : ∑ k ∈ T, u k * v k = 1 := by
    rw [Finset.sum_subset (Finset.subset_univ T) (fun k _ hk => by
      by_contra hc
      exact hk ((hmem k).mpr ⟨left_ne_zero_of_mul hc, right_ne_zero_of_mul hc⟩))]
    exact huv
  have hsubT : T ⊆ ({k | u k ≠ 0} : Finset ι) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ((hmem k).mp hk).1
  have hcardle : #T ≤ 2 := by
    refine le_trans (Finset.card_le_card hsubT) ?_
    rw [card_support_eq_two_of_dotProduct_self_eq_two hu]
  have hT1 : #T = 1 := by
    rcases (show #T = 0 ∨ #T = 1 ∨ #T = 2 by omega) with h | h | h
    · rw [Finset.card_eq_zero] at h
      rw [h] at hsum
      simp at hsum
    · exact h
    · obtain ⟨x, y, hxy, hTxy⟩ := Finset.card_eq_two.mp h
      rw [hTxy, Finset.sum_pair hxy] at hsum
      have hx := hpm x (by rw [hTxy]; simp)
      have hy := hpm y (by rw [hTxy]; simp)
      omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hT1
  have haT : a ∈ T := by rw [ha]; simp
  obtain ⟨hua, hva⟩ := (hmem a).mp haT
  have h1 : u a * v a = 1 := by
    rw [ha, Finset.sum_singleton] at hsum
    exact hsum
  refine ⟨a, ?_, ?_, eq_one_or_neg_one_of_dotProduct_self_eq_two hu hua⟩
  · ext k
    simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_singleton_iff]
    rw [← hmem k, ha]
    simp
  · rcases eq_one_or_neg_one_of_dotProduct_self_eq_two hu hua with h | h <;>
      rcases eq_one_or_neg_one_of_dotProduct_self_eq_two hv hva with h' | h' <;>
      rw [h, h'] at h1 ⊢ <;> omega

theorem exists_row_pivots_of_column_pivots {d m n : ℕ} (hm : 2 ≤ m) (hn : n = 2 ∨ 4 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) {c : Fin n → Fin d → ℤ}
    (hcsigned : ∀ j, IsSignedCoordVec (c j))
    (hcdot : ∀ (i : Fin m) (k j : Fin n), b i k ⬝ᵥ c j = if k = j then 1 else 0) :
    ∃ r : Fin m → Fin d → ℤ, (∀ i, IsSignedCoordVec (r i)) ∧
      ∀ i j k, b i j ⬝ᵥ r k = if i = k then 1 else 0 := by
  classical
  have hn2 : 2 ≤ n := by rcases hn with h | h <;> omega
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by omega
  set i₀ : Fin m := ⟨0, hmpos⟩ with hi₀
  set j₀ : Fin n := ⟨0, hnpos⟩ with hj₀
  choose q hqsupp hqval using fun j => (hcsigned j).exists_support_eq
  have hqne : ∀ j, c j (q j) ≠ 0 := fun j => by rcases hqval j with h | h <;> simp [h]
  have hbq : ∀ (i : Fin m) (j : Fin n), b i j (q j) ≠ 0 := by
    intro i j
    have h1 : b i j ⬝ᵥ c j = 1 := by simpa using hcdot i j j
    rw [eq_single_of_support_eq (hqsupp j), dotProduct_single] at h1
    exact left_ne_zero_of_mul (by rw [h1]; norm_num)
  have hqinj : ∀ j l : Fin n, j ≠ l → q j ≠ q l := by
    intro j l hjl
    refine ne_of_dotProduct_ne_zero_of_dotProduct_eq_zero (hqsupp j) (hqsupp l)
      (x := b i₀ j) ?_ ?_
    · rw [hcdot i₀ j j]; norm_num
    · rw [hcdot i₀ j l, if_neg hjl]
  have hcc : ∀ j l : Fin n, j ≠ l → c j ⬝ᵥ c l = 0 := by
    intro j l hjl
    rw [eq_single_of_support_eq (hqsupp l), dotProduct_single,
      apply_eq_zero_of_support_eq_singleton (hqsupp j) (Ne.symm (hqinj j l hjl)), zero_mul]
  have hcself : ∀ j, c j ⬝ᵥ c j = 1 := fun j => (hcsigned j).dotProduct_self
  set a : Fin m → Fin n → Fin d → ℤ := fun i j => b i j - c j with hadef
  have haa : ∀ i j, a i j ⬝ᵥ a i j = 2 := by
    intro i j
    have h1 : b i j ⬝ᵥ c j = 1 := by simpa using hcdot i j j
    have h2 : c j ⬝ᵥ b i j = 1 := by rw [dotProduct_comm]; exact h1
    simp only [hadef]
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hb.dotProduct_self, hcself, h1, h2]
    ring
  have hajl : ∀ (i : Fin m) (j l : Fin n), j ≠ l → a i j ⬝ᵥ a i l = 1 := by
    intro i j l hjl
    have h1 : b i j ⬝ᵥ b i l = 1 := hb.dotProduct_row i hjl
    have h2 : b i j ⬝ᵥ c l = 0 := by rw [hcdot i j l, if_neg hjl]
    have h3 : c j ⬝ᵥ b i l = 0 := by
      rw [dotProduct_comm, hcdot i l j, if_neg (Ne.symm hjl)]
    simp only [hadef]
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, h2, h3, hcc j l hjl]
    ring
  have hac : ∀ i j, a i j ⬝ᵥ c j = 0 := by
    intro i j
    have h1 : b i j ⬝ᵥ c j = 1 := by simpa using hcdot i j j
    simp only [hadef]
    rw [sub_dotProduct, h1, hcself]
    ring
  have hcommon : ∀ i : Fin m, ∃ p : Fin d, ∀ j, a i j p ≠ 0 := by
    intro i
    have hinter : ∀ j l : Fin n, j ≠ l →
        (Function.support (a i j) ∩ Function.support (a i l)).ncard = 1 := by
      intro j l hjl
      obtain ⟨x, hx, -, -⟩ := exists_support_inter_eq_singleton_of_dotProduct_two
        (haa i j) (haa i l) (hajl i j l hjl)
      rw [hx, Set.ncard_singleton]
    have hinj : Function.Injective (fun j => Function.support (a i j)) := by
      intro j l hjl
      by_contra hne
      have h1 := hinter j l hne
      simp only at hjl
      rw [hjl, Set.inter_self, ncard_support_eq_two_of_dotProduct_self_eq_two (haa i l)] at h1
      omega
    have h1 := ncard_iInter_eq_one_of_pairwise_ncard_inter_eq_one hn hinj
      (fun j => ncard_support_eq_two_of_dotProduct_self_eq_two (haa i j)) hinter
    obtain ⟨p, hp⟩ := Set.ncard_eq_one.1 h1
    refine ⟨p, fun j => ?_⟩
    have hmem : p ∈ ⋂ j, Function.support (a i j) := by rw [hp]; rfl
    exact Set.mem_iInter.1 hmem j
  choose p hp using hcommon
  have hval : ∀ (i : Fin m) (j l : Fin n), a i j (p i) = a i l (p i) := by
    intro i j l
    by_cases hjl : j = l
    · rw [hjl]
    obtain ⟨x, hx, hxval, -⟩ := exists_support_inter_eq_singleton_of_dotProduct_two
      (haa i j) (haa i l) (hajl i j l hjl)
    have hpx : p i = x := by
      have hmem : p i ∈ Function.support (a i j) ∩ Function.support (a i l) :=
        ⟨hp i j, hp i l⟩
      rw [hx] at hmem
      exact hmem
    rw [hpx]; exact hxval
  set s : Fin m → ℤ := fun i => a i j₀ (p i) with hsdef
  have hs : ∀ i, s i = 1 ∨ s i = -1 := fun i =>
    eq_one_or_neg_one_of_dotProduct_self_eq_two (haa i j₀) (hp i j₀)
  have hpq : ∀ (i : Fin m) (j : Fin n), p i ≠ q j := by
    intro i j hij
    have h0 : c j ⬝ᵥ a i j = 0 := by rw [dotProduct_comm]; exact hac i j
    rw [eq_single_of_support_eq (hqsupp j), single_dotProduct] at h0
    exact hp i j (hij ▸ ((mul_eq_zero.mp h0).resolve_left (hqne j)))
  have hcp : ∀ (i : Fin m) (j : Fin n), c j (p i) = 0 := fun i j =>
    apply_eq_zero_of_support_eq_singleton (hqsupp j) (hpq i j)
  have hbp : ∀ (i : Fin m) (j : Fin n), b i j (p i) = s i := by
    intro i j
    have h1 : a i j (p i) = s i := by rw [hsdef]; exact hval i j j₀
    have h2 : a i j (p i) = b i j (p i) - c j (p i) := by simp [hadef]
    rw [hcp i j, sub_zero] at h2
    rw [← h2, h1]
  have hbp0 : ∀ (i k : Fin m) (j : Fin n), i ≠ k → b k j (p i) = 0 := by
    intro i k j hik
    by_contra hne
    obtain ⟨x, hx, -, -⟩ := exists_support_inter_eq_singleton_of_isGramArray_fin hm hn2 hb
      (i := i) (j := j) (k := k) (l := j) (by simp [hik]) (Or.inr rfl)
    have h1 : p i ∈ Function.support (b i j) ∩ Function.support (b k j) := by
      refine ⟨?_, hne⟩
      rw [Function.mem_support, hbp i j]
      rcases hs i with h | h <;> simp [h]
    have h2 : q j ∈ Function.support (b i j) ∩ Function.support (b k j) :=
      ⟨hbq i j, hbq k j⟩
    rw [hx] at h1 h2
    exact hpq i j (h1.trans h2.symm)
  refine ⟨fun i => Pi.single (p i) (s i), fun i => isSignedCoordVec_single (hs i), ?_⟩
  intro i j k
  rw [dotProduct_single]
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl, hbp i j]
    rcases hs i with h | h <;> simp [h]
  · rw [if_neg hik, hbp0 k i j (Ne.symm hik), zero_mul]

theorem support_pairwise_ne_of_dotProduct_eq_delta {d m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} {r : Fin m → Fin d → ℤ} {c : Fin n → Fin d → ℤ}
    (hr : ∀ i, IsSignedCoordVec (r i)) (hc : ∀ j, IsSignedCoordVec (c j))
    (hrd : ∀ i j k, b i j ⬝ᵥ r k = if i = k then 1 else 0)
    (hcd : ∀ i j l, b i j ⬝ᵥ c l = if j = l then 1 else 0) :
    (∀ i k, i ≠ k → Function.support (r i) ≠ Function.support (r k)) ∧
      (∀ j l, j ≠ l → Function.support (c j) ≠ Function.support (c l)) ∧
      (∀ i j, Function.support (r i) ≠ Function.support (c j)) := by
  have hmpos : 0 < m := by omega
  have hnpos : 0 < n := by omega
  set i₀ : Fin m := ⟨0, hmpos⟩ with hi₀
  set j₀ : Fin n := ⟨0, hnpos⟩ with hj₀
  refine ⟨fun i k hik => ?_, fun j l hjl => ?_, fun i j => ?_⟩
  · exact (hr i).support_ne_of_dotProduct (hr k) (x := b i j₀)
      (by rw [hrd i j₀ i, if_pos rfl]; norm_num) (by rw [hrd i j₀ k, if_neg hik])
  · exact (hc j).support_ne_of_dotProduct (hc l) (x := b i₀ j)
      (by rw [hcd i₀ j j, if_pos rfl]; norm_num) (by rw [hcd i₀ j l, if_neg hjl])
  ·
    obtain ⟨j', hj'⟩ : ∃ j' : Fin n, j' ≠ j := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
      obtain ⟨j', hj'⟩ := exists_ne j
      exact ⟨j', hj'⟩
    exact (hr i).support_ne_of_dotProduct (hc j) (x := b i j')
      (by rw [hrd i j' i, if_pos rfl]; norm_num) (by rw [hcd i j' j, if_neg hj'])

theorem exists_row_col_pivots_of_four_le_row {d m n : ℕ} (hm : 4 ≤ m) (hn : n = 2 ∨ 4 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) :
    ∃ (r : Fin m → Fin d → ℤ) (c : Fin n → Fin d → ℤ),
      (∀ i, IsSignedCoordVec (r i)) ∧ (∀ j, IsSignedCoordVec (c j)) ∧
      (∀ i k, i ≠ k → Function.support (r i) ≠ Function.support (r k)) ∧
      (∀ j l, j ≠ l → Function.support (c j) ≠ Function.support (c l)) ∧
      (∀ i j, Function.support (r i) ≠ Function.support (c j)) ∧
      (∀ i j k, b i j ⬝ᵥ r k = if i = k then 1 else 0) ∧
      (∀ i j l, b i j ⬝ᵥ c l = if j = l then 1 else 0) := by
  have hn2 : 2 ≤ n := by rcases hn with h | h <;> omega
  obtain ⟨c, hcsigned, hcdot⟩ := exists_pivot_family hm hn2 hb
  obtain ⟨r, hrsigned, hrdot⟩ :=
    exists_row_pivots_of_column_pivots (by omega) hn hb hcsigned hcdot
  have hcdot' : ∀ i j l, b i j ⬝ᵥ c l = if j = l then 1 else 0 := fun i j l => hcdot i j l
  obtain ⟨h1, h2, h3⟩ := support_pairwise_ne_of_dotProduct_eq_delta (by omega) hn2
    hrsigned hcsigned hrdot hcdot'
  exact ⟨r, c, hrsigned, hcsigned, h1, h2, h3, hrdot, hcdot'⟩

theorem exists_row_col_pivots_of_isGramArray {d m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hme : Even m) (hne : Even n) (hmn : m ≠ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) :
    ∃ (r : Fin m → Fin d → ℤ) (c : Fin n → Fin d → ℤ),
      (∀ i, IsSignedCoordVec (r i)) ∧ (∀ j, IsSignedCoordVec (c j)) ∧
      (∀ i k, i ≠ k → Function.support (r i) ≠ Function.support (r k)) ∧
      (∀ j l, j ≠ l → Function.support (c j) ≠ Function.support (c l)) ∧
      (∀ i j, Function.support (r i) ≠ Function.support (c j)) ∧
      (∀ i j k, b i j ⬝ᵥ r k = if i = k then 1 else 0) ∧
      (∀ i j l, b i j ⬝ᵥ c l = if j = l then 1 else 0) := by
  obtain ⟨m', rfl⟩ := hme
  obtain ⟨n', rfl⟩ := hne
  rcases (show 4 ≤ m' + m' ∨ 4 ≤ n' + n' by omega) with h4 | h4
  · exact exists_row_col_pivots_of_four_le_row h4 (by omega) hb
  ·
    obtain ⟨c, r, hcsigned, hrsigned, hc, hr, hcr, hcdot, hrdot⟩ :=
      exists_row_col_pivots_of_four_le_row h4 (by omega) hb.transpose
    exact ⟨r, c, hrsigned, hcsigned, hr, hc, fun i j => Ne.symm (hcr j i),
      fun i j k => hrdot j i k, fun i j l => hcdot j i l⟩

end CFSG.FeitThompson
