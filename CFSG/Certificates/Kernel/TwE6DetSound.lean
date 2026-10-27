module

public import Certificates.Data.Kernel.TwE6Det.Defs
public import Certificates.Data.TwE6Q2Determinants
public import CFSG.Certificates.Kernel.E6WKSound
public import CFSG.LieType.SeitzGeneration.ExcTorusUntw
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.Data.ZMod.Basic
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

set_option exponentiation.threshold 4096

public section

universe u

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.HardMathSupport.Timmesfeld.Steinberg Certificates.TwE6Q2Determinants
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular
open scoped Matrix

theorem e6Rho_apply_apply (k : Fin Tag.E6.rank) : e6Rho (e6Rho k) = k := by
  revert k
  decide

theorem charMatrix_eq {t : List ℕ} {v : WeylGroup Tag.E6} (hrep : e6Certificate.Represents t v)
    {M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ}
    (hv : ∀ x, v • x = M *ᵥ permLattice e6Rho x) :
    charMatrix t = M - (2 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) := by
  ext i k
  have h1 : (v • (Pi.single (e6Rho k) 1 : Fin Tag.E6.rank → ℤ)) i = M i k := by
    rw [hv, permLattice_single, e6Rho_apply_apply, Matrix.mulVec_single_one]
    rfl
  rw [charMatrix, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, ← h1,
    ← (hrep.2 (e6Rho k)).2]
  by_cases h : i = k <;> simp [h]

end CFSG.StandardType.TableCRes

namespace CFSG.KC.TwE6Det

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.StandardType.TwE6RootKill CFSG.KC.E6WK Certificates.TwE6Q2Determinants
  CFSG.StandardType.TableCRes CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular CFSG.RankThree.E6
open scoped Matrix

theorem nland (x n : ℕ) : Nat.land x (2 ^ n - 1) = x % 2 ^ n := Nat.and_two_pow_sub_one_eq_mod x n

theorem nshr (x n : ℕ) : Nat.shiftRight x n = x / 2 ^ n := Nat.shiftRight_eq_div_pow x n

theorem nshl (x n : ℕ) : Nat.shiftLeft x n = x * 2 ^ n := Nat.shiftLeft_eq x n

theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem nadd (a b : ℕ) : Nat.add a b = a + b := rfl

theorem letN_eq {α : Sort u} (y : ℕ) (k : ℕ → α) : letN y k = k y := by
  cases y <;> rfl

theorem lnT_eq (T L : ℕ) : lnT T L = T / 2 ^ (64 + 32 * L) % 2 ^ 32 := by
  change (T >>> (64 + 32 * L)) &&& (2 ^ 32 - 1) = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem lnT_lt (T L : ℕ) : lnT T L < 2 ^ 32 := by
  rw [lnT_eq]
  exact Nat.mod_lt _ (by positivity)

theorem lnT_salt {s X : ℕ} (hs : s < 2 ^ 64) (L : ℕ) :
    lnT (s + 2 ^ 64 * X) L = X / 2 ^ (32 * L) % 2 ^ 32 := by
  rw [lnT_eq, pow_add, ← Nat.div_div_eq_div_mul, mul_comm (2 ^ 64) X,
    Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hs, zero_add]

theorem sum_lt {w N : ℕ} {x : ℕ → ℕ} (hx : ∀ L < N, x L < 2 ^ w) :
    ∑ L ∈ Finset.range N, x L * 2 ^ (w * L) < 2 ^ (w * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih fun L hL => hx L (by omega)
    have h2 : x N + 1 ≤ 2 ^ w := hx N (by omega)
    calc _ < 2 ^ (w * N) + x N * 2 ^ (w * N) := Nat.add_lt_add_right h1 _
      _ = (x N + 1) * 2 ^ (w * N) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * N) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (w * (N + 1)) := by rw [← pow_add]; ring_nf

theorem sum_lane {w N : ℕ} {x : ℕ → ℕ} (hx : ∀ L < N, x L < 2 ^ w) (L0 : ℕ) :
    (∑ L ∈ Finset.range N, x L * 2 ^ (w * L)) / 2 ^ (w * L0) % 2 ^ w =
      if L0 < N then x L0 else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hx' : ∀ L < N, x L < 2 ^ w := fun L hL => hx L (by omega)
    have hlt := sum_lt hx'
    have hlt' := sum_lt hx
    rcases lt_trichotomy L0 N with h | h | h
    · obtain ⟨d, rfl⟩ : ∃ d, N = L0 + 1 + d := ⟨N - L0 - 1, by omega⟩
      have e : x (L0 + 1 + d) * 2 ^ (w * (L0 + 1 + d)) =
          2 ^ w * (x (L0 + 1 + d) * 2 ^ (w * d)) * 2 ^ (w * L0) := by ring
      rw [Finset.sum_range_succ, e, Nat.add_mul_div_right _ _ (by positivity),
        Nat.add_mul_mod_self_left, ih hx', if_pos h, if_pos (by omega)]
    · subst h
      rw [Finset.sum_range_succ, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt,
        zero_add, Nat.mod_eq_of_lt (hx L0 (by omega)), if_pos (by omega)]
    · rw [Nat.div_eq_of_lt (lt_of_lt_of_le hlt'
        (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h))), Nat.zero_mod,
        if_neg (by omega)]

theorem lane_add {X d m : ℕ} (hX : X / 2 ^ (32 * m) % 2 ^ 32 = 0) (hd : d < 2 ^ 32) (L : ℕ) :
    (X + d * 2 ^ (32 * m)) / 2 ^ (32 * L) % 2 ^ 32 =
      if L = m then d else X / 2 ^ (32 * L) % 2 ^ 32 := by
  obtain ⟨lo, h, hlo, rfl⟩ : ∃ lo h, lo < 2 ^ (32 * m) ∧ X = lo + 2 ^ (32 * m) * (2 ^ 32 * h) := by
    refine ⟨X % 2 ^ (32 * m), X / 2 ^ (32 * m) / 2 ^ 32, Nat.mod_lt _ (by positivity), ?_⟩
    have h1 := Nat.mod_add_div X (2 ^ (32 * m))
    have h2 := Nat.mod_add_div (X / 2 ^ (32 * m)) (2 ^ 32)
    rw [hX, zero_add] at h2
    rw [h2]
    exact h1.symm
  rcases lt_trichotomy L m with hL | rfl | hL
  · obtain ⟨e, rfl⟩ : ∃ e, m = L + 1 + e := ⟨m - L - 1, by omega⟩
    have he : d * 2 ^ (32 * (L + 1 + e)) = 2 ^ 32 * (d * 2 ^ (32 * e)) * 2 ^ (32 * L) := by ring
    rw [if_neg (by omega), he, Nat.add_mul_div_right _ _ (by positivity),
      Nat.add_mul_mod_self_left]
  · have he : lo + 2 ^ (32 * L) * (2 ^ 32 * h) + d * 2 ^ (32 * L) =
        lo + (2 ^ 32 * h + d) * 2 ^ (32 * L) := by ring
    rw [if_pos rfl, he, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
  · obtain ⟨e, rfl⟩ : ∃ e, L = m + 1 + e := ⟨L - m - 1, by omega⟩
    have hP : (2 : ℕ) ^ (32 * (m + 1 + e)) = 2 ^ (32 * (m + 1)) * 2 ^ (32 * e) := by
      rw [← pow_add]; ring_nf
    have h1 : lo + 2 ^ (32 * m) * (2 ^ 32 * h) + d * 2 ^ (32 * m) =
        (lo + d * 2 ^ (32 * m)) + h * 2 ^ (32 * (m + 1)) := by ring
    have h2 : lo + 2 ^ (32 * m) * (2 ^ 32 * h) = lo + h * 2 ^ (32 * (m + 1)) := by ring
    have hb : lo + d * 2 ^ (32 * m) < 2 ^ (32 * (m + 1)) := by
      have : d * 2 ^ (32 * m) + 2 ^ (32 * m) ≤ 2 ^ 32 * 2 ^ (32 * m) := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hd
      have e2 : (2 : ℕ) ^ (32 * (m + 1)) = 2 ^ 32 * 2 ^ (32 * m) := by rw [← pow_add]; ring_nf
      omega
    have hb' : lo < 2 ^ (32 * (m + 1)) :=
      lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [if_neg (by omega), h1, h2, hP, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_div_right _ _ (by positivity),
      Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hb']

theorem lnT_step {T S d : ℕ} (h0 : lnT T (72 + S) = 0) (hd : d < 2 ^ 32) (L : ℕ) :
    lnT (T - T % 2 ^ 64 + ((T % 2 ^ 64 * 6364136223846793005 + (d + S)) % 2 ^ 64 +
      d <<< (64 + 32 * (72 + S)))) L = if L = 72 + S then d else lnT T L := by
  have hTL : ∀ L, lnT T L = T / 2 ^ 64 / 2 ^ (32 * L) % 2 ^ 32 := fun L => by
    conv_lhs => rw [← Nat.mod_add_div T (2 ^ 64)]
    exact lnT_salt (Nat.mod_lt _ (by norm_num)) L
  have hsub : T - T % 2 ^ 64 = 2 ^ 64 * (T / 2 ^ 64) := by
    have := Nat.mod_add_div T (2 ^ 64)
    omega
  have e1 : T - T % 2 ^ 64 + ((T % 2 ^ 64 * 6364136223846793005 + (d + S)) % 2 ^ 64 +
      d <<< (64 + 32 * (72 + S))) = (T % 2 ^ 64 * 6364136223846793005 + (d + S)) % 2 ^ 64 +
        2 ^ 64 * (T / 2 ^ 64 + d * 2 ^ (32 * (72 + S))) := by
    rw [Nat.shiftLeft_eq, pow_add, hsub]
    ring
  have hz : T / 2 ^ 64 / 2 ^ (32 * (72 + S)) % 2 ^ 32 = 0 := by rw [← hTL, h0]
  rw [e1, lnT_salt (Nat.mod_lt _ (by norm_num)), lane_add hz hd, hTL]

@[expose] def bA (vp k r i : ℕ) : ℕ := (crd vp r i + 2 ^ 32 - if i = k then 10 else 8) % 2 ^ 32

@[expose] def bB (vp k r i : ℕ) : ℕ := ((if i = k then 10 else 8) + 2 ^ 32 - crd vp r i) % 2 ^ 32

theorem foldr_two (a b : ℕ → ℕ) : ∀ N c, (List.range N).foldr
    (fun i acc => acc + a i * 2 ^ (32 * i) + b i * 2 ^ (192 + 32 * i)) c =
    c + ∑ i ∈ Finset.range N, a i * 2 ^ (32 * i) + 2 ^ 192 * ∑ i ∈ Finset.range N, b i * 2 ^ (32 * i)
  | 0, c => by simp
  | N + 1, c => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_two a b N,
      Finset.sum_range_succ, Finset.sum_range_succ, pow_add]
    ring

theorem blk_eq (vp k r : ℕ) : blk vp k r = ∑ i ∈ Finset.range 6, bA vp k r i * 2 ^ (32 * i) +
    2 ^ 192 * ∑ i ∈ Finset.range 6, bB vp k r i * 2 ^ (32 * i) := by
  have h := foldr_two (bA vp k r) (bB vp k r) 6 0
  rw [zero_add] at h
  exact h

theorem sumA_lt (vp k r : ℕ) : ∑ i ∈ Finset.range 6, bA vp k r i * 2 ^ (32 * i) < 2 ^ 192 :=
  sum_lt (w := 32) (N := 6) fun _ _ => Nat.mod_lt _ (by positivity)

theorem sumB_lt (vp k r : ℕ) : ∑ i ∈ Finset.range 6, bB vp k r i * 2 ^ (32 * i) < 2 ^ 192 :=
  sum_lt (w := 32) (N := 6) fun _ _ => Nat.mod_lt _ (by positivity)

theorem blk_lt (vp k r : ℕ) : blk vp k r < 2 ^ 384 := by
  rw [blk_eq]
  have h1 := sumA_lt vp k r
  have h2 := sumB_lt vp k r
  have : 2 ^ 192 * ∑ i ∈ Finset.range 6, bB vp k r i * 2 ^ (32 * i) + 2 ^ 192 ≤ 2 ^ 384 := by
    calc _ = 2 ^ 192 * (∑ i ∈ Finset.range 6, bB vp k r i * 2 ^ (32 * i) + 1) := by ring
      _ ≤ 2 ^ 192 * 2 ^ 192 := Nat.mul_le_mul_left _ h2
      _ = 2 ^ 384 := by rw [← pow_add]
  omega

theorem rt_foldr (vp : ℕ) : ∀ N c, (List.range N).foldr (fun b acc =>
    letN (blk vp (b / 72) (b % 72)) fun x => letN acc fun a => a + x * 2 ^ (384 * b)) c =
    c + ∑ b ∈ Finset.range N, blk vp (b / 72) (b % 72) * 2 ^ (384 * b)
  | 0, c => by simp
  | N + 1, c => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, rt_foldr vp N,
      Finset.sum_range_succ, letN_eq, letN_eq]
    ring

theorem rt_block (vp : ℕ) {k r : ℕ} (hk : k < 6) (hr : r < 72) :
    rt vp / 2 ^ (384 * (72 * k + r)) % 2 ^ 384 = blk vp k r := by
  unfold rt
  rw [rt_foldr, zero_add, sum_lane (fun _ _ => blk_lt _ _ _), if_pos (by omega)]
  congr 1 <;> omega

@[expose] def rIdx (p v k : ℕ) : ℕ := lane p (lane v (wkRho.getD k 0))

@[expose] def xL (vp p v L : ℕ) : ℕ :=
  if L < 36 then bA vp (L / 6) (rIdx p v (L / 6)) (L % 6)
  else if L < 72 then bB vp ((L - 36) / 6) (rIdx p v ((L - 36) / 6)) ((L - 36) % 6) else 1

theorem tab_foldr (RT p v : ℕ) : ∀ N c, (List.range N).foldr (fun k acc =>
    letN (Nat.land (Nat.shiftRight RT
      (Nat.mul 384 (Nat.add (Nat.mul 72 k) (lane p (lane v (wkRho.getD k 0))))))
      (2 ^ 384 - 1)) fun b =>
    letN acc fun a =>
      a + Nat.shiftLeft (Nat.land b (2 ^ 192 - 1)) (64 + 192 * k) +
        Nat.shiftLeft (Nat.shiftRight b 192) (64 + 1152 + 192 * k)) c =
    c + ∑ k ∈ Finset.range N,
      (RT / 2 ^ (384 * (72 * k + rIdx p v k)) % 2 ^ 384 % 2 ^ 192 * 2 ^ (64 + 192 * k) +
        RT / 2 ^ (384 * (72 * k + rIdx p v k)) % 2 ^ 384 / 2 ^ 192 * 2 ^ (64 + 1152 + 192 * k))
  | 0, c => by simp
  | N + 1, c => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, tab_foldr RT p v N,
      Finset.sum_range_succ, letN_eq, letN_eq]
    simp only [nland, nshr, nshl, nmul, nadd]
    unfold rIdx
    ring

theorem tabA_eq {vp p v : ℕ} (hr : ∀ k < 6, rIdx p v k < 72) :
    tabA (rt vp) p v = salt0 p v + 2 ^ 64 * ∑ L ∈ Finset.range 73, xL vp p v L * 2 ^ (32 * L) := by
  unfold tabA
  rw [tab_foldr]
  have hb : ∀ k < 6, rt vp / 2 ^ (384 * (72 * k + rIdx p v k)) % 2 ^ 384 =
      ∑ i ∈ Finset.range 6, bA vp k (rIdx p v k) i * 2 ^ (32 * i) +
        2 ^ 192 * ∑ i ∈ Finset.range 6, bB vp k (rIdx p v k) i * 2 ^ (32 * i) := fun k hk => by
    rw [rt_block vp hk (hr k hk), blk_eq]
  have hlo : ∀ k < 6, rt vp / 2 ^ (384 * (72 * k + rIdx p v k)) % 2 ^ 384 % 2 ^ 192 =
      ∑ i ∈ Finset.range 6, bA vp k (rIdx p v k) i * 2 ^ (32 * i) := fun k hk => by
    rw [hb k hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (sumA_lt _ _ _)]
  have hhi : ∀ k < 6, rt vp / 2 ^ (384 * (72 * k + rIdx p v k)) % 2 ^ 384 / 2 ^ 192 =
      ∑ i ∈ Finset.range 6, bB vp k (rIdx p v k) i * 2 ^ (32 * i) := fun k hk => by
    rw [hb k hk, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (sumA_lt _ _ _),
      zero_add]
  rw [Finset.sum_congr rfl fun k hk => by
    rw [hlo k (Finset.mem_range.1 hk), hhi k (Finset.mem_range.1 hk)]]
  simp only [xL, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

theorem lnT_tabA {vp p v : ℕ} (hr : ∀ k < 6, rIdx p v k < 72) (L : ℕ) :
    lnT (tabA (rt vp) p v) L = if L < 73 then xL vp p v L else 0 := by
  have hs : salt0 p v < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  rw [tabA_eq hr, lnT_salt hs, sum_lane]
  intro L _
  unfold xL
  split_ifs
  · exact Nat.mod_lt _ (by positivity)
  · exact Nat.mod_lt _ (by positivity)
  · norm_num

section Minors

variable {R : Type*} [CommRing R]

noncomputable def Dl (A : Matrix (Fin 6) (Fin 6) R) (n : ℕ) (l : List (Fin 6)) : R :=
  (Matrix.of fun i j : Fin n => A ⟨(6 - n + i) % 6, Nat.mod_lt _ (by norm_num)⟩ (l.getD j 0)).det

theorem getD_eraseIdx (l : List (Fin 6)) (j k : ℕ) :
    (l.eraseIdx j).getD k 0 = l.getD (if k < j then k else k + 1) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
  split_ifs <;> rfl

theorem val_succAbove {m : ℕ} (j : Fin (m + 1)) (k : Fin m) :
    (j.succAbove k : ℕ) = if (k : ℕ) < j then (k : ℕ) else (k : ℕ) + 1 := by
  rcases lt_or_ge (k : ℕ) j with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; exact h), if_pos h]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; exact h), if_neg (by omega)]
    rfl

theorem Dl_succ (A : Matrix (Fin 6) (Fin 6) R) {m : ℕ} (hm : m + 1 ≤ 6) (l : List (Fin 6)) :
    Dl A (m + 1) l = ∑ j : Fin (m + 1),
      (-1) ^ (j : ℕ) * A ⟨5 - m, by omega⟩ (l.getD j 0) * Dl A m (l.eraseIdx j) := by
  unfold Dl
  rw [Matrix.det_succ_row_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hrow : (⟨(6 - (m + 1) + ((0 : Fin (m + 1)) : ℕ)) % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6) =
      ⟨5 - m, by omega⟩ := Fin.ext (by simp only [Fin.val_zero]; omega)
  simp only [Matrix.of_apply, hrow]
  congr 2
  ext i k
  simp only [Matrix.submatrix_apply, Matrix.of_apply, getD_eraseIdx, val_succAbove]
  congr 1
  exact Fin.ext (by simp only [Fin.val_succ]; omega)

theorem Dl_zero (A : Matrix (Fin 6) (Fin 6) R) (l : List (Fin 6)) : Dl A 0 l = 1 :=
  Matrix.det_isEmpty

end Minors

@[expose] def bitsOf (S : ℕ) : List (Fin 6) :=
  ((List.range 6).filter fun j => S.testBit j).map fun j => ⟨j % 6, Nat.mod_lt _ (by decide)⟩

@[expose] def termsOf (S : ℕ) : List ℕ :=
  (List.range (bitsOf S).length).map fun j =>
    36 * (j % 2) + 6 * (6 - (bitsOf S).length) + ((bitsOf S).getD j 0 : ℕ) +
      128 * (S - 2 ^ ((bitsOf S).getD j 0 : ℕ))

@[expose] def schOK : List (ℕ × List ℕ) → List ℕ → Bool
  | [], _ => true
  | (S, ts) :: sc, done =>
    decide (0 < S) && decide (S < 64) && !done.contains S && decide (0 < (bitsOf S).length) &&
      ts == termsOf S &&
      (List.range (bitsOf S).length).all (fun j =>
        ((S - 2 ^ ((bitsOf S).getD j 0 : ℕ)) == 0 || done.contains (S - 2 ^ ((bitsOf S).getD j 0 : ℕ)))
          && bitsOf (S - 2 ^ ((bitsOf S).getD j 0 : ℕ)) == (bitsOf S).eraseIdx j) &&
      schOK sc (S :: done)

theorem schOK_sch : schOK sch [] = true := by
  decide +kernel

theorem mem_sch_63 : 63 ∈ sch.map Prod.fst := by
  decide +kernel

theorem bitsOf_63 : bitsOf 63 = [0, 1, 2, 3, 4, 5] := by
  decide +kernel

abbrev Z := ZMod (2 ^ 32)

noncomputable def aval (A : Matrix (Fin 6) (Fin 6) Z) (e : ℕ) : Z :=
  (-1) ^ (e / 36) * A ⟨e % 36 / 6, by omega⟩ ⟨e % 6, by omega⟩

noncomputable def DS (A : Matrix (Fin 6) (Fin 6) Z) (S : ℕ) : Z := Dl A (bitsOf S).length (bitsOf S)

def Inv (A : Matrix (Fin 6) (Fin 6) Z) (T : ℕ) (done : List ℕ) : Prop :=
  (∀ e < 72, (lnT T e : Z) = aval A e) ∧
  (∀ S, (S = 0 ∨ S ∈ done) → (lnT T (72 + S) : Z) = DS A S) ∧
  (∀ S, 0 < S → S < 64 → S ∉ done → lnT T (72 + S) = 0)

theorem dotT_cast (T : ℕ) : ∀ ts : List ℕ,
    (dotT T ts : Z) = (ts.map fun t => (lnT T (t % 128) : Z) * lnT T (72 + t / 128)).sum
  | [] => by simp [dotT]
  | t :: ts => by
    rw [dotT, letN_eq, List.map_cons, List.sum_cons, ← dotT_cast T ts]
    change ((dotT T ts + lnT T (t % 128) * lnT T (72 + t / 128) : ℕ) : Z) = _
    push_cast
    ring

theorem sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range f n,
      Finset.sum_range_succ]
    simp

theorem length_bitsOf (S : ℕ) : (bitsOf S).length ≤ 6 := by
  unfold bitsOf
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem aval_eq (A : Matrix (Fin 6) (Fin 6) Z) {s r c : ℕ} (hs : s < 2) (hr : r < 6)
    (hc : c < 6) : aval A (36 * s + 6 * r + c) = (-1) ^ s * A ⟨r, hr⟩ ⟨c, hc⟩ := by
  have e1 : (36 * s + 6 * r + c) / 36 = s := by omega
  unfold aval
  rw [e1]
  congr 2
  · exact Fin.ext (by change (36 * s + 6 * r + c) % 36 / 6 = r; omega)
  · exact Fin.ext (by change (36 * s + 6 * r + c) % 6 = c; omega)

theorem inv_step {A : Matrix (Fin 6) (Fin 6) Z} {T S : ℕ} {done : List ℕ}
    (hI : Inv A T done) (hS0 : 0 < S) (hS : S < 64) (hnd : S ∉ done) (hn : 0 < (bitsOf S).length)
    (hj : ∀ j < (bitsOf S).length,
      (S - 2 ^ ((bitsOf S).getD j 0 : ℕ) = 0 ∨ S - 2 ^ ((bitsOf S).getD j 0 : ℕ) ∈ done) ∧
        bitsOf (S - 2 ^ ((bitsOf S).getD j 0 : ℕ)) = (bitsOf S).eraseIdx j) :
    Inv A (T - T % 2 ^ 64 + ((T % 2 ^ 64 * 6364136223846793005 +
      (dotT T (termsOf S) % 2 ^ 32 + S)) % 2 ^ 64 +
        (dotT T (termsOf S) % 2 ^ 32) <<< (64 + 32 * (72 + S)))) (S :: done) := by
  obtain ⟨hA, hD, hZ⟩ := hI
  have h0 : lnT T (72 + S) = 0 := hZ S hS0 hS hnd
  have hd : dotT T (termsOf S) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hstep := lnT_step h0 hd
  refine ⟨fun e he => ?_, fun S0 hS0' => ?_, fun S0 h1 h2 h3 => ?_⟩
  · rw [hstep, if_neg (by omega)]
    exact hA e he
  · by_cases hSS : S0 = S
    · subst hSS
      rw [hstep, if_pos rfl, ZMod.natCast_mod, dotT_cast]
      set l := bitsOf S0 with hl
      obtain ⟨m, hm⟩ : ∃ m, l.length = m + 1 := ⟨l.length - 1, by omega⟩
      have hm6 : m + 1 ≤ 6 := by
        rw [← hm]
        exact length_bitsOf S0
      unfold DS
      rw [← hl, hm, Dl_succ _ hm6, Fin.sum_univ_eq_sum_range
        (fun j => (-1) ^ j * A ⟨5 - m, by omega⟩ (l.getD j 0) * Dl A m (l.eraseIdx j)),
        termsOf, ← hl, List.map_map, sum_map_range, hm]
      refine Finset.sum_congr rfl fun j hj' => ?_
      have hjm := Finset.mem_range.1 hj'
      have hlj : ((l.getD j 0 : Fin 6) : ℕ) < 6 := (l.getD j 0).2
      obtain ⟨hj1, hj2⟩ := hj j (by omega)
      simp only [Function.comp_apply]
      have hmod : (36 * (j % 2) + 6 * (6 - (m + 1)) + ((l.getD j 0 : Fin 6) : ℕ) +
          128 * (S0 - 2 ^ ((l.getD j 0 : Fin 6) : ℕ))) % 128 =
          36 * (j % 2) + 6 * (5 - m) + ((l.getD j 0 : Fin 6) : ℕ) := by omega
      have hdiv : (36 * (j % 2) + 6 * (6 - (m + 1)) + ((l.getD j 0 : Fin 6) : ℕ) +
          128 * (S0 - 2 ^ ((l.getD j 0 : Fin 6) : ℕ))) / 128 =
          S0 - 2 ^ ((l.getD j 0 : Fin 6) : ℕ) := by omega
      rw [hmod, hdiv, hA _ (by omega), hD _ hj1,
        aval_eq A (Nat.mod_lt _ (by norm_num)) (by omega : 5 - m < 6) hlj, Fin.eta, DS, hj2,
        List.length_eraseIdx_of_lt (by omega), hm, Nat.add_sub_cancel,
        ← neg_one_pow_eq_pow_mod_two]
    · rw [hstep, if_neg (by omega)]
      rcases hS0' with h | h
      · exact hD S0 (Or.inl h)
      · exact hD S0 (Or.inr ((List.mem_cons.1 h).resolve_left hSS))
  · rw [hstep, if_neg (by
      intro h
      exact h3 (by rw [List.mem_cons]; left; omega))]
    exact hZ S0 h1 h2 fun h => h3 (List.mem_cons_of_mem _ h)

theorem inv_stepS {A : Matrix (Fin 6) (Fin 6) Z} : ∀ (sc : List (ℕ × List ℕ)) (done : List ℕ)
    (T : ℕ), schOK sc done = true → Inv A T done →
      Inv A (stepS T sc) ((sc.map Prod.fst).reverse ++ done)
  | [], done, T, _, hI => by simpa [stepS] using hI
  | (S, ts) :: sc, done, T, h, hI => by
    simp only [schOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hS0, hS⟩, hnd⟩, hn⟩, hts⟩, hj⟩, hrest⟩ := h
    subst hts
    have hnd' : S ∉ done := by simpa using hnd
    have hI' := inv_step hI hS0 hS hnd' hn fun j hj' => by
      obtain ⟨h1, h2⟩ := hj j hj'
      exact ⟨h1.imp id (fun h => by simpa using h), h2⟩
    have hI'' := inv_stepS sc (S :: done) _ hrest hI'
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    simp only [stepS, letN_eq]
    exact hI''

@[expose] def AZ (vp p v : ℕ) : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun k i => (crd vp (rIdx p v k) i : ℤ) - if (i : ℕ) = k then 10 else 8

theorem crd_lt (vp r i : ℕ) : crd vp r i < 16 := Nat.mod_lt _ (by norm_num)

theorem cast_wrap {a b : ℕ} (hb : b ≤ 2 ^ 32) :
    (((a + 2 ^ 32 - b) % 2 ^ 32 : ℕ) : Z) = (a : Z) - (b : Z) := by
  rw [ZMod.natCast_mod, Nat.cast_sub (le_trans hb (Nat.le_add_left _ _)), Nat.cast_add,
    ZMod.natCast_self, add_zero]

theorem inv_tabA {vp p v : ℕ} (hr : ∀ k < 6, rIdx p v k < 72) :
    Inv ((AZ vp p v).map (Int.cast : ℤ → Z)) (tabA (rt vp) p v) [] := by
  refine ⟨fun e he => ?_, fun S hS => ?_, fun S h1 h2 _ => ?_⟩
  · rw [lnT_tabA hr, if_pos (by omega)]
    unfold xL aval
    simp only [Matrix.map_apply, AZ, Matrix.of_apply]
    by_cases h36 : e < 36
    · have e1 : e / 36 = 0 := by omega
      have e2 : e % 36 = e := by omega
      rw [if_pos h36, bA, cast_wrap (by split_ifs <;> norm_num), e1, pow_zero, one_mul]
      simp only [e2]
      split_ifs <;> push_cast <;> ring
    · have e1 : e / 36 = 1 := by omega
      have e2 : e % 36 = e - 36 := by omega
      have e3 : e % 6 = (e - 36) % 6 := by omega
      have hc := crd_lt vp (rIdx p v ((e - 36) / 6)) ((e - 36) % 6)
      rw [if_neg h36, if_pos he, bB, cast_wrap (by omega), e1, pow_one]
      simp only [e2, e3]
      split_ifs <;> push_cast <;> ring
  · have hS0 : S = 0 := hS.resolve_right (List.not_mem_nil)
    subst hS0
    have hb : bitsOf 0 = [] := by decide +kernel
    rw [lnT_tabA hr, if_pos (by omega)]
    unfold DS xL
    rw [hb, List.length_nil, Dl_zero]
    simp
  · rw [lnT_tabA hr, if_neg (by omega)]

theorem Dl_six (A : Matrix (Fin 6) (Fin 6) Z) : Dl A 6 [0, 1, 2, 3, 4, 5] = A.det := by
  unfold Dl
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem detS_cast {vp p v : ℕ} (hr : ∀ k < 6, rIdx p v k < 72) :
    (detS sch (tabA (rt vp) p v) : Z) = (((AZ vp p v).det : ℤ) : Z) := by
  have hI := inv_stepS sch [] _ schOK_sch (inv_tabA (vp := vp) hr)
  have h63 : 63 ∈ (sch.map Prod.fst).reverse ++ [] := by
    rw [List.append_nil, List.mem_reverse]
    exact mem_sch_63
  have h := hI.2.1 63 (Or.inr h63)
  have e : (135 : ℕ) = 72 + 63 := rfl
  have e6 : ([0, 1, 2, 3, 4, 5] : List (Fin 6)).length = 6 := rfl
  unfold detS
  rw [e, h, DS, bitsOf_63, e6, Dl_six]
  exact (RingHom.map_det (Int.castRingHom Z) (AZ vp p v)).symm

theorem abs_AZ (vp p v : ℕ) (k i : Fin 6) : |AZ vp p v k i| ≤ 10 := by
  have hc := crd_lt vp (rIdx p v k) i
  simp only [AZ, Matrix.of_apply]
  rw [abs_le]
  split_ifs <;> constructor <;> omega

theorem natAbs_det_lt (vp p v : ℕ) : ((AZ vp p v).det).natAbs < 2 ^ 31 := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := (10 : ℤ)) fun k i => by
    rw [AbsoluteValue.abs_apply]
    exact abs_AZ vp p v k i
  rw [AbsoluteValue.abs_apply, Fintype.card_fin] at h
  norm_num at h
  zify
  have h31 : (720000000 : ℤ) < 2 ^ 31 := by norm_num
  linarith

theorem absK_detS {vp p v : ℕ} (hr : ∀ k < 6, rIdx p v k < 72) :
    absK (detS sch (tabA (rt vp) p v)) = ((AZ vp p v).det).natAbs := by
  have hx : detS sch (tabA (rt vp) p v) < 2 ^ 32 := lnT_lt _ _
  have hmod : (detS sch (tabA (rt vp) p v) : ℤ) % 2 ^ 32 = (AZ vp p v).det % 2 ^ 32 := by
    have h : (((detS sch (tabA (rt vp) p v) : ℤ)) : Z) = (((AZ vp p v).det : ℤ) : Z) := by
      rw [Int.cast_natCast]
      exact detS_cast hr
    exact (ZMod.intCast_eq_intCast_iff' _ _ _).1 h
  have hb := natAbs_det_lt vp p v
  unfold absK
  simp only [Nat.reducePow, Int.reducePow] at *
  rcases Int.natAbs_eq (AZ vp p v).det with h | h <;> split_ifs <;> omega

theorem exists_tuple
    {vp ir rm : ℕ} {words : List (List ℕ)} {up vk : List ℕ}
    (htab : tabCheckWith vp ir rm = true) (hup : upCheckWith ir words up = true)
    (hk : kCheckWith up = true) (hv : vCheckWith ir vk (KTree.ofSorted vk) = true)
    (w : WeylGroup TwistTag.E6.tag) :
    ∃ p ∈ up, ∃ c ∈ vk, e6Certificate.Represents ((decodeT 6 c).map (lane p)) w := by
  obtain ⟨u, ω, hω, hupos, rfl⟩ := exists_decomp w
  obtain ⟨c, hc, hvrep⟩ := exists_vk htab hv ω hω
  obtain ⟨p, hp, hurep⟩ := exists_up hk u hupos
  obtain ⟨n, hn, hpn⟩ := List.getElem_of_mem hp
  simp only [upCheckWith, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at hup
  obtain ⟨hlen, hall⟩ := hup
  have hzip := hall (words[n]'(by rw [hlen]; exact hn), up[n]) (by
    rw [List.mem_iff_getElem]
    exact ⟨n, by rw [List.length_zip, hlen, min_self]; exact hn, by rw [List.getElem_zip]⟩)
  have hw6 : ∀ i ∈ words[n]'(by rw [hlen]; exact hn), i < 6 := hzip.1
  have hwp : wordPerm ir (words[n]'(by rw [hlen]; exact hn)) = up[n] := hzip.2
  obtain ⟨g, hg⟩ := exists_wordPerm_spec htab _ hw6
  rw [hwp, hpn] at hg
  have hug : u = g := by
    refine ext_single fun j => ?_
    have hj6 : (j : ℕ) < 6 := j.2
    have h1 := (hurep.2 j).2
    rw [getD_decodeT hj6, lane_mod_pow hj6] at h1
    rw [← h1, (hg j (by omega)).2, root_single]
  subst hug
  refine ⟨p, hp, c, hc, ?_⟩
  have hvlt := lt_of_represents hvrep
  have hvlen : (decodeT 6 c).length = 6 := length_decodeT 6 c
  refine ⟨by rw [List.length_map, hvlen]; rfl, fun j => ?_⟩
  have hj : (j : ℕ) < (decodeT 6 c).length := by rw [hvlen]; exact j.2
  have hget : ((decodeT 6 c).map (lane p)).getD j 0 = lane p ((decodeT 6 c).getD j 0) := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hj]
  have hy := hvlt _ (getD_mem' 0 hj)
  rw [hget]
  refine ⟨by rw [roots_length]; exact (hg _ hy).1, ?_⟩
  rw [(hg _ hy).2, (hvrep.2 j).2, mul_smul]

theorem rIdx_eq (p c : ℕ) (k : Fin TwistTag.E6.tag.rank) :
    rIdx p c k = ((decodeT 6 c).map (lane p)).getD (TwistTag.E6.perm k) 0 := by
  have h6 : ((TwistTag.E6.perm k : Fin _) : ℕ) < 6 := (TwistTag.E6.perm k).2
  have hlt : ((TwistTag.E6.perm k : Fin _) : ℕ) < (decodeT 6 c).length := by
    rw [length_decodeT]
    exact h6
  unfold rIdx
  rw [wkRho_getD k, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt),
    List.getElem_map, ← List.getD_eq_getElem _ 0 hlt]
  exact congrArg (lane p) (getD_decodeT h6).symm

theorem AZ_eq {vp ir rm : ℕ} (htab : tabCheckWith vp ir rm = true) {p c : ℕ}
    (hr : ∀ k < 6, rIdx p c k < 72) :
    AZ vp p c = (charMatrix ((decodeT 6 c).map (lane p)))ᵀ := by
  ext k i
  have hrk := hr k k.2
  have hroot := (tab_parts htab).1 _ hrk
  have hρ : e6Rho k = TwistTag.E6.perm k := rfl
  change AZ vp p c k i = e6Certificate.root (((decodeT 6 c).map (lane p)).getD (e6Rho k) 0) i -
    if i = k then 2 else 0
  simp only [AZ, Matrix.of_apply, hρ, ← rIdx_eq p c k,
    RootCertificate.root, decodeVec, crd, hroot, Fin.val_inj]
  split_ifs <;> ring

theorem okD_spec {d : ℕ} (h : okD d = true) : (13 ∣ d → d = 39) ∧ (19 ∣ d → d = 57) := by
  simp only [okD, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  omega

theorem mem_chunk {vk : List ℕ} {m : ℕ} (hm : m < vk.length) : vk[m] ∈ chunk vk (m / 128) := by
  have hq : m - 128 * (m / 128) < ((vk.drop (128 * (m / 128))).take 128).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have h := List.getElem_mem hq
  simp only [List.getElem_take, List.getElem_drop] at h
  have e : 128 * (m / 128) + (m - 128 * (m / 128)) = m := by omega
  simp only [e] at h
  exact h

theorem charpoly_two_of_checks
    {vp ir rm : ℕ} {words : List (List ℕ)} {up vk : List ℕ}
    (htab : tabCheckWith vp ir rm = true) (hup : upCheckWith ir words up = true)
    (hk : kCheckWith up = true) (hv : vCheckWith ir vk (KTree.ofSorted vk) = true)
    (hlen : up.length = 27) (hvk : vk.length ≤ 1920)
    (hch : ∀ i < 405, chkAt vp up vk i = true) (v : WeylGroup TwistTag.E6.tag)
    (M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ)
    (hvM : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x) :
    (13 ∣ (M.charpoly.eval (2 : ℤ)).natAbs → (M.charpoly.eval (2 : ℤ)).natAbs = 39) ∧
      (19 ∣ (M.charpoly.eval (2 : ℤ)).natAbs → (M.charpoly.eval (2 : ℤ)).natAbs = 57) := by
  obtain ⟨p, hp, c, hc, hrep⟩ := exists_tuple htab hup hk hv v
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hp
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
  have hr : ∀ k < 6, rIdx up[n] vk[m] k < 72 := fun k hk => by
    have e : rIdx up[n] vk[m] k = rIdx up[n] vk[m] ((⟨k, hk⟩ : Fin TwistTag.E6.tag.rank) : ℕ) :=
      rfl
    rw [e, rIdx_eq]
    have h := (hrep.2 (TwistTag.E6.perm ⟨k, hk⟩)).1
    rwa [roots_length] at h
  have hi := hch (15 * n + m / 128) (by omega)
  have e1 : (15 * n + m / 128) / 15 = n := by omega
  have e2 : (15 * n + m / 128) % 15 = m / 128 := by omega
  unfold chkAt at hi
  rw [letN_eq, e1, e2, List.getD_eq_getElem _ _ hn] at hi
  have hok := List.all_eq_true.1 hi _ (mem_chunk hm)
  have hdet : (AZ vp up[n] vk[m]).det = (charMatrix ((decodeT 6 vk[m]).map (lane up[n]))).det :=
    (congrArg Matrix.det (AZ_eq htab hr)).trans (Matrix.det_transpose _)
  have hord : (AZ vp up[n] vk[m]).det.natAbs = (M.charpoly.eval (2 : ℤ)).natAbs := by
    rw [hdet, charMatrix_eq hrep hvM, natAbs_eval_charpoly]
    rfl
  rw [absK_detS hr, hord] at hok
  exact okD_spec hok

end CFSG.KC.TwE6Det
