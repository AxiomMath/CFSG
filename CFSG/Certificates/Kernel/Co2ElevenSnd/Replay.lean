module

public import Certificates.Data.Kernel.Co2SmithS.Orb
public import CFSG.Certificates.Kernel.Spor.PK.BFS
import CFSG.Certificates.Kernel.Co2SmithS.BfsSound

public section

namespace CFSG.KC.Co2Eleven.Snd

open CFSG.KS.PK CFSG.KC.Co2SmithS

private theorem rec_facts {stepK : Nat → Nat → Nat} {ngen N start : Nat}
    {T PA LA M S : Nat → Nat} {TB : Nat → Nat → Nat} {k : Nat}
    (h : orbRecK stepK ngen N start T PA LA M S TB k = true) :
    (∀ j < ngen, TB k j < N ∧ stepK j (T k) = T (TB k j)) ∧
      M (k + 1) = (if k < M k then rowC PA LA TB ngen k (M k) else 0) ∧
      (k = 0 → T 0 = start ∧ PA 0 = 0 ∧ M 0 = 1) := by
  unfold orbRecK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩ := h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true h2, fun hk => ?_⟩
  · rw [List.all_eq_true] at h1
    have := h1 j (List.mem_range.2 hj)
    simp only [Bool.and_eq_true] at this
    exact ⟨of_decide_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩
  · subst hk
    rw [if_pos rfl] at h5
    simp only [Bool.and_eq_true] at h5
    obtain ⟨⟨⟨a, b⟩, -⟩, d⟩ := h5
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true d⟩

private def stR (T PA LB : Nat → Nat) (c : Nat) : BS :=
  ⟨(List.range c).map T, (List.range c).map PA, (List.range c).map LB⟩

private theorem stR_len (T PA LB : Nat → Nat) (c : Nat) : (stR T PA LB c).pts.length = c := by
  simp [stR]

private theorem stR_getD (T PA LB : Nat → Nat) {c k : Nat} (hk : k < c) :
    (stR T PA LB c).pts.getD k 0 = T k := by
  simp [stR, List.getD_eq_getElem?_getD, hk]

private theorem stR_succ (T PA LB : Nat → Nat) (c : Nat) :
    stR T PA LB (c + 1) =
      ⟨(stR T PA LB c).pts ++ [T c], (stR T PA LB c).par ++ [PA c], (stR T PA LB c).lab ++ [LB c]⟩ := by
  simp [stR, List.range_succ]

private theorem take_succ_getD {l : List Nat} {j : Nat} (hj : j < l.length) :
    l.take (j + 1) = l.take j ++ [l.getD j 0] := by
  rw [List.take_succ, List.getElem?_eq_getElem hj, Option.toList_some, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some]

private theorem row_run {F : Nat → Nat → Nat} {lv : List Nat} {N h c0 : Nat}
    {T PA LA LB : Nat → Nat} {TB : Nat → Nat → Nat}
    (hinj : ∀ a < N, ∀ b < N, T a = T b → a = b)
    (hpt : ∀ j < lv.length, TB h j < N ∧ F (lv.getD j 0) (T h) = T (TB h j))
    (hlb : ∀ k < N, 0 < k → LB k = lv.getD (LA k) 0)
    (hr : rowC PA LA TB lv.length h c0 ≠ 0) (hrN : rowC PA LA TB lv.length h c0 ≤ N) :
    ∀ j ≤ lv.length, (lv.take j).foldl (BS.letter F h (T h)) (stR T PA LB c0) =
      stR T PA LB (pcC PA LA TB h c0 j)
  | 0, _ => rfl
  | j + 1, hj => by
    have hre : rowC PA LA TB lv.length h c0 = pcC PA LA TB h c0 lv.length := rfl
    rw [hre] at hr hrN
    rw [take_succ_getD (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil,
      row_run hinj hpt hlb (by rw [hre]; exact hr) (by rw [hre]; exact hrN) j (by omega),
      pcC_succ]
    have hle1 := pcC_le (PA := PA) (LA := LA) (TB := TB) (h := h) (c := c0)
      (lv.length - (j + 1)) (j + 1) (by rw [Nat.add_sub_cancel' hj]; exact hr)
    rw [Nat.add_sub_cancel' hj] at hle1
    have hv : stepC PA LA h j (pcC PA LA TB h c0 j) (TB h j) ≠ 0 := by
      rw [← pcC_succ]
      exact hle1.1
    have hvN : stepC PA LA h j (pcC PA LA TB h c0 j) (TB h j) ≤ N := by
      rw [← pcC_succ]
      omega
    obtain ⟨haN, hy⟩ := hpt j (by omega)
    generalize pcC PA LA TB h c0 j = c at hv hvN
    obtain ⟨hc0, hcase⟩ := stepC_spec hv
    unfold BS.letter
    rw [hy]
    rcases hcase with ⟨hlt, e⟩ | ⟨heq, hpa, hla, e⟩
    · have hmem : T (TB h j) ∈ (stR T PA LB c).pts := by
        simp only [stR, List.mem_map, List.mem_range]
        exact ⟨TB h j, hlt, rfl⟩
      rw [if_pos hmem, e]
    · have hcN : c < N := by omega
      have hnm : T (TB h j) ∉ (stR T PA LB c).pts := by
        simp only [stR, List.mem_map, List.mem_range, not_exists, not_and]
        intro a ha e'
        rw [heq] at e'
        have := hinj a (by omega) c hcN e'
        omega
      rw [if_neg hnm, e, stR_succ, heq, hpa, hlb c hcN (by omega), hla]

theorem run_of_rec {F : Nat → Nat → Nat} {lv : List Nat} {n N r : Nat}
    {T PA LA LB M S : Nat → Nat} {TB : Nat → Nat → Nat} (hN : 0 < N) (hNn : N ≤ n)
    (hrec : ∀ k < N,
      orbRecK (fun j x => F (lv.getD j 0) x) lv.length N r T PA LA M S TB k = true)
    (hlast : M N = N) (hinj : ∀ a < N, ∀ b < N, T a = T b → a = b)
    (hlb : ∀ k < N, LB k = if k = 0 then 0 else lv.getD (LA k) 0) :
    BS.run F lv n r = ⟨(List.range N).map T, (List.range N).map PA, (List.range N).map LB⟩ := by
  have hF := fun k (hk : k < N) => rec_facts (hrec k hk)
  obtain ⟨hT0, hP0, hM0⟩ := (hF 0 hN).2.2 rfl
  have C : Counts PA LA M TB lv.length N := ⟨hN, hM0, fun h hh => (hF h hh).2.1, hlast⟩
  obtain ⟨hcn, hlt⟩ := C.facts
  have hlb' : ∀ k < N, 0 < k → LB k = lv.getD (LA k) 0 := fun k hk hk0 => by
    rw [hlb k hk, if_neg (by omega)]
  have hinit : (⟨[r], [0], [0]⟩ : BS) = stR T PA LB 1 := by
    rw [show stR T PA LB 1 = ⟨[T 0], [PA 0], [LB 0]⟩ from rfl, hT0, hP0, hlb 0 hN, if_pos rfl]
  have key : ∀ k ≤ n, (List.range k).foldl (BS.step F lv) ⟨[r], [0], [0]⟩ =
      stR T PA LB (M (min k N)) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.zero_min, hM0]
      exact hinit
    | succ k ih =>
      intro hk
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      unfold BS.step
      by_cases hkN : k < N
      · rw [Nat.min_eq_left (by omega : k ≤ N), Nat.min_eq_left (by omega : k + 1 ≤ N),
          stR_len, if_pos (hlt k hkN).1, stR_getD _ _ _ (hlt k hkN).1, (hlt k hkN).2]
        have hr := (hcn (k + 1) (by omega)).1
        have hrN := (hcn (k + 1) (by omega)).2
        rw [(hlt k hkN).2] at hr hrN
        have := row_run hinj (hF k hkN).1 hlb' hr hrN lv.length (Nat.le_refl _)
        rw [List.take_length] at this
        exact this
      · rw [Nat.min_eq_right (by omega : N ≤ k), Nat.min_eq_right (by omega : N ≤ k + 1), hlast,
          stR_len, if_neg hkN]
  have := key n (Nat.le_refl _)
  rw [Nat.min_eq_right hNn, hlast] at this
  exact this

end CFSG.KC.Co2Eleven.Snd

end
