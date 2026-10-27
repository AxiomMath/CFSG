module

public import Certificates.Certificate38600

public section

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6

theorem tvListCheck_holds : chkTvList = true :=
  Certificates.certificate38600.1

theorem tvImgCheck_holds : chkTvImg = true :=
  Certificates.certificate38600.2

structure TvListFacts : Prop where
  size : tvList.size = 1953
  entry : ∀ k < 1953, (tvPair k).1 < 64 ∧ (tvPair k).2 < 64 ∧ (tvPair k).1 ≠ 0 ∧
    (tvPair k).2 ≠ 0 ∧ form (tvPair k).2 (tvPair k).1 = false ∧
      tvIdxTab[64 * (tvPair k).1 + (tvPair k).2]! = k
  idxTab : ∀ n < 4096, tvIdxTab[n]! ≤ 1953 ∧
    (tvIdxTab[n]! = 1953 ∨ tvPair tvIdxTab[n]! = (n / 64, n % 64))
  surj : ∀ n < 4096, n / 64 ≠ 0 → n % 64 ≠ 0 → form (n % 64) (n / 64) = false →
    tvIdxTab[n]! < 1953

theorem tvListFacts : TvListFacts := by
  have h := tvListCheck_holds
  simp only [chkTvList, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true', Bool.or_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun k hk => ?_, fun n hn => ?_, fun n hn h0 h1' hf => ?_⟩
  · obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h2 k hk
    exact ⟨a, b, c, d, e, f⟩
  · obtain ⟨a, b⟩ := h3 n hn
    refine ⟨a, ?_⟩
    rcases b with b | b
    · exact Or.inl b
    · exact Or.inr (by simpa using b)
  · have := h4 n hn
    rcases this with ((h | h) | h) | h
    · exact absurd (by simpa using h) h0
    · exact absurd (by simpa using h) h1'
    · exact absurd h (by simp [hf])
    · exact h

theorem tvTab_get {j a : Nat} (hj : j < 1953) (ha : a < 1953) : tvTab[j]![a]! = tvImg j a := by
  simp [tvTab, getElem!_pos, hj, ha]

theorem tvImg_lt {j a : Nat} (hj : j < 1953) (ha : a < 1953) :
    tvImg j a < 1953 := by
  have h := tvImgCheck_holds
  simp only [chkTvImg, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  have := (h j hj a ha).1
  rwa [tvTab_get hj ha] at this

theorem tvImg_tvImg {j a : Nat} (hj : j < 1953) (ha : a < 1953) :
    tvImg j (tvImg j a) = a := by
  have h := tvImgCheck_holds
  simp only [chkTvImg, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  have := (h j hj a ha).2
  rwa [tvTab_get hj ha, tvTab_get hj (tvImg_lt hj ha)] at this

theorem tvPair_tvImg {j a : Nat} (hj : j < 1953)
    (ha : a < 1953) :
    tvPair (tvImg j a) =
      ((if form (tvPair j).2 (tvPair a).1 then (tvPair a).1 ^^^ (tvPair j).1 else (tvPair a).1),
       (if form (tvPair a).2 (tvPair j).1 then (tvPair a).2 ^^^ (tvPair j).2
         else (tvPair a).2)) := by
  have hF := tvListFacts
  obtain ⟨hj1, hj2, -, -, -, -⟩ := hF.entry j hj
  obtain ⟨ha1, ha2, -, -, -, -⟩ := hF.entry a ha
  have hv : (if form (tvPair j).2 (tvPair a).1 then (tvPair a).1 ^^^ (tvPair j).1
      else (tvPair a).1) < 64 := by
    split
    · exact Nat.xor_lt_two_pow (n := 6) ha1 hj1
    · exact ha1
  have hφ : (if form (tvPair a).2 (tvPair j).1 then (tvPair a).2 ^^^ (tvPair j).2
      else (tvPair a).2) < 64 := by
    split
    · exact Nat.xor_lt_two_pow (n := 6) ha2 hj2
    · exact ha2
  generalize hv' : (if form (tvPair j).2 (tvPair a).1 then (tvPair a).1 ^^^ (tvPair j).1
      else (tvPair a).1) = v' at hv ⊢
  generalize hφ' : (if form (tvPair a).2 (tvPair j).1 then (tvPair a).2 ^^^ (tvPair j).2
      else (tvPair a).2) = φ' at hφ ⊢
  have h1 : tvImg j a = tvIdxTab[64 * v' + φ']! := by
    simp only [tvImg]
    rw [hv', hφ']
  have hlt := tvImg_lt hj ha
  rw [h1] at hlt ⊢
  have hn : 64 * v' + φ' < 4096 := by omega
  rcases (hF.idxTab _ hn).2 with h | h
  · rw [h] at hlt
    omega
  · rw [h]
    ext <;> simp <;> omega

end CFSG.GF2Type.SmithTypeE.LMod
