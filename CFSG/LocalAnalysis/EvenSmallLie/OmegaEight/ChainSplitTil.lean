module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTilCheck
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainZ4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Matrix Stage1 CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem bz_mod_two (n : ℕ) : bz (n % 2 == 1) = (n : ZMod 2) := by
  rw [← ZMod.natCast_mod n 2]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> rfl

theorem toMat_red2 (M : Array (Array ℕ)) : toMat 6 6 (red2 M) = (toMat4 M).map red4 := by
  ext i j
  rw [toMat_apply, red2, getD_ofFn, testBit_bitsOf]
  simp only [j.isLt, decide_true, Bool.true_and, bz_mod_two, map_apply, toMat4, of_apply]
  exact (map_natCast red4 _).symm

theorem red2_eq_id6 {M : Array (Array ℕ)} (h : (toMat4 M).map red4 = 1) : red2 M = id6 := by
  have h1 : ∀ i j : Fin 6, ((red2 M).getD i 0).testBit j = decide ((i : ℕ) = j) := by
    intro i j
    have := congrFun (congrFun (toMat_red2 M ▸ h) i) j
    rw [toMat_apply, one_apply] at this
    by_cases hij : i = j
    · rw [ite_eq_left_iff.2 (fun h' => absurd hij h')] at this
      rw [decide_eq_true (congrArg Fin.val hij)]
      cases hb : ((red2 M).getD i 0).testBit j
      · rw [hb] at this; exact absurd this (by decide)
      · rfl
    · rw [ite_eq_right_iff.2 (fun h' => absurd h' hij)] at this
      rw [decide_eq_false (fun e => hij (Fin.ext e))]
      cases hb : ((red2 M).getD i 0).testBit j
      · rfl
      · rw [hb] at this; exact absurd this (by decide)
  have hf : ∀ i : Fin 6, (bitsOf 6 fun j => m4Get M i j % 2 == 1) = 2 ^ (i : ℕ) := by
    intro i
    apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_bitsOf, Nat.testBit_two_pow]
    by_cases hj : j < 6
    · have := h1 i ⟨j, hj⟩
      rw [red2, getD_ofFn, testBit_bitsOf] at this
      simp only [hj, decide_true, Bool.true_and] at this ⊢
      rw [this]
    · simp only [hj, decide_false, Bool.false_and]
      exact (decide_eq_false fun (e : (i : ℕ) = j) => hj (e ▸ i.isLt)).symm
  rw [red2]
  simp only [hf]
  rfl

theorem tilIdx_spec {ε : Eps} {M : Array (Array ℕ)} (h : tilIdx ε M < 128) :
    tilGet ε (tilIdx ε M) = M := by
  unfold tilIdx at h ⊢
  cases hf : (List.range 128).find? fun i => tilGet ε i == M with
  | none => rw [hf] at h; exact absurd h (by decide)
  | some i =>
    simp only [Option.getD_some]
    exact beq_iff_eq.1 (List.find?_some (p := fun i => tilGet ε i == M) hf)

section Cert


theorem tilCheck_parts (ε : Eps) : xCheck ε = true ∧ tabCheck ε = true ∧ invCheckS ε = true := by
  have h := tilCheck_spec ε
  simp only [tilCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem xTil_facts (ε : Eps) :
    toMat4 (xTil ε) * toMat4 (xTil ε) = 1 ∧
    (toMat4 (xTil ε)).map red4 = toMat 6 6 (CPrime.reflRows ε (n0 ε)) ∧
    ∀ s < 6, toMat4 (xTil ε) * liftW ε (c0Mat ε) s * toMat4 (xTil ε) =
        prodW ε (c0Mat ε) ((reflWords ε).getD s []) ∧
      toMat 6 6 (wordRows ε ((reflWords ε).getD s [])) =
        toMat 6 6 (CPrime.reflRows ε (n0 ε)) * genMat ε s *
          toMat 6 6 (CPrime.reflRows ε (n0 ε)) := by
  have h := (tilCheck_parts ε).1
  simp only [xCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by rw [← toMat4_mul4, h1, toMat4_one4], by rw [← toMat_red2, h2], fun s hs => ?_⟩
  obtain ⟨h4, h5⟩ := h3 s hs
  refine ⟨?_, ?_⟩
  · have := congrArg toMat4 h4
    rwa [toMat4_mul4, toMat4_mul4, toMat4_ptil4, toMat4_prod4] at this
  · rw [h5, toMat_bmul, toMat_bmul, genMat, mul_assoc]

theorem tab_facts (ε : Eps) :
    tilGet ε 0 = one4 ∧ tilIdx ε (xTil ε) < 128 ∧
    (∀ k < 6, wordRows ε ((uWords ε).getD k []) = uRows ε k ∧
      tilIdx ε (prod4 ε ((uWords ε).getD k [])) < 128) ∧
    (∀ i < 128, ∀ j < 128, tilIdx ε (mul4 (tilGet ε i) (tilGet ε j)) < 128) ∧
    ∀ i < 128, ∀ j < 128, red2 (tilGet ε i) = red2 (tilGet ε j) → i = j := by
  have h := (tilCheck_parts ε).2.1
  simp only [tabCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun i hi j hj hij => ?_⟩
  rcases h5 i hi j hj with h | h
  · exact h
  · rw [hij] at h
    simp at h

theorem inv_facts (ε : Eps) {i : ℕ} (hi : i < 128) (h : isInvol4 (tilGet ε i) = true) :
    128 * fix2c (red2 (tilGet ε i)) < 64 * fix4c (tilGet ε i) ∧
    (i = zTil ε ∨ 256 < 2 * fix4c (tilGet ε i) ∨
      2 * fix4c (tilGet ε i) * centc ε (tilGet ε i) < 16384) := by
  have hc := (tilCheck_parts ε).2.2
  simp only [invCheckS, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at hc
  rcases hc i hi with h' | ⟨h1, h2⟩
  · rw [h] at h'; exact absurd h' (by decide)
  · refine ⟨h1, ?_⟩
    rcases h2 with (h2 | h2) | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h2)

end Cert

end CFSG.EvenSmallLie.OmegaEight.Chain
