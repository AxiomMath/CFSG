module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhFrame
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.IlinykhGL

public section

namespace CFSG.EvenSmallLie.OmegaEight

open Finset

@[expose] def unionClass : Fin 7 → ℕ := ![1, 2, 3, 5, 6, 7, 8]

@[expose] def inUnion (S : Finset (Fin 7)) (n : ℕ) : Prop :=
  frameClass n = 9 ∨ ∃ k ∈ S, frameClass n = unionClass k

instance (S : Finset (Fin 7)) : DecidablePred (inUnion S) := fun n =>
  inferInstanceAs (Decidable (frameClass n = 9 ∨ ∃ k ∈ S, frameClass n = unionClass k))

@[expose] def unionF (S : Finset (Fin 7)) (m : ℕ) : ℕ :=
  ((range 256).filter fun a => inUnion S a ∧ inUnion S (a ^^^ m)).card

@[expose] def unionIdx (S : Finset (Fin 7)) : ℕ := ∑ k ∈ S, 2 ^ (k : ℕ)

@[expose] def unionWitList : List ℕ := [
    0, 0, 3, 1, 0, 0, 3, 1, 23, 1, 3, 1, 7, 23, 3, 1, 0, 0, 3, 1, 7, 1, 7, 1, 23, 23, 3, 1, 7, 1,
    3, 3, 0, 0, 3, 1, 7, 7, 7, 3, 63, 1, 3, 1, 7, 7, 3, 3, 31, 1, 31, 3, 7, 1, 3, 1, 23, 1, 3, 3,
    7, 1, 3, 1, 0, 1, 3, 0, 0, 1, 3, 1, 23, 1, 3, 1, 23, 1, 3, 1, 0, 1, 3, 3, 7, 1, 3, 1, 23, 1, 3,
    3, 7, 1, 3, 1, 0, 63, 3, 1, 7, 7, 3, 7, 63, 1, 3, 1, 7, 7, 3, 3, 31, 1, 3, 31, 7, 1, 3, 1, 23,
    1, 3, 3, 7, 1, 3, 1]

@[expose] def unionWit (S : Finset (Fin 7)) : ℕ := unionWitList.getD (unionIdx S) 0

set_option maxRecDepth 100000 in
theorem union_table : ∀ S : Finset (Fin 7), S = ∅ ∨ S = {0} ∨ S = {6} ∨ S = {0, 1, 6} ∨
    (unionWit S < 256 ∧ inUnion S (unionWit S) ∧ unionF S (unionWit S) ≠ unionF S 255) ∨
    ¬ ((range 256).filter (inUnion S)).card ∣
      2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
  decide +kernel

theorem exists_unionClass : ∀ c ≤ 9, c ≠ 0 → c ≠ 4 → c ≠ 9 → ∃ k, unionClass k = c := by
  decide

theorem unionClass_ne (k : Fin 7) : unionClass k ≠ 0 ∧ unionClass k ≠ 4 ∧ unionClass k ≠ 9 := by
  revert k
  decide

@[expose] def frameNine : Set FrameVec := {v | frameCls v = 1 ∨ frameCls v = 9}

@[expose] def frameNine' : Set FrameVec := {v | frameCls v = 8 ∨ frameCls v = 9}

@[expose] def frameFortyFive : Set FrameVec :=
  {v | frameCls v = 1 ∨ frameCls v = 2 ∨ frameCls v = 8 ∨ frameCls v = 9}

theorem orbit_frameZ_cases {N : Type*} [Group N] [MulAction N FrameVec]
    (hadd : ∀ (n : N) (x y : FrameVec), n • (x + y) = n • x + n • y)
    (hgen : ∀ σ ∈ frameGens, ∃ n : N, ∀ v : FrameVec, n • v = permVec σ v)
    (hplane : ∀ n : N, ∀ B ∈ frameBlocks, n • frameZ ≠ blockVec B) :
    MulAction.orbit N frameZ = {frameZ} ∨ MulAction.orbit N frameZ = frameNine ∨
      MulAction.orbit N frameZ = frameNine' ∨ MulAction.orbit N frameZ = frameFortyFive := by
  classical
  set Y := MulAction.orbit N frameZ
  have hYsmul : ∀ (n : N) (v : FrameVec), v ∈ Y → n • v ∈ Y := by
    rintro n _ ⟨m, rfl⟩
    exact ⟨n * m, mul_smul n m frameZ⟩
  have hYz : frameZ ∈ Y := MulAction.mem_orbit_self _
  have hYcl : ∀ σ ∈ Subgroup.closure frameGens, ∀ v ∈ Y, permVec σ v ∈ Y := by
    intro σ hσ v hv
    obtain ⟨n, hn⟩ := closure_le_frameRealized hgen hσ
    rw [← hn]
    exact hYsmul n v hv
  have hY0 : ∀ v ∈ Y, frameCls v ≠ 0 := by
    rintro _ ⟨n, rfl⟩ h
    rw [frameCls_eq_zero_iff] at h
    have h' := congrArg (n⁻¹ • ·) h
    simp only [inv_smul_smul, smul_zero_of_hadd hadd] at h'
    exact frameZ_ne_zero h'
  have hY4 : ∀ v ∈ Y, frameCls v ≠ 4 := by
    rintro _ ⟨n, rfl⟩ h
    obtain ⟨B, hB, hv⟩ := (frameCls_eq_four_iff _).mp h
    exact hplane n B hB hv
  set S : Finset (Fin 7) := univ.filter fun k => ∃ u ∈ Y, frameCls u = unionClass k
  have hYS : ∀ v, v ∈ Y ↔ inUnion S (frameEncode v) := by
    intro v
    constructor
    · intro hv
      by_cases h9 : frameCls v = 9
      · exact Or.inl h9
      · right
        obtain ⟨k, hk⟩ := exists_unionClass _ (frameCls_le v) (hY0 v hv) (hY4 v hv) h9
        refine ⟨k, ?_, hk.symm⟩
        simp only [S, mem_filter, mem_univ, true_and]
        exact ⟨v, hv, hk.symm⟩
    · rintro (h9 | ⟨k, hk, hvk⟩)
      · rw [(frameCls_eq_nine_iff v).mp h9]
        exact hYz
      · simp only [S, mem_filter, mem_univ, true_and] at hk
        obtain ⟨u, hu, huk⟩ := hk
        have hne := unionClass_ne k
        exact mem_of_frameCls_eq hYcl (huk.trans hvk.symm) (huk ▸ hne.1) (huk ▸ hne.2.1)
          (huk ▸ hne.2.2) hu
  set fY : FrameVec → ℕ := fun v => (univ.filter fun a => a ∈ Y ∧ a + v ∈ Y).card
  have hfinv : ∀ (n : N) (v : FrameVec), fY (n • v) = fY v := by
    intro n v
    symm
    refine card_nbij' (n • ·) (n⁻¹ • ·) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      refine ⟨hYsmul n a ha.1, ?_⟩
      rw [← hadd]
      exact hYsmul n _ ha.2
    · intro b hb
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨hYsmul n⁻¹ b hb.1, ?_⟩
      have h := hYsmul n⁻¹ _ hb.2
      rwa [hadd, inv_smul_smul] at h
    · intro a _
      exact inv_smul_smul n a
    · intro b _
      exact smul_inv_smul n b
  have hfconst : ∀ v ∈ Y, fY v = fY frameZ := by
    rintro _ ⟨n, rfl⟩
    exact hfinv n frameZ
  have hfnat : ∀ m < 256, fY (frameDecode m) = unionF S m := by
    intro m hm
    simp only [fY]
    rw [card_filter_frameVec]
    refine congrArg card (filter_congr fun a ha => ?_)
    have ha' := mem_range.mp ha
    rw [hYS, hYS, ← frameDecode_xor, frameEncode_frameDecode a ha',
      frameEncode_frameDecode _ (Nat.xor_lt_two_pow (n := 8) ha' hm)]
  have hcard : Nat.card Y = ((range 256).filter (inUnion S)).card := by
    have h1 : Nat.card Y = (univ.filter fun v => v ∈ Y).card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by simp)
    rw [h1, card_filter_frameVec]
    refine congrArg card (filter_congr fun n hn => ?_)
    rw [hYS, frameEncode_frameDecode n (mem_range.mp hn)]
  have hdvd : Nat.card Y ∣ 2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
    rw [← card_GL_eight_two, ← card_addPerms_pi 8]
    exact card_orbit_dvd_card_addPerms hadd frameZ
  have hset : ∀ T : Set FrameVec, (∀ v, inUnion S (frameEncode v) ↔ v ∈ T) → Y = T := by
    intro T hT
    ext v
    rw [hYS, hT]
  rcases union_table S with hS | hS | hS | hS | ⟨hw, hwY, hwf⟩ | hS
  · left
    refine hset _ fun v => ?_
    rw [hS, Set.mem_singleton_iff, ← frameCls_eq_nine_iff]
    simp [inUnion, frameCls]
  · right; left
    refine hset _ fun v => ?_
    rw [hS]
    simp [inUnion, frameNine, frameCls, unionClass, or_comm]
  · right; right; left
    refine hset _ fun v => ?_
    rw [hS]
    simp [inUnion, frameNine', frameCls, unionClass, or_comm]
  · right; right; right
    refine hset _ fun v => ?_
    rw [hS]
    simp only [inUnion, frameFortyFive, frameCls, mem_insert, mem_singleton,
      exists_eq_or_imp, exists_eq_left, Set.mem_ofPred_eq]
    simp [unionClass]
    tauto
  · exfalso
    have hv : frameDecode (unionWit S) ∈ Y := by
      rw [hYS, frameEncode_frameDecode _ hw]
      exact hwY
    have h := hfconst _ hv
    rw [hfnat _ hw, ← frameDecode_255, hfnat 255 (by decide)] at h
    exact hwf h
  · exact absurd (hcard ▸ hdvd) hS

end CFSG.EvenSmallLie.OmegaEight
