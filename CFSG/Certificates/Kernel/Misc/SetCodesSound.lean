module

public import Certificates.Data.Kernel.Misc.SetCodes
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs
import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.Certificates.Kernel.Spor.RawDefs

public section

namespace CFSG.KC.Misc.SetCodes

open CFSG.KC.Enum (pg)
open CFSG.KS (mask)
open CFSG.KS.Raw (unpack)
open CFSG.KC.Misc.Clos (allN_iff anyN_iff)
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2

theorem unpack_getElem! {n w P i : ℕ} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem testBit_maskK (L w s x : ℕ) :
    Nat.testBit (maskK L w s) x = true ↔ ∃ q < L, pg w (mask w) s q = x := by
  induction L with
  | zero => simp [maskK]
  | succ L ih =>
    change Nat.testBit (maskK L w s ||| 1 <<< pg w (mask w) s L) x = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
      decide_eq_true_iff]
    constructor
    · rintro (⟨q, hq, e⟩ | e)
      · exact ⟨q, Nat.lt_succ_of_lt hq, e⟩
      · exact ⟨L, Nat.lt_succ_self L, e⟩
    · rintro ⟨q, hq, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
      · exact Or.inl ⟨q, hq, e⟩
      · exact Or.inr e

theorem contains_unpack (L w s x : ℕ) :
    (unpack L w s).contains x = Nat.testBit (maskK L w s) x := by
  rw [Bool.eq_iff_iff, Array.contains_iff_mem, testBit_maskK, unpack, Array.mem_ofFn]
  constructor
  · rintro ⟨q, e⟩
    exact ⟨q.val, q.isLt, e⟩
  · rintro ⟨q, hq, e⟩
    exact ⟨⟨q, hq⟩, e⟩

theorem all_unpack (L w s : ℕ) (p : ℕ → Bool) :
    (unpack L w s).all p = true ↔ ∀ q < L, p (pg w (mask w) s q) = true := by
  rw [Array.all_eq_true]
  simp only [unpack, Array.size_ofFn, Array.getElem_ofFn]

theorem any_unpack (L w s : ℕ) (p : ℕ → Bool) :
    (unpack L w s).any p = true ↔ ∃ q < L, p (pg w (mask w) s q) = true := by
  rw [Array.any_eq_true]
  simp only [unpack, Array.size_ofFn, Array.getElem_ofFn, exists_prop]

theorem mapsInto_unpack {L w P s s' : ℕ} (hlt : ∀ q < L, pg w (mask w) s q < 315) :
    mapsInto (unpack 315 w P) (unpack L w s) (unpack L w s') = intoK L w P s (maskK L w s') := by
  rw [Bool.eq_iff_iff, mapsInto, all_unpack, intoK, allN_iff]
  refine forall₂_congr fun q hq => ?_
  rw [unpack_getElem! (hlt q hq), contains_unpack]

variable {F : Array (Array ℕ)} {m L w : ℕ} {SC : ℕ → ℕ}

theorem all_fam (hm : F.size = m) (p : Array ℕ → Bool) :
    F.all p = true ↔ ∀ i < m, p F[i]! = true := by
  rw [Array.all_eq_true]
  constructor
  · intro h i hi
    rw [getElem!_pos F i (by omega)]
    exact h i (by omega)
  · intro h i hi
    have := h i (by omega)
    rwa [getElem!_pos F i hi] at this

theorem any_fam (hm : F.size = m) (p : Array ℕ → Bool) :
    F.any p = true ↔ ∃ i < m, p F[i]! = true := by
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    refine ⟨i, by omega, ?_⟩
    rwa [getElem!_pos F i hi]
  · rintro ⟨i, hi, h⟩
    refine ⟨i, by omega, ?_⟩
    rwa [getElem!_pos F i (by omega)] at h

theorem permutes_sound (hF : F.size = m ∧ ∀ i < m, F[i]! = unpack L w (SC i))
    (hlt : ∀ i < m, ∀ q < L, pg w (mask w) (SC i) q < 315) (P : ℕ) :
    permutesSets F (unpack 315 w P) = permutesK m L w SC P := by
  rw [Bool.eq_iff_iff, permutesSets, all_fam hF.1, permutesK, allN_iff]
  refine forall₂_congr fun i hi => ?_
  rw [any_fam hF.1, anyN_iff]
  refine exists_congr fun j => and_congr_right fun hj => ?_
  rw [hF.2 i hi, hF.2 j hj, mapsInto_unpack (hlt i hi)]

theorem fixes_sound (hF : F.size = m ∧ ∀ i < m, F[i]! = unpack L w (SC i))
    (hlt : ∀ i < m, ∀ q < L, pg w (mask w) (SC i) q < 315) (P : ℕ) :
    fixesSets F (unpack 315 w P) = fixesK m L w SC P := by
  rw [Bool.eq_iff_iff, fixesSets, all_fam hF.1, fixesK, allN_iff]
  refine forall₂_congr fun i hi => ?_
  rw [hF.2 i hi, mapsInto_unpack (hlt i hi)]

theorem acts_sound (hF : F.size = m ∧ ∀ i < m, F[i]! = unpack L w (SC i))
    (hlt : ∀ i < m, ∀ q < L, pg w (mask w) (SC i) q < 315) {σ : List ℕ}
    (hσ : ∀ i < m, σ.getD i 0 < m) (P : ℕ) :
    actsBy F (unpack 315 w P) σ = actsK m L w SC P (fun i => σ.getD i 0) := by
  rw [Bool.eq_iff_iff, actsBy, List.all_eq_true, actsK, allN_iff, hF.1]
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · have := h i (List.mem_range.2 hi)
    rwa [hF.2 i hi, hF.2 _ (hσ i hi), mapsInto_unpack (hlt i hi)] at this
  · have hi' := List.mem_range.1 hi
    rw [hF.2 i hi', hF.2 _ (hσ i hi'), mapsInto_unpack (hlt i hi')]
    exact h i hi'

theorem nodup_unpack (L w s : ℕ) :
    (unpack L w s).toList.Nodup ↔ ∀ q < L, ∀ r < q, pg w (mask w) s q ≠ pg w (mask w) s r := by
  rw [unpack, Array.toList_ofFn, List.Nodup, List.pairwise_ofFn]
  constructor
  · intro h q hq r hr e
    exact @h ⟨r, by omega⟩ ⟨q, hq⟩ hr e.symm
  · intro h r q hrq e
    exact h q.val q.isLt r.val hrq e.symm

theorem setsOK_sound (hF : F.size = m ∧ ∀ i < m, F[i]! = unpack L w (SC i)) :
    setsOK F L = setsK 315 m L w SC := by
  rw [Bool.eq_iff_iff, setsOK, setsK, Bool.and_eq_true, Bool.and_eq_true, all_fam hF.1, allN_iff,
    List.all_eq_true, allN_iff, hF.1]
  refine and_congr (forall₂_congr fun i hi => ?_) ?_
  · rw [hF.2 i hi]
    have hs : ((unpack L w (SC i)).size == L) = true := by simp [unpack]
    simp only [hs, Bool.true_and, Bool.and_eq_true, allN_iff, all_unpack, decide_eq_true_eq,
      nodup_unpack, Nat.blt_eq]
    refine and_congr Iff.rfl (forall₂_congr fun q hq => forall₂_congr fun r hr => ?_)
    constructor
    · intro hne
      cases e : Nat.beq (pg w (mask w) (SC i) q) (pg w (mask w) (SC i) r)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hne
    · intro h e
      rw [e, Nat.beq_refl] at h
      exact absurd h (by decide)
  · refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
    · rw [allN_iff]
      intro j hj
      have := (List.all_eq_true.1 (h i (List.mem_range.2 hi))) j (List.mem_range.2 hj)
      rw [Bool.or_eq_true, beq_iff_eq, hF.2 i hi, hF.2 j hj, any_unpack] at this
      rw [Bool.or_eq_true, Nat.beq_eq, anyN_iff]
      rcases this with e | ⟨q, hq, hn⟩
      · exact Or.inl e
      · rw [contains_unpack] at hn
        exact Or.inr ⟨q, hq, hn⟩
    · have hi' := List.mem_range.1 hi
      rw [List.all_eq_true]
      intro j hj
      have hj' := List.mem_range.1 hj
      have := (allN_iff _ _).1 (h i hi') j hj'
      rw [Bool.or_eq_true, Nat.beq_eq, anyN_iff] at this
      rw [Bool.or_eq_true, beq_iff_eq, hF.2 i hi', hF.2 j hj', any_unpack]
      rcases this with e | ⟨q, hq, hn⟩
      · exact Or.inl e
      · refine Or.inr ⟨q, hq, ?_⟩
        rw [contains_unpack]
        exact hn

end CFSG.KC.Misc.SetCodes

end
