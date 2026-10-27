module

public import Certificates.Data.Kernel.YoshQ.Idx
public import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.PF

variable {n w cnt EP : Nat} {R : List (List (List Nat))}

theorem fldN_lt (X b i : Nat) : fldN X b i < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos _)

theorem fldN_mod (X i : Nat) : fldN X (n * w) i % 2 ^ (n * w) = fldN X (n * w) i :=
  Nat.mod_eq_of_lt (fldN_lt _ _ _)

theorem apN_mod (x i : Nat) : apN n w (x % 2 ^ (n * w)) i = apN n w x i := by
  unfold apN
  rw [Nat.mod_mod]

theorem bucketN_mod (x : Nat) : bucketN n w R (x % 2 ^ (n * w)) = bucketN n w R x := by
  unfold bucketN
  rw [apN_mod, apN_mod]

theorem mem_or_nil_getD {α : Type} (L : List (List α)) (i : Nat) :
    L.getD i [] ∈ L ∨ L.getD i [] = [] := by
  by_cases h : i < L.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ (Nat.le_of_not_lt h)

theorem idxOK_spec (h : idxOK n w cnt EP R = true) :
    (∀ x, ∀ e ∈ bucketN n w R x, e % 4096 < cnt ∧ fldN EP (n * w) (e % 4096) = e >>> 12) ∧
      ∀ i < cnt, fldN EP (n * w) i * 4096 + i ∈ bucketN n w R (fldN EP (n * w) i) := by
  unfold idxOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x e he => ?_, fun i hi => ?_⟩
  · rw [List.all_eq_true] at h1
    unfold bucketN at he
    rcases mem_or_nil_getD R (apN n w x 0) with hr | hr
    · have h3 := h1 _ hr
      rw [List.all_eq_true] at h3
      rcases mem_or_nil_getD (R.getD (apN n w x 0) []) (apN n w x 1) with hb | hb
      · have h4 := h3 _ hb
        rw [List.all_eq_true] at h4
        have h5 := h4 e he
        simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h5
        exact h5
      · rw [hb] at he
        exact absurd he List.not_mem_nil
    · rw [hr] at he
      simp at he
  · have h3 := allN_spec h2 i hi
    rw [List.any_eq_true] at h3
    obtain ⟨e, he, h4⟩ := h3
    rw [Nat.beq_eq] at h4
    rw [← h4]
    exact he

theorem shr12 (x i : Nat) (hi : i < 4096) : (x * 4096 + i) >>> 12 = x := by
  rw [Nat.shiftRight_eq_div_pow]
  have : (2 : Nat) ^ 12 = 4096 := rfl
  rw [this]
  omega

theorem mod4096 (x i : Nat) (hi : i < 4096) : (x * 4096 + i) % 4096 = i := by omega

@[expose] def Distinct (n w cnt EP : Nat) : Prop :=
  ∀ a < cnt, ∀ b < cnt, fldN EP (n * w) a = fldN EP (n * w) b → a = b

theorem idxN_lt (h : idxOK n w cnt EP R = true) (hc : cnt ≤ 4096) {x : Nat}
    (hx : idxN n w R x < cnt) :
    x % 2 ^ (n * w) = fldN EP (n * w) (idxN n w R x) := by
  unfold idxN at hx ⊢
  cases e : (bucketN n w R x).find? (fun e => Nat.beq (e >>> 12) (x % 2 ^ (n * w))) with
  | none =>
    rw [e] at hx
    simp at hx
    omega
  | some e' =>
    simp only []
    have hm := List.mem_of_find?_eq_some e
    have hp := List.find?_some e
    rw [Nat.beq_eq] at hp
    obtain ⟨-, h2⟩ := (idxOK_spec h).1 x e' hm
    rw [h2, hp]

theorem idxN_entry (h : idxOK n w cnt EP R = true) (hd : Distinct n w cnt EP) (hc : cnt ≤ 4096)
    {x i : Nat} (hi : i < cnt) (hx : x % 2 ^ (n * w) = fldN EP (n * w) i) :
    idxN n w R x = i := by
  obtain ⟨h1, h2⟩ := idxOK_spec h
  have hb : bucketN n w R x = bucketN n w R (fldN EP (n * w) i) := by
    rw [← bucketN_mod x, hx, ← bucketN_mod (fldN EP (n * w) i), fldN_mod]
  have hmem := h2 i hi
  rw [← hb] at hmem
  unfold idxN
  cases e : (bucketN n w R x).find? (fun e => Nat.beq (e >>> 12) (x % 2 ^ (n * w))) with
  | none =>
    have := List.find?_eq_none.1 e _ hmem
    rw [shr12 _ _ (by omega), Nat.beq_eq, hx] at this
    exact absurd rfl this
  | some e' =>
    simp only []
    have hm := List.mem_of_find?_eq_some e
    have hp := List.find?_some e
    rw [Nat.beq_eq] at hp
    obtain ⟨h3, h4⟩ := h1 x e' hm
    apply hd _ h3 _ hi
    rw [h4, hp, hx]

theorem testBit_maskN_aux (L : List Nat) (M j : Nat) :
    (L.foldl (fun M x => M ||| (1 <<< idxN n w R x)) M).testBit j =
      (M.testBit j || L.any fun x => idxN n w R x == j) := by
  induction L generalizing M with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.any_cons]
    by_cases e : idxN n w R x = j
    · subst e
      simp
    · have e' : (idxN n w R x == j) = false := by simpa using e
      simp [e, e']

theorem testBit_maskN (L : List Nat) (j : Nat) :
    (maskN n w R L).testBit j = L.any fun x => idxN n w R x == j := by
  unfold maskN
  rw [testBit_maskN_aux]
  simp

theorem memN_eq_memI (h : idxOK n w cnt EP R = true) (hd : Distinct n w cnt EP) (hc : cnt ≤ 4096)
    {L : List Nat} (hL : allIn n w cnt R L = true) (y : Nat) :
    memN n w L y = memI n w cnt R L y := by
  unfold allIn at hL
  rw [List.all_eq_true] at hL
  apply Bool.eq_iff_iff.2
  unfold memN memI eqN
  rw [List.any_eq_true, Bool.and_eq_true, Nat.blt_eq, testBit_maskN, List.any_eq_true]
  constructor
  · rintro ⟨s, hs, e⟩
    rw [Nat.beq_eq] at e
    have hsl : idxN n w R s < cnt := by simpa [Nat.blt_eq] using hL s hs
    have h1 := idxN_lt h hc hsl
    have hy : idxN n w R y = idxN n w R s := idxN_entry h hd hc hsl (by rw [← e, h1])
    exact ⟨by rw [hy]; exact hsl, s, hs, by rw [hy]; exact beq_self_eq_true _⟩
  · rintro ⟨hy, s, hs, e⟩
    rw [beq_iff_eq] at e
    refine ⟨s, hs, ?_⟩
    rw [Nat.beq_eq, idxN_lt h hc (e ▸ hy), e, ← idxN_lt h hc hy]

theorem memN_eq_memI' (h : idxOK n w cnt EP R = true) (hd : Distinct n w cnt EP)
    (hc : cnt ≤ 4096) {L : List Nat} (hL : allIn n w cnt R L = true) :
    memN n w L = memI n w cnt R L :=
  funext (memN_eq_memI h hd hc hL)

theorem fusionCoverN_of_I {cnt EP : Nat} {R : List (List (List Nat))} {GS NL : List Nat}
    {α k : Nat} (h : idxOK 16 5 cnt EP R = true) (hd : Distinct 16 5 cnt EP) (hc : cnt ≤ 4096)
    (hI : fusionCoverI cnt R GS NL α k = true) : fusionCoverN GS NL α k = true := by
  unfold fusionCoverI at hI
  rw [Bool.and_eq_true, Bool.and_eq_true] at hI
  obtain ⟨⟨hg, hb⟩, hr⟩ := hI
  unfold fusionCoverN
  rw [memN_eq_memI' h hd hc hg, memN_eq_memI' h hd hc hb]
  exact hr

end CFSG.KC.YoshQ

end
