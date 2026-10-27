module

public import Certificates.Data.Kernel.J4Mask11

public section

namespace CFSG.KC.J4Mask11

open CFSG.EvenSporadicStandard.J4Std.Data11 CFSG.Sporadic.J4.QT
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (duadMasks)

theorem foldl_congr_mem {f g : ℕ → ℕ → ℕ} :
    ∀ (l : List ℕ) (a : ℕ), (∀ b ∈ l, ∀ x, f x b = g x b) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h b (by simp) a]
    exact foldl_congr_mem l _ fun b' hb' x => h b' (by simp [hb']) x

theorem rowsXor_congr {r r' : ℕ → ℕ} {m : ℕ} (h : ∀ j < m, r j = r' j) (c : ℕ) :
    rowsXor r m c = rowsXor r' m c := by
  unfold rowsXor
  exact foldl_congr_mem _ _ fun j hj x => by rw [h j (List.mem_range.mp hj)]

theorem pRowK_eq : ∀ j < 11, pRowK j = pRow j := by decide +kernel

theorem pMapK_eq (c : ℕ) : pMapK c = pMap c := by
  unfold pMapK pMap
  exact rowsXor_congr pRowK_eq c

theorem pPowK_eq (k c : ℕ) : pPowK k c = pPow k c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change pMapK (pPowK k c) = pPow (k + 1) c
    rw [ih, pMapK_eq, pPow]

theorem evAtK_eq (y f : ℕ) : evAtK y f = evAt y f := by
  unfold evAtK evAt
  exact rowsXor_congr (fun i _ => pPowK_eq i y) f

theorem isPowK_iff (v : ℕ) : isPowK v = true ↔ ∃ m < 11, v = pPow m 1 := by
  unfold isPowK
  simp [pPowK_eq]

theorem two_pow_eleven : (2 : ℕ) ^ 11 = 2048 := rfl

theorem mask6_of (h : chkMask6 = true) : ((List.range (2 ^ 11)).map (evAt 1)).Nodup := by
  rw [two_pow_eleven]
  unfold chkMask6 at h
  rw [List.all_eq_true] at h
  unfold List.Nodup
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem ?_ List.nodup_range
  intro x y hx hy hne hxy
  have hx' := Nat.eq_of_beq_eq_true (h x hx)
  have hy' := Nat.eq_of_beq_eq_true (h y hy)
  rw [evAtK_eq] at hx' hy'
  exact hne (by rw [← hx', ← hy', hxy])

theorem mask7_of (h : chkMask7 = true) :
    ∀ f < 2 ^ 11, ∀ k < 11, evAt (evAt 1 f) f = pPow k 1 → ∃ m < 11, evAt 1 f = pPow m 1 := by
  intro f hf k hk he
  rw [two_pow_eleven] at hf
  unfold chkMask7 at h
  rw [List.all_eq_true] at h
  have hf' := h f (List.mem_range.mpr hf)
  simp only [evAtK_eq, Bool.or_eq_true, Bool.not_eq_true'] at hf'
  rcases hf' with hp | hn
  · exact (isPowK_iff _).mp hp
  · exfalso
    rw [(isPowK_iff _).mpr ⟨k, hk, he⟩] at hn
    exact absurd hn (by decide)

theorem mask8_of (h : chkMask8 = true) (hw : chkMask8w = true) :
    ∀ f < 2 ^ 11, (∀ g < 2 ^ 11, evAt 1 g ∈ duadMasks → evAt (evAt 1 f) g ∈ duadMasks) →
      ∃ m < 11, evAt 1 f = pPow m 1 := by
  intro f hf H
  rw [two_pow_eleven] at hf H
  unfold chkMask8 at h
  rw [List.all_eq_true] at h
  have hf' := h f (List.mem_range.mpr hf)
  simp only [evAtK_eq, Bool.or_eq_true, List.any_eq_true] at hf'
  rcases hf' with hp | ⟨g, hg, hn⟩
  · exact (isPowK_iff _).mp hp
  · exfalso
    unfold chkMask8w at hw
    rw [List.all_eq_true] at hw
    have hg2 := hw g hg
    rw [Bool.and_eq_true, evAtK_eq] at hg2
    have hin := H g (of_decide_eq_true hg2.1) (List.contains_iff_mem.mp hg2.2)
    rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at hn
    exact hn hin

end CFSG.KC.J4Mask11
