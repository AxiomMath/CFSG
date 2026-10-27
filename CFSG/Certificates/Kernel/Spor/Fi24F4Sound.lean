module

public import Certificates.Data.Kernel.Spor.Fi24F4
public import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Sporadic.Th.TableSpec
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.Fi24F4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Fi24F4 CFSG.Sporadic.Th
open CFSG.KS.Raw.Orb (PRep)

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : CFSG.KC.Enum.strictN y k = k y := by
  cases y <;> rfl

theorem wPt_nil {w m : Nat} {S SI : Nat → Nat} (x : Nat) : wPt w m S SI [] x = x := rfl

theorem wPt_cons {w m : Nat} {S SI : Nat → Nat} (z : Int) (wd : List Int) (x : Nat) :
    wPt w m S SI (z :: wd) x = pg w m (letP S SI z) (wPt w m S SI wd x) := by
  change CFSG.KC.Enum.strictN (wPt w m S SI wd x) (fun y => pg w m (letP S SI z) y) = _
  rw [strictN_eq']

theorem wordG_cons' {G : Type*} [Group G] (L : ℤ → G) (z : ℤ) (wd : List ℤ) :
    wordG L (z :: wd) = L z * wordG L wd := by
  unfold wordG
  rw [List.map_cons, List.prod_cons]

theorem wordG_nil' {G : Type*} [Group G] (L : ℤ → G) : wordG L [] = 1 := rfl

theorem wordG_append' {G : Type*} [Group G] (L : ℤ → G) (u v : List ℤ) :
    wordG L (u ++ v) = wordG L u * wordG L v := by
  unfold wordG
  rw [List.map_append, List.prod_append]

theorem wPt_wordG {n w : Nat} {S SI : Nat → Nat} {L : ℤ → Equiv.Perm (Fin n)} :
    ∀ wd : List Int, (∀ z ∈ wd, PRep n w (letP S SI z) (L z)) →
      ∀ x : Fin n, wPt w (mask w) S SI wd x.val = (wordG L wd x).val
  | [], _, x => by rw [wPt_nil, wordG_nil']; rfl
  | z :: wd, h, x => by
    rw [wPt_cons, wPt_wordG wd (fun z' hz' => h z' (List.mem_cons_of_mem _ hz')) x,
      h z List.mem_cons_self, wordG_cons', Equiv.Perm.mul_apply]

theorem prep_of_recOK {n w P : Nat} {S SI : Nat → Nat} {wd : List Int}
    {L : ℤ → Equiv.Perm (Fin n)} (hL : ∀ z ∈ wd, PRep n w (letP S SI z) (L z))
    (h : recOK n w (mask w) P S SI wd = true) :
    PRep n w P (wordG L wd) ∧ canonK n w (mask w) (n * w) P = true := by
  unfold recOK at h
  simp only [bAnd_iff] at h
  refine ⟨fun x => ?_, h.1⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec h.2 x.val x.isLt)]
  exact wPt_wordG wd hL x

theorem prep_mul {n w P Q : Nat} {g h : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hP : PRep n w P g) (hQ : PRep n w Q h) : PRep n w (pcomp n w (mask w) P Q) (g * h) :=
  fun x => by
    rw [PackFld.pg_pcomp hn x.isLt, hQ x, hP (h x), Equiv.Perm.mul_apply]

theorem pcomp_shr' {n w P Q : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) :
    pcomp n w (mask w) P Q >>> (n * w) = 0 := PackFld.pcomp_shr hn hw

theorem comm_iff {n w P Q : Nat} {g h : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32) (hw : 0 < w)
    (hP : PRep n w P g) (hQ : PRep n w Q h) :
    g * h = h * g ↔ pcomp n w (mask w) P Q = pcomp n w (mask w) Q P := by
  have h1 := prep_mul hn hP hQ
  have h2 := prep_mul hn hQ hP
  constructor
  · intro e
    refine CFSG.KS.PF.eq_of_fields hw (pcomp_shr' hn hw) (pcomp_shr' hn hw) fun i hi => ?_
    rw [h1 ⟨i, hi⟩, h2 ⟨i, hi⟩, e]
  · intro e
    ext x
    rw [← h1 x, ← h2 x, e]

theorem cntComm_succ {n w m : Nat} {T : Nat → Nat} {Y lo d : Nat} :
    cntComm n w m T Y lo (d + 1) =
      if pcomp n w m (T (lo + d)) Y = pcomp n w m Y (T (lo + d)) then cntComm n w m T Y lo d + 1
      else cntComm n w m T Y lo d := by
  change CFSG.KC.Enum.strictN (cntComm n w m T Y lo d) (fun c =>
    CFSG.KC.Enum.strictN (T (Nat.add lo d)) (fun t =>
      nIf(Nat.beq (pcomp n w m t Y) (pcomp n w m Y t), Nat.succ c, c))) = _
  rw [strictN_eq', strictN_eq']
  by_cases e : pcomp n w m (T (lo + d)) Y = pcomp n w m Y (T (lo + d))
  · rw [if_pos e]
    have : Nat.beq (pcomp n w m (T (Nat.add lo d)) Y) (pcomp n w m Y (T (Nat.add lo d))) = true :=
      Nat.beq_eq.mpr e
    rw [this]
  · rw [if_neg e]
    have : Nat.beq (pcomp n w m (T (Nat.add lo d)) Y) (pcomp n w m Y (T (Nat.add lo d))) = false := by
      cases hb : Nat.beq (pcomp n w m (T (Nat.add lo d)) Y) (pcomp n w m Y (T (Nat.add lo d)))
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) e
    rw [this]

theorem cntComm_eq {n w m : Nat} (T : Nat → Nat) (Y lo : Nat) : ∀ len,
    cntComm n w m T Y lo len =
      ((List.range' lo len).filter fun i => pcomp n w m (T i) Y == pcomp n w m Y (T i)).length
  | 0 => rfl
  | d + 1 => by
    rw [cntComm_succ, cntComm_eq T Y lo d, List.range'_concat, List.filter_append,
      List.length_append, Nat.one_mul]
    by_cases e : pcomp n w m (T (lo + d)) Y = pcomp n w m Y (T (lo + d))
    · rw [if_pos e]
      simp [e]
    · rw [if_neg e]
      simp [e]

theorem card_inf_eq_length_filter {G : Type*} [Group G] {H K : Subgroup G} {n : ℕ} (g : ℕ → G)
    (hmem : ∀ x, x ∈ H ↔ ∃ i < n, g i = x) (hcard : Nat.card H = n) (p : ℕ → Bool)
    (hp : ∀ i < n, p i = true ↔ g i ∈ K) :
    Nat.card ↥(H ⊓ K) = ((List.range n).filter p).length := by
  classical
  have himg : g '' ↑(Finset.range n) = (H : Set G) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_range, SetLike.mem_coe, hmem x]
  have hinj : Set.InjOn g ↑(Finset.range n) := by
    refine Set.injOn_of_ncard_image_eq ?_
    rw [himg, Set.ncard_coe_finset, Finset.card_range, ← hcard, ← Nat.card_coe_set_eq]
    rfl
  have hT : g '' ↑((List.range n).filter p).toFinset = ((H ⊓ K : Subgroup G) : Set G) := by
    ext x
    simp only [Set.mem_image, Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range,
      SetLike.mem_coe, Subgroup.mem_inf]
    constructor
    · rintro ⟨i, ⟨hi, hpi⟩, rfl⟩
      exact ⟨(hmem _).2 ⟨i, hi, rfl⟩, (hp i hi).1 hpi⟩
    · rintro ⟨hxH, hxK⟩
      obtain ⟨i, hi, rfl⟩ := (hmem x).1 hxH
      exact ⟨i, ⟨hi, (hp i hi).2 hxK⟩, rfl⟩
  have hsub : (↑((List.range n).filter p).toFinset : Set ℕ) ⊆ ↑(Finset.range n) := by
    intro i hi
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hi
    exact Finset.mem_coe.2 (Finset.mem_range.2 hi.1)
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter p), ← Set.ncard_coe_finset,
    ← (hinj.mono hsub).ncard_image, hT, ← Nat.card_coe_set_eq]
  rfl

end CFSG.KS.Fi24F4

end
