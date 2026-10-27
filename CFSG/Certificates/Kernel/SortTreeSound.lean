module

public import Certificates.Data.Kernel.SortTree
public import CFSG.Certificates.Kernel.MonsterB.NatBfsSound

public section

namespace CFSG.KC.SortTree

open CFSG.KLie.CT CFSG.KC.Bfs CFSG.Monster.B.TwoA.Census

theorem andB_true_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

theorem ble_iff {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]

theorem allN_iff (n : ℕ) (f : ℕ → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_true_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem cntF_eq (n B i0 : ℕ) : cntF n B i0 = min B (n - i0) := by
  unfold cntF
  cases h : Nat.blt (n - i0) B
  · dsimp only
    have : ¬ n - i0 < B := fun h' => by rw [← blt_iff] at h'; simp_all
    change B = _
    omega
  · have : n - i0 < B := blt_iff.1 h
    change n - i0 = _
    omega

theorem strictK_eq (y : ℕ) (k : ℕ → Bool) : strictK y k = k y := by cases y <;> rfl

variable {act : ℕ → ℕ → ℕ} {ng : ℕ} {valid : ℕ → Bool} {root : ℕ} {rec : ℕ → ℕ}
  {n wv wl wp : ℕ}

theorem recOK_spec {r : ℕ} (h : recOK act ng valid root rec n wv wl wp r = true) :
    valid (valF wv r) = true ∧ (levF wv wl r = 0 → valF wv r = root) ∧
      (levF wv wl r ≠ 0 → parF wv wl wp r < n ∧ letF wv wl wp r < ng ∧
        levF wv wl (rec (parF wv wl wp r)) < levF wv wl r ∧
        act (letF wv wl wp r) (valF wv (rec (parF wv wl wp r))) = valF wv r) := by
  simp only [recOK] at h
  rw [andB_true_iff] at h
  refine ⟨h.1, fun h0 => ?_, fun h0 => ?_⟩
  · have hb : Nat.beq (levF wv wl r) 0 = true := beq_iff.2 h0
    have h2 := h.2
    rw [hb] at h2
    exact beq_iff.1 h2
  · have hb : Nat.beq (levF wv wl r) 0 = false := by
      cases e : Nat.beq (levF wv wl r) 0
      · rfl
      · exact absurd (beq_iff.1 e) h0
    have h2 := h.2
    rw [hb] at h2
    change strictK _ _ = true at h2
    rw [strictK_eq] at h2
    change andB _ (andB _ (andB _ _)) = true at h2
    rw [andB_true_iff, andB_true_iff, andB_true_iff, blt_iff, blt_iff, blt_iff, beq_iff] at h2
    exact h2

theorem runOK_succ (i0 c x : ℕ) : runOK act ng valid root rec n wv wl wp i0 (c + 1) x =
    andB (Nat.blt (valF wv (rec (i0 + c))) x)
      (andB (recOK act ng valid root rec n wv wl wp (rec (i0 + c)))
        (runOK act ng valid root rec n wv wl wp i0 c (valF wv (rec (i0 + c))))) := rfl

theorem runOK_spec (i0 : ℕ) : ∀ (c x : ℕ), runOK act ng valid root rec n wv wl wp i0 c x = true →
    (∀ j < c, recOK act ng valid root rec n wv wl wp (rec (i0 + j)) = true) ∧
    (∀ j, j + 1 < c → valF wv (rec (i0 + j)) < valF wv (rec (i0 + (j + 1)))) ∧
    (c ≠ 0 → valF wv (rec (i0 + (c - 1))) < x)
  | 0, _, _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => by omega, fun h => absurd rfl h⟩
  | c + 1, x, h => by
    rw [runOK_succ, andB_true_iff, andB_true_iff, blt_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2, ih3⟩ := runOK_spec i0 c _ h3
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun _ => by simpa using h1⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact ih1 j hj
      · exact h2
    · by_cases hjc : j + 1 < c
      · exact ih2 j hjc
      · have e : j = c - 1 := by omega
        have hc : c ≠ 0 := by omega
        have e2 : j + 1 = c := by omega
        rw [e2]
        rw [e]
        exact ih3 hc

theorem chunk_spec {B c : ℕ} (h : chunkOK act ng valid root rec n wv wl wp B c = true) :
    (∀ j < min B (n - c * B), recOK act ng valid root rec n wv wl wp (rec (c * B + j)) = true) ∧
    (∀ j, j + 1 < min B (n - c * B) →
      valF wv (rec (c * B + j)) < valF wv (rec (c * B + (j + 1)))) ∧
    (min B (n - c * B) ≠ 0 → c * B + min B (n - c * B) < n →
      valF wv (rec (c * B + (min B (n - c * B) - 1))) <
        valF wv (rec (c * B + min B (n - c * B)))) := by
  have h' : runOK act ng valid root rec n wv wl wp (c * B) (cntF n B (c * B))
      (Bool.rec (motive := fun _ => ℕ) (pw2 wv) (valF wv (rec (c * B + cntF n B (c * B))))
        (Nat.blt (c * B + cntF n B (c * B)) n)) = true := h
  rw [cntF_eq] at h'
  obtain ⟨h1, h2, h3⟩ := runOK_spec _ _ _ h'
  refine ⟨h1, h2, fun hm hn => ?_⟩
  have e : Nat.blt (c * B + min B (n - c * B)) n = true := blt_iff.2 hn
  have := h3 hm
  rw [e] at this
  exact this

theorem split_idx {n B C i : ℕ} (hcov : n ≤ Nat.mul C B) (hi : i < n) :
    i / B < C ∧ i / B * B + i % B = i ∧ i % B < B := by
  have hcov' : n ≤ C * B := hcov
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.mul_zero] at hcov'
      omega
    · exact h0
  refine ⟨?_, Nat.div_add_mod' i B, Nat.mod_lt i hB⟩
  apply Nat.lt_of_mul_lt_mul_right (a := B)
  exact lt_of_le_of_lt (Nat.div_mul_le_self i B) (lt_of_lt_of_le hi hcov')

theorem tree_spec {B C : ℕ} (h : treeOK act ng valid root rec n wv wl wp B C = true) :
    (∀ i < n, recOK act ng valid root rec n wv wl wp (rec i) = true) ∧
    (∀ i, i + 1 < n → valF wv (rec i) < valF wv (rec (i + 1))) := by
  rw [treeOK, andB_true_iff, ble_iff, allN_iff] at h
  obtain ⟨hcov, hc⟩ := h
  constructor
  · intro i hi
    obtain ⟨hcC, e, hm⟩ := split_idx hcov hi
    have h1 := (chunk_spec (hc _ hcC)).1
    generalize i / B * B = t at *
    generalize i % B = j at *
    subst e
    exact h1 j (by omega)
  · intro i hi
    obtain ⟨hcC, e, hm⟩ := split_idx hcov (Nat.lt_of_succ_lt hi)
    obtain ⟨-, h2, h3⟩ := chunk_spec (hc _ hcC)
    generalize i / B * B = t at *
    generalize i % B = j at *
    subst e
    by_cases hj : j + 1 < B
    · exact h2 j (by omega)
    · have hmin : min B (n - t) = B := by omega
      rw [hmin] at h3
      have := h3 (by omega) (by omega)
      have e1 : t + (B - 1) = t + j := by omega
      have e2 : t + B = t + j + 1 := by omega
      rwa [e1, e2] at this

theorem val_lt_of_lt (hs : ∀ i, i + 1 < n → valF wv (rec i) < valF wv (rec (i + 1))) :
    ∀ {i j : ℕ}, i < j → j < n → valF wv (rec i) < valF wv (rec j)
  | _, 0, h, _ => absurd h (Nat.not_lt_zero _)
  | i, j + 1, h, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact lt_trans (val_lt_of_lt hs h (by omega)) (hs j hj)
    · exact hs i hj

theorem tree_reach (h : ∀ i < n, recOK act ng valid root rec n wv wl wp (rec i) = true) :
    ∀ i < n, Reach act ng root (valF wv (rec i)) ∧ ∃ j < n, valF wv (rec j) = root := by
  suffices H : ∀ L i, i < n → levF wv wl (rec i) ≤ L →
      Reach act ng root (valF wv (rec i)) ∧ ∃ j < n, valF wv (rec j) = root from
    fun i hi => H _ i hi le_rfl
  intro L
  induction L with
  | zero =>
    intro i hi hL
    have e := (recOK_spec (h i hi)).2.1 (by omega)
    rw [e]
    exact ⟨Reach.root, i, hi, e⟩
  | succ L ih =>
    intro i hi hL
    by_cases h0 : levF wv wl (rec i) = 0
    · exact ih i hi (by omega)
    · obtain ⟨hp, hg, hlev, e⟩ := (recOK_spec (h i hi)).2.2 h0
      obtain ⟨hr, hroot⟩ := ih _ hp (by omega)
      rw [← e]
      exact ⟨Reach.step _ hg hr, hroot⟩

theorem tree_sound {B C : ℕ} (h : treeOK act ng valid root rec n wv wl wp B C = true) :
    (∀ i < n, Reach act ng root (valF wv (rec i))) ∧ (∀ i < n, valid (valF wv (rec i)) = true) ∧
    (∀ i j, i < j → j < n → valF wv (rec i) < valF wv (rec j)) ∧
    (0 < n → ∃ j < n, valF wv (rec j) = root) := by
  obtain ⟨h1, h2⟩ := tree_spec h
  exact ⟨fun i hi => (tree_reach h1 i hi).1, fun i hi => (recOK_spec (h1 i hi)).1,
    fun i j hij hj => val_lt_of_lt h2 hij hj, fun hn => (tree_reach h1 0 hn).2⟩

theorem close_sound {E : ℕ → ℕ → ℕ} {B C : ℕ} (h : closeOK act ng rec E n wv B C = true) :
    ∀ i < n, ∀ k < ng, E i k < n ∧ act k (valF wv (rec i)) = valF wv (rec (E i k)) := by
  rw [closeOK, andB_true_iff, ble_iff, allN_iff] at h
  obtain ⟨hcov, hc⟩ := h
  intro i hi k hk
  obtain ⟨hcC, e, hm⟩ := split_idx hcov hi
  have h1 : closeRun act ng rec E n wv (i / B * B) (cntF n B (i / B * B)) = true := hc _ hcC
  rw [cntF_eq, closeRun, allN_iff] at h1
  generalize i / B * B = t at *
  generalize i % B = j at *
  subst e
  have h2 : allN ng (fun k => andB (Nat.blt (E (t + j) k) n)
      (Nat.beq (act k (valF wv (rec (t + j)))) (valF wv (rec (E (t + j) k))))) = true :=
    h1 j (by omega)
  rw [allN_iff] at h2
  have h3 := h2 k hk
  rw [andB_true_iff, blt_iff, beq_iff] at h3
  exact h3

theorem memK_sound {m : ℕ} (h : memK rec n wv m = true) : ∃ i < n, valF wv (rec i) = m := by
  unfold memK at h
  induction n with
  | zero => exact absurd h (by simp [anyN])
  | succ n ih =>
    change orB (Nat.beq (valF wv (rec n)) m) (anyN n _) = true at h
    cases e : Nat.beq (valF wv (rec n)) m
    · rw [e] at h
      obtain ⟨i, hi, hv⟩ := ih h
      exact ⟨i, by omega, hv⟩
    · exact ⟨n, by omega, beq_iff.1 e⟩

theorem orbit_sound {E : ℕ → ℕ → ℕ} {B C B' C' : ℕ} (hn : 0 < n)
    (hT : treeOK act ng valid root rec n wv wl wp B C = true)
    (hE : closeOK act ng rec E n wv B' C' = true) :
    ∃ S : Finset ℕ, (∀ x, Reach act ng root x ↔ x ∈ S) ∧ S.card = n ∧
      (∀ x ∈ S, valid x = true) ∧ (∀ x ∈ S, valF wv (rec 0) ≤ x) ∧
      (∀ x, x ∈ S ↔ ∃ i < n, valF wv (rec i) = x) := by
  obtain ⟨hr, hv, hlt, hroot⟩ := tree_sound hT
  have hc := close_sound hE
  let S := (Finset.range n).image fun i => valF wv (rec i)
  have hmem : ∀ x, x ∈ S ↔ ∃ i < n, valF wv (rec i) = x := by
    intro x
    simp [S]
  have hinj : Set.InjOn (fun i => valF wv (rec i)) (Finset.range n : Set ℕ) := by
    intro a ha b hb e
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with hab | rfl | hab
    · exact absurd e (ne_of_lt (hlt a b hab hb))
    · rfl
    · exact absurd e (ne_of_gt (hlt b a hab ha))
  obtain ⟨j0, hj0, ej0⟩ := hroot hn
  have hS : ∀ x, Reach act ng root x ↔ x ∈ S := by
    refine reach_iff_of_closed ((hmem _).2 ⟨j0, hj0, ej0⟩) (fun x hx k hk => ?_) (fun x hx => ?_)
    · obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
      rw [(hc i hi k hk).2]
      exact (hmem _).2 ⟨_, (hc i hi k hk).1, rfl⟩
    · obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
      exact hr i hi
  refine ⟨S, hS, ?_, fun x hx => ?_, fun x hx => ?_, hmem⟩
  · rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  · obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    exact hv i hi
  · obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exact le_rfl
    · exact le_of_lt (hlt _ _ h hi)

theorem natBfs_tree {E : ℕ → ℕ → ℕ} {B C B' C' fuel : ℕ} (hn : 0 < n) (hfuel : n ≤ fuel)
    (hT : treeOK act ng valid root rec n wv wl wp B C = true)
    (hE : closeOK act ng rec E n wv B' C' = true) :
    natCertOK act ng valid root (natBfs act ng root fuel) = true ∧
      (natBfs act ng root fuel).pts.size = n ∧
      ∀ x, x ∈ (natBfs act ng root fuel).pts ↔ ∃ i < n, valF wv (rec i) = x := by
  obtain ⟨S, hS, hcard, hv, -, hmem⟩ := orbit_sound hn hT hE
  obtain ⟨h1, h2, h3, -⟩ := natBfs_spec S hS hv (hcard ▸ hfuel)
  exact ⟨h1, h3.trans hcard, fun x => (h2 x).trans (hmem x)⟩

end CFSG.KC.SortTree

end
