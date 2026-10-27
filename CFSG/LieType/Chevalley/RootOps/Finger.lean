module

public import CFSG.LieType.Chevalley.RootOps.Fast
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley

@[expose] def pidx (e : Entry) : ℕ := e.1 * 256 + e.2.1

@[expose] def fpZ (L : List Entry) : ℤ :=
  (L.map fun e => e.2.2 * ((1 <<< (10 * pidx e) : ℕ) : ℤ)).sum

@[expose] def absSum (L : List Entry) : ℕ :=
  (L.map fun e => e.2.2.natAbs).sum

@[expose] def sumAt (L : List Entry) (k : ℕ) : ℤ :=
  (L.map fun e => if pidx e = k then e.2.2 else 0).sum

@[expose] def Bounded (N : ℕ) (L : List Entry) : Prop :=
  ∀ e ∈ L, e.2.1 < 256 ∧ pidx e < N

theorem sum_regroup {M : Type*} [AddCommGroup M] (N : ℕ) (g : ℕ → M) {L : List Entry}
    (hL : ∀ e ∈ L, pidx e < N) :
    (L.map fun e => e.2.2 • g (pidx e)).sum = ∑ k ∈ Finset.range N, sumAt L k • g k := by
  induction L with
  | nil => simp [sumAt]
  | cons e L ih =>
    rw [List.map_cons, List.sum_cons, ih fun f hf => hL f (List.mem_cons_of_mem _ hf)]
    simp only [sumAt, List.map_cons, List.sum_cons, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (pidx e)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_range.2 (hL e (List.mem_cons_self ..))) h

theorem abs_sumAt_le (L : List Entry) (k : ℕ) : |sumAt L k| ≤ absSum L := by
  induction L with
  | nil => simp [sumAt, absSum]
  | cons e L ih =>
    simp only [sumAt, absSum, List.map_cons, List.sum_cons] at ih ⊢
    refine (abs_add_le _ _).trans ?_
    rw [Nat.cast_add]
    refine add_le_add ?_ ih
    split_ifs
    · simp
    · simp

theorem eq_zero_of_sum_digits (B : ℤ) (hB : 0 < B) :
    ∀ (N : ℕ) (d : ℕ → ℤ), (∀ k < N, |d k| < B) → ∑ k ∈ Finset.range N, d k * B ^ k = 0 →
      ∀ k < N, d k = 0
  | 0, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | N + 1, d, hd, hs, k, hk => by
    rw [Finset.sum_range_succ'] at hs
    simp only [pow_zero, mul_one, pow_succ] at hs
    have hdvd : B ∣ d 0 := by
      refine ⟨-∑ i ∈ Finset.range N, d (i + 1) * B ^ i, ?_⟩
      have : ∑ i ∈ Finset.range N, d (i + 1) * (B ^ i * B) =
          B * ∑ i ∈ Finset.range N, d (i + 1) * B ^ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      linarith
    have h0 : d 0 = 0 := by
      obtain ⟨m, hm⟩ := hdvd
      have h1 := hd 0 (Nat.succ_pos _)
      rw [hm, abs_mul, abs_of_pos hB] at h1
      have hm0 : |m| < 1 := by
        by_contra hcon
        push Not at hcon
        nlinarith [abs_nonneg m]
      have : m = 0 := by
        rw [abs_lt] at hm0
        omega
      rw [hm, this, mul_zero]
    have hrest : ∑ i ∈ Finset.range N, d (i + 1) * B ^ i = 0 := by
      have : ∑ i ∈ Finset.range N, d (i + 1) * (B ^ i * B) =
          B * ∑ i ∈ Finset.range N, d (i + 1) * B ^ i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [this, h0, add_zero] at hs
      exact (mul_eq_zero.1 hs).resolve_left hB.ne'
    rcases k with _ | k
    · exact h0
    · exact eq_zero_of_sum_digits B hB N (fun i => d (i + 1))
        (fun i hi => hd (i + 1) (by omega)) hrest k (by omega)

theorem fpZ_eq_sum {N : ℕ} {L : List Entry} (hL : ∀ e ∈ L, pidx e < N) :
    fpZ L = ∑ k ∈ Finset.range N, sumAt L k * (2 ^ 10 : ℤ) ^ k := by
  have h := sum_regroup N (fun k => (2 ^ 10 : ℤ) ^ k) hL
  simp only [smul_eq_mul] at h
  rw [← h, fpZ]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  rw [Nat.one_shiftLeft, ← pow_mul]
  push_cast
  rfl

theorem sumAt_eq_of_fpZ_eq {N : ℕ} {L L' : List Entry} (hL : ∀ e ∈ L, pidx e < N)
    (hL' : ∀ e ∈ L', pidx e < N) (hb : absSum L < 2 ^ 9) (hb' : absSum L' < 2 ^ 9)
    (h : fpZ L = fpZ L') : ∀ k < N, sumAt L k = sumAt L' k := by
  have hs : ∑ k ∈ Finset.range N, (sumAt L k - sumAt L' k) * (2 ^ 10 : ℤ) ^ k = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [← fpZ_eq_sum hL, ← fpZ_eq_sum hL', h, sub_self]
  intro k hk
  have := eq_zero_of_sum_digits (2 ^ 10) (by norm_num) N (fun k => sumAt L k - sumAt L' k)
    (fun k _ => by
      have h1 := abs_sumAt_le L k
      have h2 := abs_sumAt_le L' k
      have hb1 : ((absSum L : ℕ) : ℤ) < 2 ^ 9 := by exact_mod_cast hb
      have hb2 : ((absSum L' : ℕ) : ℤ) < 2 ^ 9 := by exact_mod_cast hb'
      calc |sumAt L k - sumAt L' k| ≤ |sumAt L k| + |sumAt L' k| := abs_sub _ _
        _ < 2 ^ 10 := by norm_num at hb1 hb2 ⊢; linarith) hs k hk
  linarith

variable {τ : Tag} {R : Type*} [CommRing R]

theorem entriesOp_eq_sum {N : ℕ} {L : List Entry} (hL : Bounded N L) :
    entriesOp τ R L = ∑ k ∈ Finset.range N,
      sumAt L k • (posCoord τ R (k / 256)).smulRight (posVec τ R (k % 256)) := by
  have h := sum_regroup N (fun k => (posCoord τ R (k / 256)).smulRight (posVec τ R (k % 256)))
    (L := L) fun e he => (hL e he).2
  rw [← h, entriesOp]
  congr 1
  refine List.map_congr_left fun e he => ?_
  have hr := (hL e he).1
  have h1 : pidx e / 256 = e.1 := by unfold pidx; omega
  have h2 : pidx e % 256 = e.2.1 := by unfold pidx; omega
  rw [h1, h2, ← Int.cast_smul_eq_zsmul R]

theorem entriesOp_eq_of_fpZ_eq {N : ℕ} {L L' : List Entry} (hL : Bounded N L)
    (hL' : Bounded N L') (hb : absSum L < 2 ^ 9) (hb' : absSum L' < 2 ^ 9) (h : fpZ L = fpZ L') :
    entriesOp τ R L = entriesOp τ R L' := by
  rw [entriesOp_eq_sum hL, entriesOp_eq_sum hL']
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [sumAt_eq_of_fpZ_eq (fun e he => (hL e he).2) (fun e he => (hL' e he).2) hb hb' h k
    (Finset.mem_range.1 hk)]

@[expose] def bounded256 (L : List Entry) : Bool :=
  L.all fun e => Nat.blt e.1 256 && Nat.blt e.2.1 256

theorem bounded_of_bounded256 {L : List Entry} (h : bounded256 L = true) :
    Bounded 65536 L := by
  intro e he
  simp only [bounded256, List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h e he
  exact ⟨h2, by unfold pidx; omega⟩

@[expose] def summary : List Entry → Bool × ℕ × ℕ × ℕ
  | [] => (true, 0, 0, 0)
  | e :: L =>
    match summary L with
    | (b, n, fp, fn) =>
      (Nat.blt e.1 256 && Nat.blt e.2.1 256 && b, e.2.2.natAbs + n,
        match e.2.2 with
        | .ofNat z => (z <<< (10 * pidx e)) + fp
        | .negSucc _ => fp,
        match e.2.2 with
        | .ofNat _ => fn
        | .negSucc z => ((z + 1) <<< (10 * pidx e)) + fn)

theorem fpZ_cons (e : Entry) (L : List Entry) :
    fpZ (e :: L) = e.2.2 * ((1 <<< (10 * pidx e) : ℕ) : ℤ) + fpZ L :=
  rfl

theorem summary_spec (L : List Entry) :
    (summary L).1 = bounded256 L ∧ (summary L).2.1 = absSum L ∧
      ((summary L).2.2.1 : ℤ) - (summary L).2.2.2 = fpZ L := by
  induction L with
  | nil => simp [summary, bounded256, absSum, fpZ]
  | cons e L ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [summary]
    revert h1 h2 h3
    rcases summary L with ⟨b, n, fp, fn⟩
    intro h1 h2 h3
    simp only at h1 h2 h3
    refine ⟨?_, ?_, ?_⟩
    · simp only [bounded256, List.all_cons, h1, Bool.and_assoc]
    · simp only [absSum, List.map_cons, List.sum_cons, h2]
    · rw [fpZ_cons, ← h3]
      rcases e with ⟨c, p, z⟩
      rcases z with z | z
      · simp only [Nat.shiftLeft_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.one_mul,
          Int.ofNat_eq_natCast]
        push_cast
        ring
      · simp only [Nat.shiftLeft_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.one_mul,
          Int.negSucc_eq]
        push_cast
        ring

@[expose] def summaryEq (S S' : Bool × ℕ × ℕ × ℕ) : Bool :=
  S.1 && S'.1 && Nat.blt S.2.1 512 && Nat.blt S'.2.1 512 &&
    Nat.beq (S.2.2.1 + S'.2.2.2) (S'.2.2.1 + S.2.2.2)

theorem entriesOp_eq_of_summaryEq {L L' : List Entry}
    (h : summaryEq (summary L) (summary L') = true) : entriesOp τ R L = entriesOp τ R L' := by
  obtain ⟨h1, h2, h3⟩ := summary_spec L
  obtain ⟨h1', h2', h3'⟩ := summary_spec L'
  simp only [summaryEq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨hb1, hb2⟩, ha1⟩, ha2⟩, hfp⟩ := h
  replace hfp := Nat.eq_of_beq_eq_true hfp
  rw [h1] at hb1
  rw [h1'] at hb2
  rw [h2] at ha1
  rw [h2'] at ha2
  have hfp' : fpZ L = fpZ L' := by
    rw [← h3, ← h3']
    have := congrArg (fun n : ℕ => (n : ℤ)) hfp
    push_cast at this
    linarith
  exact entriesOp_eq_of_fpZ_eq (bounded_of_bounded256 hb1) (bounded_of_bounded256 hb2)
    (by norm_num; omega) (by norm_num; omega) hfp'

@[expose] def decodedAll (τ : Tag) (k : ℕ) : List (List Entry) :=
  (codes τ k).map (decodeEntries 128)

theorem entries_eq_decodedAll (τ : Tag) (a k : ℕ) :
    entries τ a k = (decodedAll τ k).getD a [] := by
  unfold entries decodedAll
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (codes τ k)[a]? <;> rfl

@[expose] def fingerCheckAux (τ : Tag) (i : Fin τ.rank) (L L' : List Entry) (s : ℤ) : Bool :=
  summaryEq (summary (conjEntries τ i L)) (summary (L'.map fun e => (e.1, e.2.1, s * e.2.2)))

@[expose] def fingerCheck (τ : Tag) (a : ℕ) (i : Fin τ.rank) (k : ℕ) : Bool :=
  fingerCheckAux τ i ((decodedAll τ k).getD a [])
    ((decodedAll τ k).getD (τ.rootCertificate.image a i) []) (signOf τ a i ^ k)

theorem conj_of_fingerCheckAux (htab : tabCheck τ = true) {i : Fin τ.rank} {L L' : List Entry}
    {s : ℤ} (hv : ValidEntries τ L) (h : fingerCheckAux τ i L L' s = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * entriesOp τ R L =
      (s : R) • (entriesOp τ R L' * (weylElt τ R i 1 : Module.End R (RootModule τ R))) := by
  have hc := entriesOp_eq_of_summaryEq (τ := τ) (R := R) h
  rw [entriesOp_map_smul] at hc
  rw [← entriesOp_conjEntries_mul htab i hv, hc, smul_mul_assoc]

theorem conj_of_fingerCheck (htab : tabCheck τ = true) {a : ℕ} {i : Fin τ.rank} {k : ℕ}
    (hv : validB τ (entries τ a k) = true) (h : fingerCheck τ a i k = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * entriesOp τ R (entries τ a k) =
      ((signOf τ a i ^ k : ℤ) : R) • (entriesOp τ R (entries τ (τ.rootCertificate.image a i) k) *
        (weylElt τ R i 1 : Module.End R (RootModule τ R))) := by
  rw [entries_eq_decodedAll] at hv ⊢
  rw [entries_eq_decodedAll]
  exact conj_of_fingerCheckAux htab (validEntries_of_validB hv) h

end CFSG.LieType.Chevalley.RootOps
