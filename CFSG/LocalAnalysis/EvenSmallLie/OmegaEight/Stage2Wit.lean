module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def invFixCheckW (E : Enum) (n : ℕ) (B : ℕ → List ℕ) : Bool :=
  (List.range E.keys.size).all fun i => mulK (E.keys.getD i 0) (E.keys.getD i 0) != idK ||
    (decide (n ≤ (B i).length) && fixLB (E.keys.getD i 0) (B i))

theorem fix_of_invFixCheckW {gs : Array (ℕ × ℕ)} {E : Enum} {n : ℕ} {B : ℕ → List ℕ}
    (hE : enumOK gs E = true) (h : invFixCheckW E n B = true) {y : GL12} (hy : y ∈ grpOf gs)
    (hy2 : y * y = 1) : 2 ^ n ≤ Nat.card (fixM (y : Mat12)) := by
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hy
  simp only [invFixCheckW, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    Bool.and_eq_true, decide_eq_true_eq] at h
  have hsq : mulK (E.keys.getD i 0) (E.keys.getD i 0) = idK :=
    (hr.mul hr).key_unique (by rw [hy2]; exact rep_one) (mulK_lt _ _) idK_lt
  rcases h i hi with h1 | ⟨h1, h2⟩
  · exact absurd hsq h1
  · rw [← fixM_of_rep hr]
    exact (Nat.pow_le_pow_right (by norm_num) h1).trans (fixLB_sound h2)

@[expose] def oneClassCheckW (E : Enum) (tK : ℕ) (B : ℕ → List ℕ) (Y : ℕ → ℕ) : Bool :=
  (List.range E.keys.size).all fun i => mulK (E.keys.getD i 0) (E.keys.getD i 0) != idK ||
    E.keys.getD i 0 == idK ||
    (decide (8 ≤ (B i).length) && fixLB (E.keys.getD i 0) (B i)) ||
    (decide (Y i < E.keys.size) &&
      mulK (E.keys.getD (Y i) 0) tK == mulK (E.keys.getD i 0) (E.keys.getD (Y i) 0))

theorem conj_of_oneClassCheckW {gs : Array (ℕ × ℕ)} {E : Enum} {tK : ℕ} {B : ℕ → List ℕ}
    {Y : ℕ → ℕ} (hE : enumOK gs E = true) (h : oneClassCheckW E tK B Y = true) {tb : GL12}
    (ht : Rep tK tb) {s : GL12} (hs : s ∈ grpOf gs) (hs2 : s * s = 1)
    (hfix : Nat.card (fixM (s : Mat12)) ≤ 2 ^ 7) : ∃ y ∈ grpOf gs, s = y * tb * y⁻¹ := by
  obtain ⟨i, hi, hr⟩ := Enum.exists_key hE hs
  simp only [oneClassCheckW, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h i hi with ((h1 | h1) | ⟨h1, h2⟩) | ⟨hj, h1⟩
  · exact absurd ((hr.mul hr).key_unique (by rw [hs2]; exact rep_one) (mulK_lt _ _) idK_lt) h1
  · rw [h1] at hr
    have : s = 1 := hr.unique rep_one
    rw [this, card_fixM_one] at hfix
    norm_num at hfix
  · rw [← fixM_of_rep hr] at hfix
    have := (Nat.pow_le_pow_right (by norm_num) h1).trans (fixLB_sound h2)
    omega
  · obtain ⟨y, hy, hry⟩ := Enum.exists_mem hE (Y i) hj
    refine ⟨y, hy, ?_⟩
    have e : y * tb = s * y := by
      have h3 := hry.mul ht
      rw [h1] at h3
      exact h3.unique (hr.mul hry)
    calc s = s * y * y⁻¹ := by group
      _ = y * tb * y⁻¹ := by rw [← e]

@[expose] def imgCheckW (tK : ℕ) (X : ℕ → ℕ) : Bool :=
  (List.range 4096).all fun v => mulVecK tK v != v || (mulVecK tK (X v) ^^^ X v) == v

theorem exists_of_imgCheckW {tK : ℕ} {X : ℕ → ℕ} (h : imgCheckW tK X = true) {v : Vec12}
    (hv : toMatK tK *ᵥ v = v) : ∃ x : Vec12, toMatK tK *ᵥ x + x = v := by
  simp only [imgCheckW, List.all_eq_true, List.mem_range, Bool.or_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  have hfix : mulVecK tK (vecBits v) = vecBits v := by
    apply toVec_injOn (mulVecK_lt _ _) (vecBits_lt _)
    rw [toVec_mulVecK, toVec_vecBits, hv]
  rcases h _ (vecBits_lt v) with h1 | hx
  · exact absurd hfix h1
  · refine ⟨toVec 12 (X (vecBits v)), ?_⟩
    rw [← toVec_mulVecK, ← toVec_xor, hx, toVec_vecBits]

@[expose] def candCheckW (EC E₂ : Enum) (samples : List ℕ) (reps : List (ℕ × ℕ)) (ys : List ℕ)
    (tuples : List (List ℕ)) (cases : List (List (ℕ × ℕ)))
    (L : ℕ → ℕ → List (List ℕ) × List ℕ × List ℕ) : Bool :=
  (List.range cases.length).all fun a => (List.range tuples.length).all fun b =>
    linCheckWith (candCons (tuples.getD b []) ys (cases.getD a [])) (L a b).1 (L a b).2.1
      (L a b).2.2 &&
    spanAll (L a b).2.1 (L a b).2.2.length fun m => !(candFilter E₂ samples m) || repOK EC reps m

theorem repOK_of_candCheckW {EC E₂ : Enum} {samples : List ℕ} {reps : List (ℕ × ℕ)}
    {ys : List ℕ} {tuples : List (List ℕ)} {cases : List (List (ℕ × ℕ))}
    {L : ℕ → ℕ → List (List ℕ) × List ℕ × List ℕ}
    (h : candCheckW EC E₂ samples reps ys tuples cases L = true) {a b : ℕ}
    (ha : a < cases.length) (hb : b < tuples.length) {m : ℕ} (hm : m < 2 ^ 144)
    (hsol : ∀ c ∈ candCons (tuples.getD b []) ys (cases.getD a []), mulK c.1 m = mulK m c.2)
    (hf : candFilter E₂ samples m = true) : repOK EC reps m = true := by
  simp only [candCheckW, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h a ha b hb
  have e := eq_linComb_of_linCheckWith h1 hm hsol
  simp only [spanAll, List.all_eq_true, List.mem_range] at h2
  have := h2 _ (freeBits_lt (L a b).2.2 m)
  rw [← e, hf] at this
  simpa using this

theorem exists_rep_of_candCheckW {cs c₂s : Array (ℕ × ℕ)} {EC E₂ : Enum} {samples : List ℕ}
    {reps : List (ℕ × ℕ)} {ys : List ℕ} {tuples : List (List ℕ)} {cases : List (List (ℕ × ℕ))}
    {L : ℕ → ℕ → List (List ℕ) × List ℕ × List ℕ}
    (hEC : enumOK cs EC = true) (hE₂ : enumOK c₂s E₂ = true) (hsz : E₂.keys.size < 2 ^ 64)
    (h : candCheckW EC E₂ samples reps ys tuples cases L = true)
    (hreps : reps.all (fun r => invPair r.1 r.2) = true)
    (hsamp : samples.all (memK E₂.keys) = true) {x : GL12} {a b : ℕ}
    (ha : a < cases.length) (hb : b < tuples.length)
    (hsol : ∀ c ∈ candCons (tuples.getD b []) ys (cases.getD a []),
      mulK c.1 (keyOfMat x) = mulK (keyOfMat x) c.2)
    (hx2 : x * x ∈ grpOf c₂s) (hx256 : x ^ 256 = 1)
    (hxn : ∀ c ∈ grpOf c₂s, x * c * x⁻¹ ∈ grpOf c₂s) :
    ∃ r ∈ reps, (glOf r.1 r.2)⁻¹ * x ∈ grpOf cs := by
  set k := keyOfMat x with hk
  have hr : Rep k x := rep_keyOfMat x
  have hinv : x ^ 255 = x⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hx256]
  have hf : candFilter E₂ samples k = true := by
    simp only [candFilter, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨Enum.memK_of_mem' hE₂ hsz hx2 (hr.mul hr) (mulK_lt _ _), ?_⟩, fun c hc => ?_⟩
    · exact (hr.fpow (by norm_num)).key_unique (by rw [hx256]; exact rep_one) (fpowK_lt _ _)
        idK_lt
    · simp only [List.all_eq_true] at hsamp
      obtain ⟨y, hy, hry⟩ := Enum.rep_of_memK hE₂ (hsamp c hc)
      have h1 : Rep (mulK (mulK k c) (fpowK k 255)) (x * y * x⁻¹) := by
        rw [← hinv]
        exact (hr.mul hry).mul (hr.fpow (by norm_num))
      exact Enum.memK_of_mem' hE₂ hsz (hxn y hy) h1 (mulK_lt _ _)
  have hok := repOK_of_candCheckW h ha hb (keyOfMat_lt _) hsol hf
  simp only [repOK, List.any_eq_true] at hok
  obtain ⟨r, hrm, hmem⟩ := hok
  refine ⟨r, hrm, ?_⟩
  simp only [List.all_eq_true] at hreps
  have h2 : Rep (mulK r.2 k) ((glOf r.1 r.2)⁻¹ * x) := (rep_glOf_inv (hreps r hrm)).mul hr
  exact Enum.mem_of_memK hEC hmem h2

end CFSG.EvenSmallLie.OmegaEight.Stage2
