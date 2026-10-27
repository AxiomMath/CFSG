module

public import Certificates.Data.Kernel.Misc.SylowG2K
public import CFSG.Certificates.Kernel.Misc.YamakiAutSound
public import CFSG.Certificates.Kernel.Misc.OmegaSixSound

public section

namespace CFSG.KC.SylowG2

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.SylowG2 CFSG.KD.YamakiAut CFSG.KD.BfsK
  CFSG.KC.BfsEnum CFSG.KC.YamakiAut CFSG.KC.OmegaSix CFSG.KC.YamakiS0 CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

theorem invPos3_sound {R : ℕ → ℕ} {o n : ℕ} : ∀ {ps : List (ℕ × ℕ)}, invPos3 R o n ps = true →
    ∀ p ∈ ps, p.1 < n ∧ recPOS R o 3 (p.1 * 3 + p.2) = 0
  | [], _ => by simp
  | (v, j) :: ps, h => by
    simp only [invPos3, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    obtain ⟨⟨hv, he⟩, hr⟩ := h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨hv, he⟩
    · exact invPos3_sound hr p hp

theorem autAt3_facts {R RP : ℕ → ℕ} {o : ℕ} {l0 l1 l2 : List ℕ} {ONEP t : ℕ}
    (h : autAt3 R RP o l0 l1 l2 ONEP t = true) :
    RP (recPOS R o 3 (t * 3 + 0)) = compL l0 (RP t) ∧
      RP (recPOS R o 3 (t * 3 + 1)) = compL l1 (RP t) ∧
      RP (recPOS R o 3 (t * 3 + 2)) = compL l2 (RP t) ∧ (RP t = ONEP ↔ t = 0) := by
  unfold autAt3 at h
  rw [CFSG.KC.YamakiRepF.strictY_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  refine ⟨a, b, c, ?_⟩
  have d' := beq_iff_eq.1 d
  constructor
  · intro e
    have : Nat.beq (RP t) ONEP = true := Nat.beq_eq.mpr e
    rw [this] at d'
    exact Nat.beq_eq.mp d'.symm
  · intro e
    have : Nat.beq t 0 = true := Nat.beq_eq.mpr e
    rw [this] at d'
    exact Nat.beq_eq.mp d'

variable {R RP : ℕ → ℕ} {o g : ℕ} {l0 l1 l2 lr li0 li1 li2 : List ℕ} {m n ONEP : ℕ} {E : Enum}
  {gs : Array (Array ℕ)}

theorem autAt3_of_chunks {L M : ℕ} (h : ∀ q < M, autChunk3 R RP o l0 l1 l2 ONEP n L q = true)
    (hm : n ≤ L * M) : ∀ t < n, autAt3 R RP o l0 l1 l2 ONEP t = true := by
  intro t ht
  have hL : 0 < L := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hm; omega
  have hq : t / L < M := (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm]; omega)
  have e := (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 (h _ hq) t (Nat.mul_div_le t L) (by
    have := Nat.lt_div_mul_add (a := t) hL
    rw [Nat.mul_comm] at this
    exact this)
  have hb : Nat.blt t n = true := Nat.blt_eq.mpr ht
  rw [hb, cond_true] at e
  exact e

theorem autOK_of_codes3
    (hE : BInvE (fun t => arrF (recX R o t)) (recF R o 0) (recF R o 1) n E) (hn : 0 < n)
    (h0 : recX R o 0 = ONE)
    (hB : ∀ i < n - 1, recF R o 0 i ≤ i ∧ recF R o 1 i < 3 ∧
      recX R o (i + 1) = MULF (recX R o (recF R o 0 i)) (R (g + recF R o 1 i)))
    (hlt : ∀ t < n, recX R o t < 2 ^ 36)
    (hstep : ∀ i < n * 3, recPOS R o 3 i < n ∧
      recX R o (recPOS R o 3 i) = MULF (recX R o (i / 3)) (R (g + i % 3)))
    (hgs : gs.size = 3) (hg : ∀ j < 3, gs[j]! = arrF (R (g + j)))
    (hm : m ≤ 64) (hl0 : l0.length = m) (hl1 : l1.length = m) (hl2 : l2.length = m)
    (hlr : lr.length = m)
    (hv0 : ∀ i < m, l0.getD i 0 < m ∧ li0.getD i 0 < m ∧ l0.getD (li0.getD i 0) 0 = i ∧
      li0.getD (l0.getD i 0) 0 = i)
    (hv1 : ∀ i < m, l1.getD i 0 < m ∧ li1.getD i 0 < m ∧ l1.getD (li1.getD i 0) 0 = i ∧
      li1.getD (l1.getD i 0) 0 = i)
    (hv2 : ∀ i < m, l2.getD i 0 < m ∧ li2.getD i 0 < m ∧ l2.getD (li2.getD i 0) 0 = i ∧
      li2.getD (l2.getD i 0) 0 = i)
    (hr : ∀ i < m, lr.getD i 0 = i) (hone : ∀ i < m, nib ONEP i = i)
    (hone' : compL lr ONEP = ONEP)
    {v0 v1 v2 : ℕ} (hinv : invPos3 R o n [(v0, 0), (v1, 1), (v2, 2)] = true)
    (hc : ∀ t < n, autAt3 R RP o l0 l1 l2 ONEP t = true) :
    autOK E gs #[arrL m l0, arrL m l1, arrL m l2]
        (buildF E #[arrL m l0, arrL m l1, arrL m l2]) = true ∧
      ∀ t < n, (buildF E #[arrL m l0, arrL m l1, arrL m l2])[t]! = encA m (RP t) := by
  have hE' := hE
  obtain ⟨e1, -, -, e4, e5, -, e7⟩ := hE
  let lj : ℕ → List ℕ := fun j => if j = 0 then l0 else if j = 1 then l1 else l2
  have hlj : ∀ j < 3, (lj j).length = m ∧ ∀ i < m, (lj j).getD i 0 < m := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact ⟨hl0, fun i hi => (hv0 i hi).1⟩
    · exact ⟨hl1, fun i hi => (hv1 i hi).1⟩
    · exact ⟨hl2, fun i hi => (hv2 i hi).1⟩
  have hsj : ∀ j < 3, (#[arrL m l0, arrL m l1, arrL m l2] : Array (Array ℕ))[j]! =
      arrL m (lj j) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
  have hP : ∀ i < n, ∀ j < 3, recPOS R o 3 (i * 3 + j) < n ∧
      recX R o (recPOS R o 3 (i * 3 + j)) = MULF (recX R o i) (R (g + j)) ∧
      RP (recPOS R o 3 (i * 3 + j)) = compL (lj j) (RP i) := by
    intro i hi j hj
    obtain ⟨s1, s2⟩ := hstep (i * 3 + j) (by omega)
    have hd : (i * 3 + j) / 3 = i := by omega
    have hm3 : (i * 3 + j) % 3 = j := by omega
    rw [hd, hm3] at s2
    obtain ⟨a, b, c, -⟩ := autAt3_facts (hc i hi)
    refine ⟨s1, s2, ?_⟩
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact a
    · exact b
    · exact c
  have hK : ∀ t < n, (RP t = ONEP ↔ t = 0) := fun t ht => (autAt3_facts (hc t ht)).2.2.2
  have hd : ∀ a < n, ∀ b < n, recX R o a = recX R o b → a = b := by
    intro a ha b hb e
    have h1 := e7 a ha
    have h2 := e7 b hb
    simp only at h1 h2
    rw [e] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  have hdisc : ∀ i < n - 1, recPOS R o 3 (recF R o 0 i * 3 + recF R o 1 i) = i + 1 := by
    intro i hi
    obtain ⟨b1, b2, b3⟩ := hB i hi
    obtain ⟨p1, p2, -⟩ := hP (recF R o 0 i) (by omega) (recF R o 1 i) b2
    exact hd _ p1 (i + 1) (by omega) (by rw [p2, b3])
  have hinjP : ∀ a < n, ∀ b < n, encF m (RP a) = encF m (RP b) → a = b := by
    have hv := fun p hp => invPos3_sound hinv p hp
    obtain ⟨hv0n, hp0⟩ := hv (v0, 0) (by simp)
    obtain ⟨hv1n, hp1⟩ := hv (v1, 1) (by simp)
    obtain ⟨hv2n, hp2⟩ := hv (v2, 2) (by simp)
    simp only at hv0n hp0 hv1n hp1 hv2n hp2
    have hunit : ∀ v j, v < n → j < 3 → recPOS R o 3 (v * 3 + j) = 0 →
        IsUnit (pkMat 6 (R (g + j))) := by
      intro v j hvn hj hp
      obtain ⟨-, p2, -⟩ := hP v hvn j hj
      rw [hp, h0] at p2
      refine matrix_isUnit (B := pkMat 6 (recX R o v)) ?_
      rw [← CFSG.KC.Sp62.pkMat_MULF, ← p2, pkMat_ONE]
    refine inj_of_tree (G := Matrix (Fin 6) (Fin 6) (ZMod 2)) (M := Function.End ℕ) (k := 3)
      (ψ := fun t => pkMat 6 (recX R o t)) (φ := fun t => encF m (RP t))
      (s := fun j => pkMat 6 (R (g + j))) (h := fun j => lF m (lj j))
      (POS := recPOS R o 3) (PA := recF R o 0) (PB := recF R o 1)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · beta_reduce
      rw [h0, pkMat_ONE]
    · beta_reduce
      have e := (hK 0 hn).2 rfl
      rw [e]
      funext p
      unfold encF
      by_cases hp : p < m
      · rw [if_pos hp, hone p hp]
        rfl
      · rw [if_neg hp]
        rfl
    · intro a ha b hb e
      exact hd a ha b hb (CFSG.KC.Sp62.pkMat_inj (hlt a ha) (hlt b hb) e)
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · exact hunit v0 0 hv0n (by norm_num) hp0
      · exact hunit v1 1 hv1n (by norm_num) hp1
      · exact hunit v2 2 hv2n (by norm_num) hp2
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · exact lF_isUnit hv0
      · exact lF_isUnit hv1
      · exact lF_isUnit hv2
    · intro i hi j hj
      obtain ⟨p1, p2, p3⟩ := hP i hi j hj
      refine ⟨p1, ?_, ?_⟩
      · beta_reduce
        rw [p2, CFSG.KC.Sp62.pkMat_MULF]
      · beta_reduce
        rw [p3, encF_mul (hlj j hj).1 (hlj j hj).2]
    · intro i hi
      obtain ⟨b1, b2, b3⟩ := hB i hi
      refine ⟨b1, b2, ?_⟩
      beta_reduce
      rw [b3, CFSG.KC.Sp62.pkMat_MULF]
    · intro t ht e
      by_contra h0t
      apply h0t
      apply (hK t ht).1
      obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
      obtain ⟨b1, b2, -⟩ := hB i (by omega)
      obtain ⟨-, -, p3⟩ := hP (recF R o 0 i) (by omega) (recF R o 1 i) b2
      rw [hdisc i (by omega)] at p3
      rw [p3, ← hone']
      refine compL_ext _ _ _ _ (by rw [hlr]; exact (hlj _ b2).1) fun q hq => ?_
      rw [(hlj _ b2).1] at hq
      rw [hr q hq, hone q hq, ← nib_compL _ _ _ (by rw [(hlj _ b2).1]; exact hq), ← p3]
      have := congrFun e q
      change encF m (RP (i + 1)) q = q at this
      unfold encF at this
      rwa [if_pos hq] at this
  have hpar : ∀ i, 1 ≤ i → i ≤ n - 1 → E.parent[i]! < i := by
    intro i h1 h2
    rw [(e5 i (by omega) (by omega)).1]
    have := (hB (i - 1) (by omega)).1
    omega
  obtain ⟨fs, f0, fr⟩ := buildF_spec E #[arrL m l0, arrL m l1, arrL m l2] (n := n - 1)
    (by rw [e1]; omega) hpar
  have hF : ∀ t < n, (buildF E #[arrL m l0, arrL m l1, arrL m l2])[t]! = encA m (RP t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      cases t with
      | zero =>
        rw [f0, (hK 0 hn).2 rfl]
        refine ext64 size_idA (by simp [encA]) fun i hi => ?_
        rw [idA_get hi, encA_get hi]
        by_cases h : i < m
        · rw [if_pos h, hone i h]
        · rw [if_neg h]
      | succ i =>
        obtain ⟨p1, p2⟩ := e5 (i + 1) ht (by omega)
        obtain ⟨b1, b2, -⟩ := hB i (by omega)
        rw [fr (i + 1) (by omega) (by omega), p1, p2, Nat.add_sub_cancel, hsj _ b2,
          ih _ (by omega) (by omega), compA_encA hm (hlj _ b2).1 (hlj _ b2).2,
          ← (hP (recF R o 0 i) (by omega) (recF R o 1 i) b2).2.2, hdisc i (by omega)]
  refine ⟨?_, hF⟩
  unfold autOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true]
  refine ⟨⟨⟨⟨by rw [fs, e1]; omega, ?_⟩, fun i hi => ?_⟩, fun i hi j hj => ?_⟩, ?_⟩
  · rw [Array.getElem?_eq_getElem (by rw [fs]; omega), ← getElem!_pos _ 0 (by rw [fs]; omega), f0]
  · rw [e1] at hi
    by_cases h0i : i = 0
    · exact Or.inl h0i
    · exact Or.inr (fr i (by omega) (by omega))
  · rw [e1] at hi
    rw [hgs] at hj
    have hl : E.lookup (compA E.elems[i]! gs[j]!) = some (recPOS R o 3 (i * 3 + j)) := by
      obtain ⟨p1, p2, -⟩ := hP i hi j hj
      rw [e4 i hi, hg j hj, arrF_mul, ← p2]
      exact lookup_of_inv hE' p1
    rw [hl]
    simp only [decide_eq_true_eq]
    obtain ⟨p1, -, p3⟩ := hP i hi j hj
    rw [hF _ p1, hF i hi, hsj j hj, compA_encA hm (hlj j hj).1 (hlj j hj).2, p3]
  · apply injOK_of_distinct
    intro a ha b hb e
    rw [fs] at ha hb
    refine hinjP a (by omega) b (by omega) (encF_of_encA hm ?_)
    rw [← hF a (by omega), ← hF b (by omega)]
    exact e

end CFSG.KC.SylowG2

end
