module

public import Certificates.Data.Kernel.Misc.YamakiAutM
public import CFSG.Certificates.Kernel.Misc.YamakiAutSound

public section

namespace CFSG.KC.YamakiAutM

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.YamakiAutM CFSG.KD.BfsK CFSG.KC.BfsEnum
  CFSG.KC.YamakiS0 CFSG.KC.YamakiAut CFSG.KC.Misc.Spec
open CFSG.KD.Sp62 (MULF ONE)

theorem pair2_mod {x y : ℕ} (hx : x < 2 ^ 36) : pair2 x y % 2 ^ 36 = x := by
  unfold pair2
  change (x + 2 ^ 36 * y) % 2 ^ 36 = x
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem pair2_div {x y : ℕ} (hx : x < 2 ^ 36) : pair2 x y / 2 ^ 36 = y := by
  unfold pair2
  change (x + 2 ^ 36 * y) / 2 ^ 36 = y
  rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt hx, Nat.zero_add]

theorem autAtT_facts {R RT : ℕ → ℕ} {a0 a1 b0 b1 t : ℕ} (h : autAtT R RT a0 a1 b0 b1 t = true) :
    RT (recPOS R 14 2 (t * 2 + 0)) =
        pair2 (MULF (RT t % 2 ^ 36) a0) (MULF (RT t / 2 ^ 36) b0) ∧
      RT (recPOS R 14 2 (t * 2 + 1)) =
        pair2 (MULF (RT t % 2 ^ 36) a1) (MULF (RT t / 2 ^ 36) b1) ∧
      (RT t % 2 ^ 36 = ONE ↔ t = 0) ∧ (RT t / 2 ^ 36 = ONE ↔ t = 0) := by
  unfold autAtT at h
  rw [CFSG.KC.YamakiRepF.strictY_eq, CFSG.KC.YamakiRepF.strictY_eq,
    CFSG.KC.YamakiRepF.strictY_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  have key : ∀ x : ℕ, (Nat.beq x ONE == Nat.beq t 0) = true → (x = ONE ↔ t = 0) := by
    intro x hx
    have c' := beq_iff_eq.1 hx
    constructor
    · intro e
      rw [Nat.beq_eq.mpr e] at c'
      exact Nat.beq_eq.mp c'.symm
    · intro e
      rw [Nat.beq_eq.mpr e] at c'
      exact Nat.beq_eq.mp c'
  exact ⟨a, b, key _ c, key _ d⟩

theorem autAtT_left {R RT : ℕ → ℕ} {a0 a1 b0 b1 t : ℕ} (h : autAtT R RT a0 a1 b0 b1 t = true) :
    RT (recPOS R 14 2 (t * 2 + 0)) % 2 ^ 36 = MULF (RT t % 2 ^ 36) a0 ∧
      RT (recPOS R 14 2 (t * 2 + 1)) % 2 ^ 36 = MULF (RT t % 2 ^ 36) a1 ∧
      (RT t % 2 ^ 36 = ONE ↔ t = 0) := by
  obtain ⟨a, b, c, -⟩ := autAtT_facts h
  rw [a, b, pair2_mod (CFSG.KC.Sp62.MULF_lt _ _), pair2_mod (CFSG.KC.Sp62.MULF_lt _ _)]
  exact ⟨rfl, rfl, c⟩

theorem autAtT_right {R RT : ℕ → ℕ} {a0 a1 b0 b1 t : ℕ} (h : autAtT R RT a0 a1 b0 b1 t = true) :
    RT (recPOS R 14 2 (t * 2 + 0)) / 2 ^ 36 = MULF (RT t / 2 ^ 36) b0 ∧
      RT (recPOS R 14 2 (t * 2 + 1)) / 2 ^ 36 = MULF (RT t / 2 ^ 36) b1 ∧
      (RT t / 2 ^ 36 = ONE ↔ t = 0) := by
  obtain ⟨a, b, -, c⟩ := autAtT_facts h
  rw [a, b, pair2_div (CFSG.KC.Sp62.MULF_lt _ _), pair2_div (CFSG.KC.Sp62.MULF_lt _ _)]
  exact ⟨rfl, rfl, c⟩

theorem autAtT_of_chunks {R RT : ℕ → ℕ} {a0 a1 b0 b1 n L M : ℕ}
    (h : ∀ q < M, autChunkT R RT a0 a1 b0 b1 n L q = true)
    (hm : n ≤ L * M) : ∀ t < n, autAtT R RT a0 a1 b0 b1 t = true := by
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

variable {R RP : ℕ → ℕ} {n a0 a1 v0 v1 : ℕ} {E : Enum} {gs : Array (Array ℕ)}

theorem autOK_of_mcodes
    (hE : BInvE (fun t => arrN (recX R 14 t)) (recF R 14 0) (recF R 14 1) n E) (hn : 0 < n)
    (h0 : recX R 14 0 = ONE)
    (hB : ∀ i < n - 1, recF R 14 0 i ≤ i ∧ recF R 14 1 i < 2 ∧
      recX R 14 (i + 1) = MULF (recX R 14 (recF R 14 0 i)) (R (12 + recF R 14 1 i)))
    (hlt : ∀ t < n, recX R 14 t < 2 ^ 36)
    (hstep : ∀ i < n * 2, recPOS R 14 2 i < n ∧
      recX R 14 (recPOS R 14 2 i) = MULF (recX R 14 (i / 2)) (R (12 + i % 2)))
    (hgs : gs.size = 2) (hg : ∀ j < 2, gs[j]! = arrN (R (12 + j)))
    (hinv : CFSG.KD.YamakiAut.invPosK R n [(v0, 0), (v1, 1)] = true)
    (hc : ∀ t < n, RP (recPOS R 14 2 (t * 2 + 0)) = MULF (RP t) a0 ∧
      RP (recPOS R 14 2 (t * 2 + 1)) = MULF (RP t) a1 ∧ (RP t = ONE ↔ t = 0)) :
    autOK E gs #[arrN a0, arrN a1] (buildF E #[arrN a0, arrN a1]) = true ∧
      ∀ t < n, (buildF E #[arrN a0, arrN a1])[t]! = arrN (RP t) := by
  have hE' := hE
  obtain ⟨e1, -, -, e4, e5, -, e7⟩ := hE
  let aj : ℕ → ℕ := fun j => if j = 0 then a0 else a1
  have hsj : ∀ j < 2, (#[arrN a0, arrN a1] : Array (Array ℕ))[j]! = arrN (aj j) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rfl
    · rfl
  have hP : ∀ i < n, ∀ j < 2, recPOS R 14 2 (i * 2 + j) < n ∧
      recX R 14 (recPOS R 14 2 (i * 2 + j)) = MULF (recX R 14 i) (R (12 + j)) ∧
      RP (recPOS R 14 2 (i * 2 + j)) = MULF (RP i) (aj j) := by
    intro i hi j hj
    obtain ⟨s1, s2⟩ := hstep (i * 2 + j) (by omega)
    have hd : (i * 2 + j) / 2 = i := by omega
    have hm2 : (i * 2 + j) % 2 = j := by omega
    rw [hd, hm2] at s2
    obtain ⟨a, b, -⟩ := hc i hi
    refine ⟨s1, s2, ?_⟩
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact a
    · exact b
  have hK : ∀ t < n, (RP t = ONE ↔ t = 0) := fun t ht => (hc t ht).2.2
  have hd : ∀ a < n, ∀ b < n, recX R 14 a = recX R 14 b → a = b := by
    intro a ha b hb e
    have h1 := e7 a ha
    have h2 := e7 b hb
    simp only at h1 h2
    rw [e] at h1
    rw [h1] at h2
    exact Option.some.inj h2
  have hdisc : ∀ i < n - 1, recPOS R 14 2 (recF R 14 0 i * 2 + recF R 14 1 i) = i + 1 := by
    intro i hi
    obtain ⟨b1, b2, b3⟩ := hB i hi
    obtain ⟨p1, p2, -⟩ := hP (recF R 14 0 i) (by omega) (recF R 14 1 i) b2
    exact hd _ p1 (i + 1) (by omega) (by rw [p2, b3])
  have hRlt : ∀ t < n, RP t < 2 ^ 36 := by
    intro t ht
    cases t with
    | zero => rw [(hK 0 hn).2 rfl]; exact ONE_lt
    | succ i =>
      obtain ⟨b1, b2, -⟩ := hB i (by omega)
      obtain ⟨-, -, p3⟩ := hP (recF R 14 0 i) (by omega) (recF R 14 1 i) b2
      rw [hdisc i (by omega)] at p3
      rw [p3]
      exact CFSG.KC.Sp62.MULF_lt _ _
  have hinjP : ∀ a < n, ∀ b < n, pkMat 6 (RP a) = pkMat 6 (RP b) → a = b := by
    obtain ⟨⟨hv0n, hp0⟩, ⟨hv1n, hp1⟩⟩ : (v0 < n ∧ recPOS R 14 2 (v0 * 2 + 0) = 0) ∧
        (v1 < n ∧ recPOS R 14 2 (v1 * 2 + 1) = 0) :=
      ⟨invPosK_sound hinv (v0, 0) (by simp), invPosK_sound hinv (v1, 1) (by simp)⟩
    have hRP0 : RP 0 = ONE := (hK 0 hn).2 rfl
    refine inj_of_tree (G := Matrix (Fin 6) (Fin 6) (ZMod 2))
      (M := Matrix (Fin 6) (Fin 6) (ZMod 2)) (k := 2)
      (ψ := fun t => pkMat 6 (recX R 14 t)) (φ := fun t => pkMat 6 (RP t))
      (s := fun j => pkMat 6 (R (12 + j))) (h := fun j => pkMat 6 (aj j))
      (POS := recPOS R 14 2) (PA := recF R 14 0) (PB := recF R 14 1)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · beta_reduce
      rw [h0, pkMat_ONE]
    · beta_reduce
      rw [hRP0, pkMat_ONE]
    · intro a ha b hb e
      exact hd a ha b hb (CFSG.KC.Sp62.pkMat_inj (hlt a ha) (hlt b hb) e)
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · obtain ⟨-, p2, -⟩ := hP v0 hv0n 0 (by norm_num)
        rw [hp0, h0] at p2
        refine matrix_isUnit (B := pkMat 6 (recX R 14 v0)) ?_
        rw [← CFSG.KC.Sp62.pkMat_MULF, ← p2, pkMat_ONE]
      · obtain ⟨-, p2, -⟩ := hP v1 hv1n 1 (by norm_num)
        rw [hp1, h0] at p2
        refine matrix_isUnit (B := pkMat 6 (recX R 14 v1)) ?_
        rw [← CFSG.KC.Sp62.pkMat_MULF, ← p2, pkMat_ONE]
    · intro j hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · obtain ⟨-, -, p3⟩ := hP v0 hv0n 0 (by norm_num)
        rw [hp0, hRP0] at p3
        refine matrix_isUnit (B := pkMat 6 (RP v0)) ?_
        rw [← CFSG.KC.Sp62.pkMat_MULF, ← p3, pkMat_ONE]
      · obtain ⟨-, -, p3⟩ := hP v1 hv1n 1 (by norm_num)
        rw [hp1, hRP0] at p3
        refine matrix_isUnit (B := pkMat 6 (RP v1)) ?_
        rw [← CFSG.KC.Sp62.pkMat_MULF, ← p3, pkMat_ONE]
    · intro i hi j hj
      obtain ⟨p1, p2, p3⟩ := hP i hi j hj
      refine ⟨p1, ?_, ?_⟩
      · beta_reduce
        rw [p2, CFSG.KC.Sp62.pkMat_MULF]
      · beta_reduce
        rw [p3, CFSG.KC.Sp62.pkMat_MULF]
    · intro i hi
      obtain ⟨b1, b2, b3⟩ := hB i hi
      refine ⟨b1, b2, ?_⟩
      beta_reduce
      rw [b3, CFSG.KC.Sp62.pkMat_MULF]
    · intro t ht e
      apply (hK t ht).1
      refine CFSG.KC.Sp62.pkMat_inj (hRlt t ht) ONE_lt ?_
      rw [pkMat_ONE]
      exact e
  have hpar : ∀ i, 1 ≤ i → i ≤ n - 1 → E.parent[i]! < i := by
    intro i h1 h2
    rw [(e5 i (by omega) (by omega)).1]
    have := (hB (i - 1) (by omega)).1
    omega
  obtain ⟨fs, f0, fr⟩ := buildF_spec E #[arrN a0, arrN a1] (n := n - 1) (by rw [e1]; omega) hpar
  have hF : ∀ t < n, (buildF E #[arrN a0, arrN a1])[t]! = arrN (RP t) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      cases t with
      | zero => rw [f0, (hK 0 hn).2 rfl, arrN_one]
      | succ i =>
        obtain ⟨p1, p2⟩ := e5 (i + 1) ht (by omega)
        obtain ⟨b1, b2, -⟩ := hB i (by omega)
        rw [fr (i + 1) (by omega) (by omega), p1, p2, Nat.add_sub_cancel, hsj _ b2,
          ih _ (by omega) (by omega), arrN_mul,
          ← (hP (recF R 14 0 i) (by omega) (recF R 14 1 i) b2).2.2, hdisc i (by omega)]
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
    have hl : E.lookup (compA E.elems[i]! gs[j]!) = some (recPOS R 14 2 (i * 2 + j)) := by
      obtain ⟨p1, p2, -⟩ := hP i hi j hj
      rw [e4 i hi, hg j hj, arrN_mul, ← p2]
      exact lookup_of_inv hE' p1
    rw [hl]
    simp only [decide_eq_true_eq]
    obtain ⟨p1, -, p3⟩ := hP i hi j hj
    rw [hF _ p1, hF i hi, hsj j hj, arrN_mul, p3]
  · apply injOK_of_distinct
    intro a ha b hb e
    rw [fs] at ha hb
    refine hinjP a (by omega) b (by omega) ?_
    rw [arrN_inj (hRlt a (by omega)) (hRlt b (by omega))
      (by rw [← hF a (by omega), ← hF b (by omega)]; exact e)]

theorem arrN_size (N : ℕ) : (arrN N).size = 64 := size_matArr _

theorem arrN_lt (N : ℕ) {i : ℕ} (hi : i < 64) : (arrN N)[i]! < 64 := by
  unfold arrN
  rw [matArr_get _ hi]
  exact codeOf_lt _

theorem autOK_of_conj {T : ℕ → Array ℕ} {PA PB POS : ℕ → ℕ} {hs : Array (Array ℕ)}
    {π πi : Array ℕ} (hE : BInvE T PA PB n E) (hn : 0 < n) (hT0 : T 0 = idA ())
    (hB : ∀ i < n - 1, PA i ≤ i ∧ PB i < 2 ∧ T (i + 1) = compA (T (PA i)) gs[PB i]!)
    (hstep : ∀ i < n * 2, POS i < n ∧ T (POS i) = compA (T (i / 2)) gs[i % 2]!)
    (hTs : ∀ t < n, (T t).size = 64) (hTb : ∀ t < n, ∀ x < 64, (T t)[x]! < 64)
    (hgs : gs.size = 2) (hgb : ∀ j < 2, ∀ x < 64, (gs[j]!)[x]! < 64)
    (hπ : ∀ x < 64, π[x]! < 64 ∧ πi[x]! < 64 ∧ π[πi[x]!]! = x ∧ πi[π[x]!]! = x)
    (hc : ∀ j < 2, ∀ x < 64, π[(gs[j]!)[x]!]! = (hs[j]!)[π[x]!]!) :
    autOK E gs hs (buildF E hs) = true ∧
      ∀ t < n, (buildF E hs)[t]! = compA (compA π (T t)) πi := by
  have hE' := hE
  obtain ⟨e1, -, -, e4, e5, -, e7⟩ := hE
  have hhs : ∀ j < 2, ∀ x < 64, πi[(hs[j]!)[x]!]! = (gs[j]!)[πi[x]!]! := by
    intro j hj x hx
    obtain ⟨-, h2, h3, -⟩ := hπ x hx
    have e := hc j hj (πi[x]!) h2
    rw [h3] at e
    rw [← e, (hπ _ (hgb j hj _ h2)).2.2.2]
  have hΦ : ∀ t < n, ∀ x < 64, (compA (compA π (T t)) πi)[x]! = π[(T t)[πi[x]!]!]! := by
    intro t ht x hx
    rw [compA_get _ _ hx, compA_get _ _ (hπ x hx).2.1]
  have hpar : ∀ i, 1 ≤ i → i ≤ n - 1 → E.parent[i]! < i := by
    intro i h1 h2
    rw [(e5 i (by omega) (by omega)).1]
    have := (hB (i - 1) (by omega)).1
    omega
  obtain ⟨fs, f0, fr⟩ := buildF_spec E hs (n := n - 1) (by rw [e1]; omega) hpar
  have hF : ∀ t < n, (buildF E hs)[t]! = compA (compA π (T t)) πi := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      refine ext64 ?_ (size_compA _ _) fun x hx => ?_
      · cases t with
        | zero => rw [f0]; exact size_idA
        | succ i => rw [fr (i + 1) (by omega) (by omega)]; exact size_compA _ _
      rw [hΦ t ht x hx]
      cases t with
      | zero =>
        rw [f0, hT0, idA_get hx, idA_get (hπ x hx).2.1, (hπ x hx).2.2.1]
      | succ i =>
        obtain ⟨p1, p2⟩ := e5 (i + 1) ht (by omega)
        obtain ⟨b1, b2, b3⟩ := hB i (by omega)
        rw [fr (i + 1) (by omega) (by omega), p1, p2, Nat.add_sub_cancel, compA_get _ _ hx,
          ih _ (by omega) (by omega)]
        have hsx : (hs[PB i]!)[x]! < 64 := by
          have e := hc (PB i) b2 (πi[x]!) (hπ x hx).2.1
          rw [(hπ x hx).2.2.1] at e
          rw [← e]
          exact (hπ _ (hgb _ b2 _ (hπ x hx).2.1)).1
        rw [hΦ _ (by omega) _ hsx, hhs _ b2 x hx, b3, compA_get _ _ (hπ x hx).2.1]
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
    obtain ⟨s1, s2⟩ := hstep (i * 2 + j) (by omega)
    have hd : (i * 2 + j) / 2 = i := by omega
    have hm2 : (i * 2 + j) % 2 = j := by omega
    rw [hd, hm2] at s2
    have hl : E.lookup (compA E.elems[i]! gs[j]!) = some (POS (i * 2 + j)) := by
      rw [e4 i hi, ← s2]
      exact lookup_of_inv hE' s1
    rw [hl]
    simp only [decide_eq_true_eq]
    rw [hF _ s1, hF i hi]
    refine ext64 (size_compA _ _) (size_compA _ _) fun x hx => ?_
    have hsx : (hs[j]!)[x]! < 64 := by
      have e := hc j hj (πi[x]!) (hπ x hx).2.1
      rw [(hπ x hx).2.2.1] at e
      rw [← e]
      exact (hπ _ (hgb _ hj _ (hπ x hx).2.1)).1
    rw [hΦ _ s1 x hx, compA_get _ _ hx, hΦ i hi _ hsx, hhs j hj x hx, s2,
      compA_get _ _ (hπ x hx).2.1]
  · apply injOK_of_distinct
    intro a ha b hb e
    rw [fs] at ha hb
    rw [hF a (by omega), hF b (by omega)] at e
    have hT : T a = T b := by
      refine ext64 (hTs a (by omega)) (hTs b (by omega)) fun y hy => ?_
      have e' : (compA (compA π (T a)) πi)[π[y]!]! = (compA (compA π (T b)) πi)[π[y]!]! := by
        rw [e]
      rw [hΦ a (by omega) _ (hπ y hy).1, hΦ b (by omega) _ (hπ y hy).1, (hπ y hy).2.2.2] at e'
      have e'' := congrArg (fun z => πi[z]!) e'
      beta_reduce at e''
      rwa [(hπ _ (hTb a (by omega) y hy)).2.2.2, (hπ _ (hTb b (by omega) y hy)).2.2.2] at e''
    have h1 := e7 a (by omega)
    have h2 := e7 b (by omega)
    rw [hT, h2] at h1
    exact (Option.some.inj h1).symm

end CFSG.KC.YamakiAutM

end
