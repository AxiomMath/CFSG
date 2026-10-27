module

public import Certificates.Data.Kernel.Sp62Twin
public import Certificates.Data.Item434SmallTwoIII
public import CFSG.Certificates.Kernel.G2Three.Tables
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat

public section

namespace CFSG.KC.Sp62

open CFSG.KD.Sp62 CFSG.Quasithin.G2U CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.KC.Misc.Spec

theorem pk_cons (e : ℕ) (m : List ℕ) : pk (e :: m) = e + 2 * pk m := rfl

theorem pk_lt : ∀ m : List ℕ, (∀ e ∈ m, e < 2) → pk m < 2 ^ m.length
  | [], _ => by simp [pk]
  | e :: m, h => by
    have he := h e (by simp)
    have ih := pk_lt m fun x hx => h x (by simp [hx])
    rw [pk_cons, List.length_cons, pow_succ]
    omega

theorem testBit_pk : ∀ m : List ℕ, (∀ e ∈ m, e < 2) → ∀ t,
    (pk m).testBit t = decide (m.getD t 0 = 1)
  | [], _, t => by simp [pk]
  | e :: m, h, t => by
    have he := h e (by simp)
    have hm : ∀ x ∈ m, x < 2 := fun x hx => h x (by simp [hx])
    rw [pk_cons]
    cases t with
    | zero =>
      rw [Nat.testBit_zero, List.getD_cons_zero, decide_eq_decide]
      constructor <;> intro <;> omega
    | succ t =>
      rw [Nat.testBit_add_one, List.getD_cons_succ, ← testBit_pk m hm t]
      congr 1
      omega

theorem canon6_facts {m : List ℕ} (h : canon6 m = true) : m.length = 36 ∧ ∀ e ∈ m, e < 2 := by
  simpa only [canon6, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] using h

theorem canon_lt {m : List ℕ} (h : canon6 m = true) : pk m < 2 ^ 36 := by
  obtain ⟨hl, h2⟩ := canon6_facts h
  have := pk_lt m h2
  rwa [hl] at this

theorem dec6_eq_pkMat {m : List ℕ} (h : canon6 m = true) : dec6 m = pkMat 6 (pk m) := by
  have h2 := (canon6_facts h).2
  ext i j
  simp only [dec6, pkMat, Matrix.of_apply]
  rw [testBit_pk m h2]
  have hlt : m.getD (6 * (i : ℕ) + j) 0 < 2 := by
    rw [List.getD_eq_getElem?_getD]
    cases hx : m[6 * (i : ℕ) + j]? with
    | none => simp
    | some x => simpa using h2 x (List.mem_of_getElem? hx)
  rcases (by omega : m.getD (6 * (i : ℕ) + j) 0 = 0 ∨ m.getD (6 * (i : ℕ) + j) 0 = 1) with e | e <;>
    rw [e] <;> simp

theorem M36_eq : M36 = 2 ^ 36 - 1 := rfl

theorem MULF_lt (A B : ℕ) : MULF A B < 2 ^ 36 := by
  unfold MULF
  rw [M36_eq]
  exact Nat.and_lt_two_pow _ (by norm_num)

theorem testBit_MULF (A B p : ℕ) (hp : p < 36) :
    (MULF A B).testBit p = (CFSG.KC.Misc.G24.mulF2 6 A B).testBit p := by
  unfold MULF
  change ((CFSG.KC.Misc.G24.mulF2 6 A B) &&& M36).testBit p = _
  rw [Nat.testBit_and, M36_eq, Nat.testBit_two_pow_sub_one]
  simp [hp]

theorem pkMat_MULF (A B : ℕ) : pkMat 6 (MULF A B) = pkMat 6 A * pkMat 6 B := by
  rw [← pkMat_mulF2]
  ext i j
  have := i.isLt
  have := j.isLt
  simp only [pkMat, Matrix.of_apply]
  rw [testBit_MULF _ _ _ (by omega)]

theorem ite_inj : ∀ a b : Bool,
    ((if a then 1 else 0 : ZMod 2) = if b then 1 else 0) → a = b := by decide

theorem pkMat_inj {A B : ℕ} (hA : A < 2 ^ 36) (hB : B < 2 ^ 36) (h : pkMat 6 A = pkMat 6 B) :
    A = B := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 36
  · have := congrFun (congrFun h ⟨p / 6, by omega⟩) ⟨p % 6, by omega⟩
    simp only [pkMat, Matrix.of_apply, Fin.val_mk] at this
    have e : 6 * (p / 6) + p % 6 = p := by omega
    rw [e] at this
    exact ite_inj _ _ this
  · have h36 : 2 ^ 36 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem pk_inj {a b : List ℕ} (ha : canon6 a = true) (hb : canon6 b = true) (h : pk a = pk b) :
    a = b :=
  dec6_injective ha hb (by rw [dec6_eq_pkMat ha, dec6_eq_pkMat hb, h])

theorem pk_mul6 {a b : List ℕ} (ha : canon6 a = true) (hb : canon6 b = true) :
    pk (mul6 a b) = MULF (pk a) (pk b) :=
  pkMat_inj (canon_lt (canon6_mul6 a b)) (MULF_lt _ _) (by
    rw [← dec6_eq_pkMat (canon6_mul6 a b), dec6_mul6, dec6_eq_pkMat ha, dec6_eq_pkMat hb,
      pkMat_MULF])

theorem mulE {a b : List ℕ} {A B : ℕ} (ha : canon6 a = true ∧ pk a = A)
    (hb : canon6 b = true ∧ pk b = B) : canon6 (mul6 a b) = true ∧ pk (mul6 a b) = MULF A B :=
  ⟨canon6_mul6 a b, by rw [pk_mul6 ha.1 hb.1, ha.2, hb.2]⟩

theorem beq_pk {a b : List ℕ} (ha : canon6 a = true) (hb : canon6 b = true) :
    (a == b) = Nat.beq (pk a) (pk b) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]
  exact ⟨fun h => h ▸ rfl, pk_inj ha hb⟩

theorem pk_one6 : pk one6 = ONE := by decide +kernel

theorem one_pk : canon6 one6 = true ∧ pk one6 = ONE := ⟨canon6_one6, pk_one6⟩

theorem build_at6 {st : ℕ → ℕ → ℕ} {X PA PB : ℕ → ℕ} {n k hi : ℕ}
    (h : buildG st X PA PB n k hi = true) (hm : n - 1 ≤ 64 * hi) :
    ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ X (i + 1) = st (X (PA i)) (PB i) := by
  intro i hi'
  have := CFSG.KC.G2Three.allBelow_g2 h hm i hi'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  exact ⟨h1, h2, h3⟩

theorem step_facts6 {st : ℕ → ℕ → ℕ} {X PA PB C POS : ℕ → ℕ} {n k hi : ℕ}
    (h : stepG st X PA PB C POS n k hi = true) (hm : n * k ≤ 64 * hi) :
    C 0 = 1 ∧ C (n * k) = n ∧ ∀ i < n * k, i / k < C i ∧ POS i ≤ C i ∧ POS i < n ∧
      X (POS i) = st (X (i / k)) (i % k) ∧
      (POS i = C i → C (i + 1) = C i + 1 ∧ PA (C i - 1) = i / k ∧ PB (C i - 1) = i % k) ∧
      (POS i ≠ C i → C (i + 1) = C i) := by
  unfold stepG at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨h0, h1, fun i hi => ?_⟩
  have e := CFSG.KC.G2Three.allBelow_g2 h2 hm i hi
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at e
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := e
  refine ⟨a, b, c, d, fun hpc => ?_, fun hpc => ?_⟩
  · have hb : Nat.beq (POS i) (C i) = true := Nat.beq_eq.mpr hpc
    rw [hb, cond_true] at e
    simp only [Bool.and_eq_true, Nat.beq_eq] at e
    obtain ⟨⟨e1, e2⟩, e3⟩ := e
    rw [Nat.pred_eq_sub_one] at e2 e3
    exact ⟨e1, e2, e3⟩
  · have hb : Nat.beq (POS i) (C i) = false := by
      cases hq : Nat.beq (POS i) (C i)
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hq) hpc
    rw [hb, cond_false] at e
    exact Nat.eq_of_beq_eq_true e

theorem push_table6 {start : List ℕ} {K : ℕ} {step : List ℕ → ℕ × ℕ → List ℕ}
    {stepP : ℕ → ℕ × ℕ → ℕ} {X : ℕ → ℕ}
    (hstep : ∀ x ps, canon6 x = true → ps.2 < K →
      canon6 (step x ps) = true ∧ pk (step x ps) = stepP (pk x) ps) :
    ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)),
      (∀ i < par.length, (par.getD i (0, 0)).1 < acc.size + i ∧ (par.getD i (0, 0)).2 < K ∧
        X (acc.size + i) = stepP (X (par.getD i (0, 0)).1) (par.getD i (0, 0))) →
      (∀ t < acc.size, canon6 (acc.getD t start) = true ∧ pk (acc.getD t start) = X t) →
      (par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 start) ps)) acc).size =
          acc.size + par.length ∧
        ∀ t < acc.size + par.length,
          canon6 ((par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 start) ps)) acc).getD
            t start) = true ∧
          pk ((par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 start) ps)) acc).getD
            t start) = X t
  | [], acc, _, hacc => by simpa using hacc
  | ps :: par, acc, hpar, hacc => by
    have h0' := hpar 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0'
    obtain ⟨hp1, hp2, hp3⟩ := h0'
    obtain ⟨hc, hk⟩ := hacc ps.1 hp1
    obtain ⟨hc', hk'⟩ := hstep (acc.getD ps.1 start) ps hc hp2
    have hacc' : ∀ t < (acc.push (step (acc.getD ps.1 start) ps)).size,
        canon6 ((acc.push (step (acc.getD ps.1 start) ps)).getD t start) = true ∧
          pk ((acc.push (step (acc.getD ps.1 start) ps)).getD t start) = X t := by
      intro t ht
      rw [Array.size_push] at ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · rw [CFSG.KC.G2Three.getD_push_lt start ht]
        exact hacc t ht
      · subst ht
        rw [CFSG.KC.G2Three.getD_push_eq]
        exact ⟨hc', by rw [hk', hk, hp3]⟩
    have ih := push_table6 hstep par (acc.push (step (acc.getD ps.1 start) ps))
      (fun i hi => by
        have := hpar (i + 1) (by simp; omega)
        simp only [List.getD_cons_succ, Array.size_push] at this ⊢
        refine ⟨by omega, this.2.1, ?_⟩
        rw [(by omega : acc.size + 1 + i = acc.size + (i + 1))]
        exact this.2.2)
      hacc'
    simp only [Array.size_push] at ih
    rw [List.foldl_cons, List.length_cons]
    refine ⟨by rw [ih.1]; omega, fun t ht => ih.2 t (by omega)⟩

theorem table6 {start : List ℕ} {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)}
    {fuel n hiB hiS hiT : ℕ} {st : ℕ → ℕ → ℕ} {X PA PB C POS SRT SRI : ℕ → ℕ}
    (hk : gens.length = 2) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hst : ∀ x, canon6 x = true → ∀ s < 2, ∀ d : List ℕ,
      canon6 (mul x (gens.getD s d)) = true ∧ pk (mul x (gens.getD s d)) = st (pk x) s)
    (h0 : canon6 start = true ∧ pk start = X 0)
    (hB : buildG st X PA PB n 2 hiB = true) (hBm : n - 1 ≤ 64 * hiB)
    (hS : stepG st X PA PB C POS n 2 hiS = true) (hSm : n * 2 ≤ 64 * hiS)
    (hT : CFSG.KD.G2Three.sortK X SRT SRI n hiT = true) (hTm : n ≤ 64 * hiT) :
    bfsParents start mul gens fuel = (List.range (n - 1)).map (fun i => (PA i, PB i)) ∧
    (∀ ps ∈ (List.range (n - 1)).map (fun i => (PA i, PB i)), ps.2 < 2) ∧
    (build start mul gens ((List.range (n - 1)).map (fun i => (PA i, PB i)))).size = n ∧
    closedCheck mul gens (build start mul gens ((List.range (n - 1)).map
      (fun i => (PA i, PB i)))) = true ∧
    distinctCheck (build start mul gens ((List.range (n - 1)).map (fun i => (PA i, PB i)))) =
      true ∧
    ∀ t < n, canon6 ((build start mul gens ((List.range (n - 1)).map
        (fun i => (PA i, PB i)))).getD t []) = true ∧
      pk ((build start mul gens ((List.range (n - 1)).map
        (fun i => (PA i, PB i)))).getD t []) = X t := by
  have hBi := build_at6 hB hBm
  obtain ⟨hC0, hCn, hSi⟩ := step_facts6 hS hSm
  have hX := CFSG.KC.G2Three.sort_inj hT hTm
  generalize hPL : (List.range (n - 1)).map (fun i => (PA i, PB i)) = PL
  have hPLlen : PL.length = n - 1 := by rw [← hPL]; simp
  have hPLget : ∀ i < n - 1, PL.getD i (0, 0) = (PA i, PB i) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [hPLlen]; exact hi)]
    simp [← hPL]
  have hPL2 : ∀ ps ∈ PL, ps.2 < 2 := by
    intro ps hps
    rw [← hPL] at hps
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hps
    exact (hBi i (List.mem_range.1 hi)).2.1
  have key := push_table6 (start := start) (K := 2)
    (step := fun x ps => mul x (gens.getD ps.2 start))
    (stepP := fun x ps => st x ps.2) (X := X)
    (fun x ps hx hs => hst x hx ps.2 hs start) PL #[start]
    (fun i hi => by
      rw [hPLlen] at hi
      obtain ⟨h1, h2, h3⟩ := hBi i hi
      rw [hPLget i hi]
      simp only [List.size_toArray, List.length_singleton]
      exact ⟨by omega, h2, by rw [Nat.add_comm]; exact h3⟩)
    (fun t ht => by
      have : t = 0 := by simpa using ht
      subst this
      exact ⟨by simpa using h0.1, by simpa using h0.2⟩)
  simp only [List.size_toArray, List.length_singleton] at key
  have hEsz : (build start mul gens PL).size = n := key.1.trans (by rw [hPLlen]; omega)
  have hrec : ∀ t < n, canon6 ((build start mul gens PL).getD t start) = true ∧
      pk ((build start mul gens PL).getD t start) = X t :=
    fun t ht => key.2 t (by rw [hPLlen]; omega)
  have hrec' : ∀ t < n, canon6 ((build start mul gens PL).getD t []) = true ∧
      pk ((build start mul gens PL).getD t []) = X t := by
    intro t ht
    rw [CFSG.KC.G2Three.getD_irrel (by rw [hEsz]; exact ht) [] start]
    exact hrec t ht
  have hd : ∀ t < (build start mul gens PL).size, ∀ t' < (build start mul gens PL).size,
      (build start mul gens PL).getD t [] = (build start mul gens PL).getD t' [] → t = t' := by
    intro t ht t' ht' he
    rw [hEsz] at ht ht'
    exact hX t ht t' ht' (by rw [← (hrec' t ht).2, ← (hrec' t' ht').2, he])
  have hprod : ∀ h < n, ∀ s < 2, (build start mul gens PL).getD (POS (h * 2 + s)) [] =
      mul ((build start mul gens PL).getD h []) (gens.getD s []) := by
    intro h hh s hs
    obtain ⟨hi, hdiv, hmod⟩ := CFSG.KC.G2Three.flat_facts (by norm_num : 0 < 2) hh hs
    obtain ⟨-, -, hp, hx, -, -⟩ := hSi _ hi
    rw [hdiv, hmod] at hx
    obtain ⟨ch, ph⟩ := hrec' h hh
    obtain ⟨cp, pp⟩ := hrec' _ hp
    obtain ⟨cm, pm⟩ := hst _ ch s hs []
    exact pk_inj cp cm (by rw [pp, hx, pm, ph])
  obtain ⟨C', hC'lo, hC'hi⟩ : ∃ C' : ℕ → ℕ, (∀ i ≤ n * 2, C' i = C i) ∧
      ∀ i, n * 2 ≤ i → C' i = n := by
    refine ⟨fun i => if i ≤ n * 2 then C i else n, fun i hi => if_pos hi, fun i hi => ?_⟩
    by_cases h : i ≤ n * 2
    · have e : i = n * 2 := by omega
      simp only [if_pos h]
      rw [e, hCn]
    · exact if_neg h
  have hstep : ∀ h < fuel, ∀ s < gens.length,
      CFSG.KC.G2Three.StepOK mul gens (build start mul gens PL) PL.toArray C' POS h s
        (h * gens.length + s) := by
    intro h _ s hs
    rw [hk] at hs ⊢
    by_cases hhn : h < n
    · obtain ⟨hi, hdiv, hmod⟩ := CFSG.KC.G2Three.flat_facts (by norm_num : 0 < 2) hhn hs
      obtain ⟨a, b, c, -, e, f⟩ := hSi _ hi
      rw [hdiv] at a
      unfold CFSG.KC.G2Three.StepOK
      rw [hC'lo _ hi.le, hC'lo (h * 2 + s + 1) hi]
      refine ⟨fun _ => ⟨b, by rw [hEsz]; exact c, hprod h hhn s hs, fun hpc => ?_,
        fun hlt => f (Nat.ne_of_lt hlt)⟩, fun hn' => absurd a hn'⟩
      obtain ⟨e1, e2, e3⟩ := e hpc
      rw [hdiv] at e2
      rw [hmod] at e3
      refine ⟨e1, ?_⟩
      have hlt : C (h * 2 + s) - 1 < n - 1 := by omega
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
        hPLget _ hlt, e2, e3]
    · have hi : n * 2 ≤ h * 2 + s := by omega
      unfold CFSG.KC.G2Three.StepOK
      rw [hC'hi _ hi, hC'hi (h * 2 + s + 1) (by omega)]
      exact ⟨fun hlt => absurd hlt (by omega), fun _ => rfl⟩
  have hPs : PL.toArray.size + 1 = (build start mul gens PL).size := by
    rw [List.size_toArray, hPLlen, hEsz]
    omega
  have hpar : bfsParents start mul gens fuel = PL := by
    have := CFSG.KC.G2Three.bfsParents_replay (C := C') (POS := POS)
      (build_getD_zero start mul gens PL) (by omega) hd
      hPs (by rw [hC'lo 0 (by omega), hC0]) hstep
      (by rw [hk, hC'hi (fuel * 2) (by omega), hEsz])
    simpa using this
  refine ⟨hpar, hPL2, hEsz, CFSG.KC.G2Three.closedCheck_of fun v hv g hg' => ?_,
    CFSG.KC.G2Three.distinctCheck_of hd, hrec'⟩
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg'
  have hs2 : s < 2 := by omega
  rw [hEsz] at hv
  refine ⟨POS (v * 2 + s), ?_, ?_⟩
  · rw [hEsz]
    exact (hSi _ (CFSG.KC.G2Three.flat_facts (by norm_num : 0 < 2) hv hs2).1).2.2.1
  · rw [hprod v hv s hs2, List.getD_eq_getElem _ _ hs]

theorem closure6_ok {gens : List (List ℕ)} {G : ℕ → ℕ} {R : ℕ → ℕ} {o n hiB hiS hiT : ℕ}
    (hk : gens.length = 2) (hn : 0 < n) (hfuel : n ≤ 24000)
    (hg : ∀ s < 2, canon6 (gens.getD s []) = true ∧ pk (gens.getD s []) = G s)
    (h : (Nat.beq (recX R o 0) ONE && tableK R (rmulSt G) o n hiB hiS hiT) = true)
    (hBm : n - 1 ≤ 64 * hiB) (hSm : n * 2 ≤ 64 * hiS) (hTm : n ≤ 64 * hiT) :
    closureOK gens (closureT gens) n = true ∧
      ∀ t < n, canon6 ((closureT gens).getD t []) = true ∧
        pk ((closureT gens).getD t []) = recX R o t := by
  simp only [tableK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, ⟨hB, hS⟩, hT⟩ := h
  obtain ⟨hpar, -, hsz, hcl, hdi, hrec⟩ := table6 (start := one6) (mul := mul6) (gens := gens)
    (fuel := 24000) hk hn hfuel
    (fun x hx s hs d => by
      rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hk]; exact hs) d []]
      exact mulE ⟨hx, rfl⟩ (hg s hs))
    ⟨canon6_one6, by rw [pk_one6, h0]⟩ hB hBm hS hSm hT hTm
  have e : closureT gens = build one6 mul6 gens
      ((List.range (n - 1)).map (fun i => (recF R o 0 i, recF R o 1 i))) := by
    unfold closureT
    rw [hpar]
  rw [e]
  refine ⟨?_, hrec⟩
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨hsz, hcl⟩, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => (hrec t (by omega)).1⟩

theorem orbitBuild6_eq {t d : List ℕ} {gps : List (List ℕ)} (par : List (ℕ × ℕ))
    (hp : ∀ ps ∈ par, ps.2 < gps.length) (acc : Array (List ℕ)) :
    par.foldl (fun acc ps => acc.push (conjStep6 (gps.getD ps.2 d) (acc.getD ps.1 t))) acc =
      par.foldl (fun acc ps => acc.push (conjStep6 (gps.getD ps.2 t) (acc.getD ps.1 t))) acc := by
  induction par generalizing acc with
  | nil => rw [List.foldl_nil, List.foldl_nil]
  | cons ps par ih =>
    rw [List.foldl_cons, List.foldl_cons,
      CFSG.KC.G2Three.listGetD_irrel (hp ps List.mem_cons_self) d t]
    exact ih (fun q hq => hp q (List.mem_cons_of_mem _ hq)) _

theorem conj_pk {a b y : List ℕ} {A B Y : ℕ} (ha : canon6 a = true ∧ pk a = A)
    (hb : canon6 b = true ∧ pk b = B) (hy : canon6 y = true ∧ pk y = Y) :
    canon6 (conjStep6 (a ++ b) y) = true ∧ pk (conjStep6 (a ++ b) y) = MULF (MULF A Y) B := by
  have hl := (canon6_facts ha.1).1
  unfold conjStep6
  rw [List.take_left' hl, List.drop_left' hl]
  exact mulE (mulE ha hy) hb

theorem orbit6_ok {t0 : List ℕ} {gps : List (List ℕ)} {GA GB : ℕ → ℕ} {R : ℕ → ℕ}
    {fuel o a n hiB hiS hiT : ℕ} (hk : gps.length = 2) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hg : ∀ s < 2, ∃ x y, gps.getD s [] = x ++ y ∧ (canon6 x = true ∧ pk x = GA s) ∧
      (canon6 y = true ∧ pk y = GB s))
    (ht0 : canon6 t0 = true ∧ pk t0 = R a)
    (h : (Nat.beq (recX R o 0) (R a) && tableK R (conjSt GA GB) o n hiB hiS hiT) = true)
    (hBm : n - 1 ≤ 64 * hiB) (hSm : n * 2 ≤ 64 * hiS) (hTm : n ≤ 64 * hiT) :
    orbitOK (orbitBuild6 t0 gps (orbitParents6 t0 gps fuel)) n = true := by
  simp only [tableK, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨h0, ⟨hB, hS⟩, hT⟩ := h
  obtain ⟨hpar, hP2, hsz, -, hdi, hrec⟩ := table6 (start := t0)
    (mul := fun x gp => conjStep6 gp x) (gens := gps) (fuel := fuel) hk hn hfuel
    (fun x hx s hs d => by
      rw [CFSG.KC.G2Three.listGetD_irrel (by rw [hk]; exact hs) d []]
      obtain ⟨u, v, e, hu, hv⟩ := hg s hs
      rw [e]
      exact conj_pk hu hv ⟨hx, rfl⟩)
    ⟨ht0.1, by rw [ht0.2, h0]⟩ hB hBm hS hSm hT hTm
  have e : orbitBuild6 t0 gps (orbitParents6 t0 gps fuel) = build t0 (fun x gp => conjStep6 gp x)
      gps ((List.range (n - 1)).map (fun i => (recF R o 0 i, recF R o 1 i))) := by
    unfold orbitBuild6 orbitParents6 build
    rw [hpar]
    exact orbitBuild6_eq _ (fun ps hps => by rw [hk]; exact hP2 ps hps) _
  rw [e]
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hsz, hdi⟩, CFSG.KC.G2Three.allCheck_of fun t ht => (hrec t (by omega)).1⟩

theorem pow2k_pk {x : List ℕ} {A : ℕ} (hx : canon6 x = true ∧ pk x = A) :
    ∀ k, canon6 (pow2k x k) = true ∧ pk (pow2k x k) = P2K A k
  | 0 => hx
  | k + 1 => by
    have ih := pow2k_pk hx k
    unfold pow2k at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact mulE ih ih

theorem pow17920_pk {x : List ℕ} {A : ℕ} (hx : canon6 x = true ∧ pk x = A) :
    canon6 (pow17920 x) = true ∧ pk (pow17920 x) = P17920 A :=
  pow2k_pk (mulE (mulE (pow2k_pk hx 5) (mulE hx hx)) hx) 9

theorem finRange_three : List.finRange 3 = [0, 1, 2] := by decide

theorem hypPred_eq {bc y : List ℕ} {BC Y Z0 Z1 Z2 Z0I Z1I Z2I : ℕ}
    (hb : canon6 bc = true ∧ pk bc = BC) (hy : canon6 y = true ∧ pk y = Y)
    (hz0 : (canon6 (zPair 0).1 = true ∧ pk (zPair 0).1 = Z0) ∧
      (canon6 (zPair 0).2 = true ∧ pk (zPair 0).2 = Z0I))
    (hz1 : (canon6 (zPair 1).1 = true ∧ pk (zPair 1).1 = Z1) ∧
      (canon6 (zPair 1).2 = true ∧ pk (zPair 1).2 = Z1I))
    (hz2 : (canon6 (zPair 2).1 = true ∧ pk (zPair 2).1 = Z2) ∧
      (canon6 (zPair 2).2 = true ∧ pk (zPair 2).2 = Z2I)) :
    hypPred bc y = hypF BC Z0 Z1 Z2 Z0I Z1I Z2I Y := by
  have c1 := mulE hy hb
  have c2 := mulE hb hy
  have p := pow17920_pk hy
  have q0 := pow17920_pk (mulE hy (conj_pk hz0.1 hz0.2 hy))
  have q1 := pow17920_pk (mulE hy (conj_pk hz1.1 hz1.2 hy))
  have q2 := pow17920_pk (mulE hy (conj_pk hz2.1 hz2.2 hy))
  unfold hypPred commutes6
  rw [finRange_three]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [beq_pk c1.1 c2.1, c1.2, c2.2, beq_pk p.1 canon6_one6, p.2, pk_one6,
    beq_pk hy.1 canon6_one6, hy.2, beq_pk q0.1 canon6_one6, q0.2,
    beq_pk q1.1 canon6_one6, q1.2, beq_pk q2.1 canon6_one6, q2.2, pk_one6]
  simp only [hypF, Bool.or_assoc]

theorem powCode_pk {c : List ℕ} {A : ℕ} (h : canon6 c = true ∧ pk c = A) :
    ∀ n, canon6 (powCode c n) = true ∧ pk (powCode c n) = PW A n
  | 0 => one_pk
  | n + 1 => by
    have ih := powCode_pk h n
    unfold powCode at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact mulE ih h

theorem vecCode_pk (hz : ∀ i : Fin 3, canon6 (zCode i) = true) (a b c : ℕ) :
    canon6 (vecCode a b c) = true ∧ pk (vecCode a b c) =
      VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) a b c :=
  mulE (mulE (powCode_pk ⟨hz 0, rfl⟩ a) (powCode_pk ⟨hz 1, rfl⟩ b)) (powCode_pk ⟨hz 2, rfl⟩ c)

theorem pk_j6C : canon6 j6C = true ∧ pk j6C = J6 := ⟨by decide +kernel, by decide +kernel⟩

theorem pairCheck_eq {a b : List ℕ} {A B T : ℕ} (ha : canon6 a = true ∧ pk a = A)
    (hb : canon6 b = true ∧ pk b = B) (ht : canon6 (tr6 a) = true ∧ pk (tr6 a) = T) :
    pairCheck (a, b) = pairN A B T := by
  have h1 := mulE ha hb
  have h2 := mulE hb ha
  have h3 := mulE (mulE ht pk_j6C) ha
  unfold pairCheck pairN
  simp only [ha.1, hb.1, Bool.true_and]
  rw [beq_pk h1.1 canon6_one6, h1.2, beq_pk h2.1 canon6_one6, h2.2, beq_pk h3.1 pk_j6C.1, h3.2,
    pk_j6C.2, pk_one6]

theorem pairCheck_of {cc : List ℕ × List ℕ} (h : pairT cc = true) : pairCheck cc = true := by
  obtain ⟨a, b⟩ := cc
  simp only [pairT, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [pairCheck_eq ⟨h1, rfl⟩ ⟨h2, rfl⟩ ⟨h3, rfl⟩]
  exact h4

theorem all_pairs {l : List (List ℕ × List ℕ)} (h : l.all pairT = true) :
    l.all pairCheck = true := by
  rw [List.all_eq_true] at h ⊢
  exact fun cc hcc => pairCheck_of (h cc hcc)

theorem all_comm {l : List (List ℕ × List ℕ)} {a : List ℕ} {A : ℕ}
    (ha : canon6 a = true ∧ pk a = A)
    (h : l.all (fun cc => canon6 cc.1 && Nat.beq (MULF (pk cc.1) A) (MULF A (pk cc.1))) = true) :
    l.all (fun cc => commutes6 cc.1 a) = true := by
  rw [List.all_eq_true] at h ⊢
  intro cc hcc
  have e := h cc hcc
  rw [Bool.and_eq_true] at e
  unfold commutes6
  rw [beq_pk (mulE ⟨e.1, rfl⟩ ha).1 (mulE ha ⟨e.1, rfl⟩).1, (mulE ⟨e.1, rfl⟩ ha).2,
    (mulE ha ⟨e.1, rfl⟩).2]
  exact e.2

end CFSG.KC.Sp62

end
