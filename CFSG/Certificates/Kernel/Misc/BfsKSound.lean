module

public import Certificates.Data.Kernel.Misc.BfsK
public import CFSG.Certificates.Kernel.G2Three.Tables

public section

namespace CFSG.KC.BfsK

open CFSG.KD.Sp62 (buildG stepG)
open CFSG.KD.BfsK CFSG.Quasithin.G2U

abbrev Enc (ok : List ℕ → Bool) (num : List ℕ → ℕ) (x : List ℕ) (N : ℕ) : Prop :=
  ok x = true ∧ num x = N

theorem buildG_at {st : ℕ → ℕ → ℕ} {X PA PB : ℕ → ℕ} {n k hi : ℕ}
    (h : buildG st X PA PB n k hi = true) (hm : n - 1 ≤ 64 * hi) :
    ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ X (i + 1) = st (X (PA i)) (PB i) := by
  intro i hi'
  have := CFSG.KC.G2Three.allBelow_g2 h hm i hi'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  exact ⟨h1, h2, h3⟩

theorem stepG_facts {st : ℕ → ℕ → ℕ} {X PA PB C POS : ℕ → ℕ} {n k hi : ℕ}
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

theorem push_tableE {E : List ℕ → ℕ → Prop} {start : List ℕ} {K : ℕ}
    {step : List ℕ → ℕ × ℕ → List ℕ} {stepP : ℕ → ℕ × ℕ → ℕ} {X : ℕ → ℕ}
    (hstep : ∀ x N ps, E x N → ps.2 < K → E (step x ps) (stepP N ps)) :
    ∀ (par : List (ℕ × ℕ)) (acc : Array (List ℕ)),
      (∀ i < par.length, (par.getD i (0, 0)).1 < acc.size + i ∧ (par.getD i (0, 0)).2 < K ∧
        X (acc.size + i) = stepP (X (par.getD i (0, 0)).1) (par.getD i (0, 0))) →
      (∀ t < acc.size, E (acc.getD t start) (X t)) →
      (par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 start) ps)) acc).size =
          acc.size + par.length ∧
        ∀ t < acc.size + par.length,
          E ((par.foldl (fun acc ps => acc.push (step (acc.getD ps.1 start) ps)) acc).getD
            t start) (X t)
  | [], acc, _, hacc => by simpa using hacc
  | ps :: par, acc, hpar, hacc => by
    have h0' := hpar 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0'
    obtain ⟨hp1, hp2, hp3⟩ := h0'
    have hc := hacc ps.1 hp1
    have hc' := hstep (acc.getD ps.1 start) _ ps hc hp2
    have hacc' : ∀ t < (acc.push (step (acc.getD ps.1 start) ps)).size,
        E ((acc.push (step (acc.getD ps.1 start) ps)).getD t start) (X t) := by
      intro t ht
      rw [Array.size_push] at ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
      · rw [CFSG.KC.G2Three.getD_push_lt start ht]
        exact hacc t ht
      · subst ht
        rw [CFSG.KC.G2Three.getD_push_eq, hp3]
        exact hc'
    have ih := push_tableE hstep par (acc.push (step (acc.getD ps.1 start) ps))
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

theorem tableE {ok : List ℕ → Bool} {num : List ℕ → ℕ}
    (hinj : ∀ a b, ok a = true → ok b = true → num a = num b → a = b)
    {start : List ℕ} {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)}
    {fuel n k hiB hiS hiT : ℕ} {st : ℕ → ℕ → ℕ} {X PA PB C POS SRT SRI : ℕ → ℕ}
    (hk : gens.length = k) (hk0 : 0 < k) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hst : ∀ x N, Enc ok num x N → ∀ s < k, ∀ d : List ℕ,
      Enc ok num (mul x (gens.getD s d)) (st N s))
    (h0 : Enc ok num start (X 0))
    (hB : buildG st X PA PB n k hiB = true) (hBm : n - 1 ≤ 64 * hiB)
    (hS : stepG st X PA PB C POS n k hiS = true) (hSm : n * k ≤ 64 * hiS)
    (hT : CFSG.KD.G2Three.sortK X SRT SRI n hiT = true) (hTm : n ≤ 64 * hiT) :
    bfsParents start mul gens fuel = (List.range (n - 1)).map (fun i => (PA i, PB i)) ∧
    (∀ ps ∈ (List.range (n - 1)).map (fun i => (PA i, PB i)), ps.2 < k) ∧
    (build start mul gens ((List.range (n - 1)).map (fun i => (PA i, PB i)))).size = n ∧
    closedCheck mul gens (build start mul gens ((List.range (n - 1)).map
      (fun i => (PA i, PB i)))) = true ∧
    distinctCheck (build start mul gens ((List.range (n - 1)).map (fun i => (PA i, PB i)))) =
      true ∧
    ∀ t < n, Enc ok num ((build start mul gens ((List.range (n - 1)).map
        (fun i => (PA i, PB i)))).getD t []) (X t) := by
  have hBi := buildG_at hB hBm
  obtain ⟨hC0, hCn, hSi⟩ := stepG_facts hS hSm
  have hX := CFSG.KC.G2Three.sort_inj hT hTm
  generalize hPL : (List.range (n - 1)).map (fun i => (PA i, PB i)) = PL
  have hPLlen : PL.length = n - 1 := by rw [← hPL]; simp
  have hPLget : ∀ i < n - 1, PL.getD i (0, 0) = (PA i, PB i) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [hPLlen]; exact hi)]
    simp [← hPL]
  have hPLk : ∀ ps ∈ PL, ps.2 < k := by
    intro ps hps
    rw [← hPL] at hps
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hps
    exact (hBi i (List.mem_range.1 hi)).2.1
  have key := push_tableE (E := Enc ok num) (start := start) (K := k)
    (step := fun x ps => mul x (gens.getD ps.2 start))
    (stepP := fun x ps => st x ps.2) (X := X)
    (fun x N ps hx hs => hst x N hx ps.2 hs start) PL #[start]
    (fun i hi => by
      rw [hPLlen] at hi
      obtain ⟨h1, h2, h3⟩ := hBi i hi
      rw [hPLget i hi]
      simp only [List.size_toArray, List.length_singleton]
      exact ⟨by omega, h2, by rw [Nat.add_comm]; exact h3⟩)
    (fun t ht => by
      have : t = 0 := by simpa using ht
      subst this
      simpa using h0)
  simp only [List.size_toArray, List.length_singleton] at key
  have hEsz : (build start mul gens PL).size = n := key.1.trans (by rw [hPLlen]; omega)
  have hrec : ∀ t < n, Enc ok num ((build start mul gens PL).getD t start) (X t) :=
    fun t ht => key.2 t (by rw [hPLlen]; omega)
  have hrec' : ∀ t < n, Enc ok num ((build start mul gens PL).getD t []) (X t) := by
    intro t ht
    rw [CFSG.KC.G2Three.getD_irrel (by rw [hEsz]; exact ht) [] start]
    exact hrec t ht
  have hd : ∀ t < (build start mul gens PL).size, ∀ t' < (build start mul gens PL).size,
      (build start mul gens PL).getD t [] = (build start mul gens PL).getD t' [] → t = t' := by
    intro t ht t' ht' he
    rw [hEsz] at ht ht'
    exact hX t ht t' ht' (by rw [← (hrec' t ht).2, ← (hrec' t' ht').2, he])
  have hprod : ∀ h < n, ∀ s < k, (build start mul gens PL).getD (POS (h * k + s)) [] =
      mul ((build start mul gens PL).getD h []) (gens.getD s []) := by
    intro h hh s hs
    obtain ⟨hi, hdiv, hmod⟩ := CFSG.KC.G2Three.flat_facts hk0 hh hs
    obtain ⟨-, -, hp, hx, -, -⟩ := hSi _ hi
    rw [hdiv, hmod] at hx
    obtain ⟨ch, ph⟩ := hrec' h hh
    obtain ⟨cp, pp⟩ := hrec' _ hp
    obtain ⟨cm, pm⟩ := hst _ _ (hrec' h hh) s hs []
    exact hinj _ _ cp cm (by rw [pp, hx, pm])
  obtain ⟨C', hC'lo, hC'hi⟩ : ∃ C' : ℕ → ℕ, (∀ i ≤ n * k, C' i = C i) ∧
      ∀ i, n * k ≤ i → C' i = n := by
    refine ⟨fun i => if i ≤ n * k then C i else n, fun i hi => if_pos hi, fun i hi => ?_⟩
    by_cases h : i ≤ n * k
    · have e : i = n * k := by omega
      simp only [if_pos h]
      rw [e, hCn]
    · exact if_neg h
  have hstep : ∀ h < fuel, ∀ s < gens.length,
      CFSG.KC.G2Three.StepOK mul gens (build start mul gens PL) PL.toArray C' POS h s
        (h * gens.length + s) := by
    intro h _ s hs
    rw [hk] at hs ⊢
    by_cases hhn : h < n
    · obtain ⟨hi, hdiv, hmod⟩ := CFSG.KC.G2Three.flat_facts hk0 hhn hs
      obtain ⟨a, b, c, -, e, f⟩ := hSi _ hi
      rw [hdiv] at a
      unfold CFSG.KC.G2Three.StepOK
      rw [hC'lo _ hi.le, hC'lo (h * k + s + 1) hi]
      refine ⟨fun _ => ⟨b, by rw [hEsz]; exact c, hprod h hhn s hs, fun hpc => ?_,
        fun hlt => f (Nat.ne_of_lt hlt)⟩, fun hn' => absurd a hn'⟩
      obtain ⟨e1, e2, e3⟩ := e hpc
      rw [hdiv] at e2
      rw [hmod] at e3
      refine ⟨e1, ?_⟩
      have hlt : C (h * k + s) - 1 < n - 1 := by omega
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
        hPLget _ hlt, e2, e3]
    · have hnk : n * k ≤ h * k := Nat.mul_le_mul_right k (by omega)
      have hi : n * k ≤ h * k + s := by omega
      unfold CFSG.KC.G2Three.StepOK
      rw [hC'hi _ hi, hC'hi (h * k + s + 1) (by omega)]
      exact ⟨fun hlt => absurd hlt (by omega), fun _ => rfl⟩
  have hPs : PL.toArray.size + 1 = (build start mul gens PL).size := by
    rw [List.size_toArray, hPLlen, hEsz]
    omega
  have hpar : bfsParents start mul gens fuel = PL := by
    have hfk : n * k ≤ fuel * k := Nat.mul_le_mul_right k hfuel
    have := CFSG.KC.G2Three.bfsParents_replay (C := C') (POS := POS)
      (build_getD_zero start mul gens PL) (by omega) hd
      hPs (by rw [hC'lo 0 (by omega), hC0]) hstep
      (by rw [hk, hC'hi (fuel * k) hfk, hEsz])
    simpa using this
  refine ⟨hpar, hPLk, hEsz, CFSG.KC.G2Three.closedCheck_of fun v hv g hg' => ?_,
    CFSG.KC.G2Three.distinctCheck_of hd, hrec'⟩
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg'
  have hsk : s < k := by omega
  rw [hEsz] at hv
  refine ⟨POS (v * k + s), ?_, ?_⟩
  · rw [hEsz]
    exact (hSi _ (CFSG.KC.G2Three.flat_facts hk0 hv hsk).1).2.2.1
  · rw [hprod v hv s hsk, List.getD_eq_getElem _ _ hs]

theorem tableKk_ok {ok : List ℕ → Bool} {num : List ℕ → ℕ}
    (hinj : ∀ a b, ok a = true → ok b = true → num a = num b → a = b)
    {start : List ℕ} {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)}
    {R : ℕ → ℕ} {st : ℕ → ℕ → ℕ} {fuel o n k hiB hiS hiT : ℕ}
    (hk : gens.length = k) (hk0 : 0 < k) (hn : 0 < n) (hfuel : n ≤ fuel)
    (hst : ∀ x N, Enc ok num x N → ∀ s < k, ∀ d : List ℕ,
      Enc ok num (mul x (gens.getD s d)) (st N s))
    (h0 : Enc ok num start (recX R o 0))
    (h : tableKk R st o n k hiB hiS hiT = true)
    (hBm : n - 1 ≤ 64 * hiB) (hSm : n * k ≤ 64 * hiS) (hTm : n ≤ 64 * hiT) :
    build start mul gens (bfsParents start mul gens fuel) =
      build start mul gens ((List.range (n - 1)).map (fun i => (recF R o 0 i, recF R o 1 i))) ∧
    (build start mul gens (bfsParents start mul gens fuel)).size = n ∧
    closedCheck mul gens (build start mul gens (bfsParents start mul gens fuel)) = true ∧
    distinctCheck (build start mul gens (bfsParents start mul gens fuel)) = true ∧
    ∀ t < n, Enc ok num ((build start mul gens (bfsParents start mul gens fuel)).getD t [])
      (recX R o t) := by
  simp only [tableKk, Bool.and_eq_true] at h
  obtain ⟨⟨hB, hS⟩, hT⟩ := h
  obtain ⟨hpar, -, hsz, hcl, hdi, hrec⟩ :=
    tableE hinj hk hk0 hn hfuel hst h0 hB hBm hS hSm hT hTm
  rw [hpar]
  exact ⟨rfl, hsz, hcl, hdi, hrec⟩

end CFSG.KC.BfsK

end
