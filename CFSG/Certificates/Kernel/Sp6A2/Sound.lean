module

public import Certificates.Data.Kernel.Sp6A2K
public import Certificates.Data.FF81Am6A2
public import CFSG.Certificates.Kernel.Sp62Pk.Sound

public section

namespace CFSG.KC.Sp6A2

open CFSG.KD.Sp62 CFSG.KD.Sp6A2 CFSG.KC.Sp62 CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec21.FF81.Am6
  CFSG.RankThree.PartTwo.Sec21.FF81.Am6.A2Data

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem stepH_facts {st : ℕ → ℕ → ℕ} {X PA PB C POS : ℕ → ℕ} {H n k hi : ℕ}
    (h : stepH st X PA PB C POS H n k hi = true) (hm : H * k ≤ 64 * hi) :
    C 0 = 1 ∧ C (H * k) = n ∧ ∀ i < H * k, i / k < C i ∧ i / k < n ∧ POS i ≤ C i ∧ POS i < n ∧
      X (POS i) = st (X (i / k)) (i % k) ∧
      (POS i = C i → C (i + 1) = C i + 1 ∧ PA (C i - 1) = i / k ∧ PB (C i - 1) = i % k) ∧
      (POS i ≠ C i → C (i + 1) = C i) := by
  unfold stepH at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨h0, h1, fun i hi => ?_⟩
  have e := CFSG.KC.G2Three.allBelow_g2 h2 hm i hi
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at e
  obtain ⟨⟨⟨⟨⟨a, a'⟩, b⟩, c⟩, d⟩, e⟩ := e
  refine ⟨a, a', b, c, d, fun hpc => ?_, fun hpc => ?_⟩
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

theorem tableP {start : List ℕ} {mul : List ℕ → List ℕ → List ℕ} {gens : List (List ℕ)}
    {H n hiB hiS hiT : ℕ} {st : ℕ → ℕ → ℕ} {X PA PB C POS SRT SRI : ℕ → ℕ}
    (hk : gens.length = 2) (hn : 0 < n)
    (hst : ∀ x, canon6 x = true → ∀ s < 2, ∀ d : List ℕ,
      canon6 (mul x (gens.getD s d)) = true ∧ pk (mul x (gens.getD s d)) = st (pk x) s)
    (h0 : canon6 start = true ∧ pk start = X 0)
    (hB : buildG st X PA PB n 2 hiB = true) (hBm : n - 1 ≤ 64 * hiB)
    (hS : stepH st X PA PB C POS H n 2 hiS = true) (hSm : H * 2 ≤ 64 * hiS)
    (hT : CFSG.KD.G2Three.sortK X SRT SRI n hiT = true) (hTm : n ≤ 64 * hiT) :
    bfsParents start mul gens H = (List.range (n - 1)).map (fun i => (PA i, PB i)) ∧
    (build start mul gens ((List.range (n - 1)).map (fun i => (PA i, PB i)))).size = n ∧
    distinctCheck (build start mul gens ((List.range (n - 1)).map (fun i => (PA i, PB i)))) =
      true ∧
    ∀ t < n, canon6 ((build start mul gens ((List.range (n - 1)).map
        (fun i => (PA i, PB i)))).getD t []) = true ∧
      pk ((build start mul gens ((List.range (n - 1)).map
        (fun i => (PA i, PB i)))).getD t []) = X t := by
  have hBi := build_at6 hB hBm
  obtain ⟨hC0, hCn, hSi⟩ := stepH_facts hS hSm
  have hX := CFSG.KC.G2Three.sort_inj hT hTm
  generalize hPL : (List.range (n - 1)).map (fun i => (PA i, PB i)) = PL
  have hPLlen : PL.length = n - 1 := by rw [← hPL]; simp
  have hPLget : ∀ i < n - 1, PL.getD i (0, 0) = (PA i, PB i) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [hPLlen]; exact hi)]
    simp [← hPL]
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
  have hprod : ∀ h < H, ∀ s < 2, (build start mul gens PL).getD (POS (h * 2 + s)) [] =
      mul ((build start mul gens PL).getD h []) (gens.getD s []) := by
    intro h hh s hs
    obtain ⟨hi, hdiv, hmod⟩ := CFSG.KC.G2Three.flat_facts (by norm_num : 0 < 2) hh hs
    obtain ⟨-, hn', -, hp, hx, -, -⟩ := hSi _ hi
    rw [hdiv, hmod] at hx
    rw [hdiv] at hn'
    obtain ⟨ch, ph⟩ := hrec' h hn'
    obtain ⟨cp, pp⟩ := hrec' _ hp
    obtain ⟨cm, pm⟩ := hst _ ch s hs []
    exact pk_inj cp cm (by rw [pp, hx, pm, ph])
  have hstep : ∀ h < H, ∀ s < gens.length,
      CFSG.KC.G2Three.StepOK mul gens (build start mul gens PL) PL.toArray C POS h s
        (h * gens.length + s) := by
    intro h hh s hs
    rw [hk] at hs ⊢
    obtain ⟨hi, hdiv, hmod⟩ := CFSG.KC.G2Three.flat_facts (by norm_num : 0 < 2) hh hs
    obtain ⟨a, -, b, c, -, e, f⟩ := hSi _ hi
    rw [hdiv] at a
    unfold CFSG.KC.G2Three.StepOK
    refine ⟨fun _ => ⟨b, by rw [hEsz]; exact c, hprod h hh s hs, fun hpc => ?_,
      fun hlt => f (Nat.ne_of_lt hlt)⟩, fun hn' => absurd a hn'⟩
    obtain ⟨e1, e2, e3⟩ := e hpc
    rw [hdiv] at e2
    rw [hmod] at e3
    refine ⟨e1, ?_⟩
    have hlt : C (h * 2 + s) - 1 < n - 1 := by omega
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
      hPLget _ hlt, e2, e3]
  have hPs : PL.toArray.size + 1 = (build start mul gens PL).size := by
    rw [List.size_toArray, hPLlen, hEsz]
    omega
  have hpar : bfsParents start mul gens H = PL := by
    have := CFSG.KC.G2Three.bfsParents_replay (C := C) (POS := POS)
      (build_getD_zero start mul gens PL) (by omega) hd hPs hC0 hstep
      (by rw [hk, hCn, hEsz])
    simpa using this
  exact ⟨hpar, hEsz, CFSG.KC.G2Three.distinctCheck_of hd, hrec'⟩

theorem isThree_eq {w : List ℕ} {W : ℕ} (hw : canon6 w = true ∧ pk w = W) :
    isThree w = threeF W := by
  have m := mulE (mulE hw hw) hw
  unfold isThree threeF
  rw [strictB_eq, beq_pk hw.1 canon6_one6, hw.2, pk_one6, beq_pk m.1 canon6_one6, m.2, pk_one6]

theorem found_of_rec {O : Array (List ℕ)} {R : ℕ → ℕ} {o pos : ℕ} {u : List ℕ}
    (hO : O.size = 168 ∧
      ∀ t < 168, canon6 (O.getD t []) = true ∧ pk (O.getD t []) = recX R o t)
    (hu : canon6 u = true) (hp : pos < 168) (he : recX R o pos = pk u) :
    found O (indexMap O) u = true := by
  obtain ⟨c, p⟩ := hO.2 pos hp
  exact CFSG.KC.G2Three.found_indexMap.2 ⟨pos, by rw [hO.1]; exact hp, pk_inj c hu (by rw [p, he])⟩

theorem scanOne_of {R8 R : ℕ → ℕ} {z hx o8 dk t o0 o1 o2 : ℕ} {τ : List ℕ}
    (hz : canon6 a2Z7 = true ∧ pk a2Z7 = z)
    (hτ : canon6 τ = true ∧ pk τ = recX R8 o8 t)
    (hX0 : (a2XTab 0).size = 168 ∧ ∀ t < 168, canon6 ((a2XTab 0).getD t []) = true ∧
      pk ((a2XTab 0).getD t []) = recX R o0 t)
    (hX1 : (a2XTab 1).size = 168 ∧ ∀ t < 168, canon6 ((a2XTab 1).getD t []) = true ∧
      pk ((a2XTab 1).getD t []) = recX R o1 t)
    (hX2 : (a2XTab 2).size = 168 ∧ ∀ t < 168, canon6 ((a2XTab 2).getD t []) = true ∧
      pk ((a2XTab 2).getD t []) = recX R o2 t)
    (ho : R hx = o0 ∧ R (hx + 1) = o1 ∧ R (hx + 2) = o2)
    (h : scanF R8 R z hx o8 dk t = true) :
    scanOne (indexMap (a2XTab 0)) (indexMap (a2XTab 1)) (indexMap (a2XTab 2)) τ = true := by
  unfold scanF at h
  rw [strictB_eq] at h
  generalize recX R8 o8 t = x at h hτ
  have hw := mulE hz hτ
  unfold scanOne
  rw [isThree_eq hw]
  cases h3 : threeF (MULF z x)
  · rfl
  rw [h3] at h
  dsimp only at h
  rw [strictB_eq] at h
  generalize R (Nat.add dk t) = d at h
  unfold capF at h
  generalize Nat.land (Nat.shiftRight d 0) 1048575 = o at h
  generalize Nat.land (Nat.shiftRight d 20) 1023 = n at h
  generalize Nat.land (Nat.shiftRight d 30) 3 = xi at h
  generalize Nat.land (Nat.shiftRight d 32) 255 = pos at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h2o, hz'⟩, hx'⟩, h1⟩, hT⟩, h168⟩, h384⟩, hor⟩ := h
  unfold tableH at hT
  simp only [Bool.and_eq_true] at hT
  obtain ⟨⟨hB, hS⟩, hTs⟩ := hT
  have e0 : at2 R (Nat.sub o 2) 0 = z := by
    simp only [at2, Nat.add_eq, Nat.add_zero]
    exact hz'
  have e1 : at2 R (Nat.sub o 2) 1 = x := by
    simp only [at2, Nat.add_eq, Nat.sub_eq] at hx' ⊢
    rw [(by omega : o - 2 + 1 = o - 1)]
    exact hx'
  obtain ⟨hpar, hsz, hdi, hrec⟩ := tableP (start := one6) (mul := mul6) (gens := [a2Z7, τ])
    (H := 168) rfl (by omega)
    (fun y hy s hs d' => by
      rw [CFSG.KC.G2Three.listGetD_irrel (by simp; omega) d' []]
      rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
      · have := mulE ⟨hy, rfl⟩ hz
        simp only [List.getD_cons_zero, rmulSt, e0]
        exact this
      · have := mulE ⟨hy, rfl⟩ hτ
        simp only [List.getD_cons_succ, List.getD_cons_zero, rmulSt, e1]
        exact this)
    ⟨canon6_one6, by rw [pk_one6, h1]⟩ hB (by omega) hS (by omega) hTs (by omega)
  have ecap : capTab [a2Z7, τ] = build one6 mul6 [a2Z7, τ]
      ((List.range (n - 1)).map (fun i => (recF R o 0 i, recF R o 1 i))) := by
    unfold capTab
    rw [hpar]
  have hge : ∀ m ≤ n, tabGe m (capTab [a2Z7, τ]) = true := by
    intro m hm
    unfold tabGe
    rw [ecap, hsz, hdi, CFSG.KC.G2Three.allCheck_of fun t ht => (hrec t (by omega)).1]
    simp [hm]
  simp only [Bool.not_true, Bool.false_or]
  rw [hge 168 h168]
  rcases hor with h169 | ⟨⟨hxi, hpos⟩, hmem⟩
  · rw [hge 169 h169]
    rfl
  · rcases (by omega : xi = 0 ∨ xi = 1 ∨ xi = 2) with rfl | rfl | rfl
    · simp only [Nat.add_eq, Nat.add_zero, ho.1] at hmem
      rw [found_of_rec hX0 hτ.1 hpos (by rw [hmem, hτ.2])]
      simp
    · simp only [Nat.add_eq, ho.2.1] at hmem
      rw [found_of_rec hX1 hτ.1 hpos (by rw [hmem, hτ.2])]
      simp
    · simp only [Nat.add_eq, ho.2.2] at hmem
      rw [found_of_rec hX2 hτ.1 hpos (by rw [hmem, hτ.2])]
      simp

theorem scanK_at {R8 R : ℕ → ℕ} {z hx o8 dk lo m hi : ℕ}
    (h : scanK R8 R z hx o8 dk lo m hi = true) (hm : m ≤ 64 * hi) :
    ∀ t, lo ≤ t → t < lo + m → scanF R8 R z hx o8 dk t = true := by
  intro t h1 h2
  have := CFSG.KC.G2Three.allBelow_g2 h hm (t - lo) (by omega)
  rwa [(by simp only [Nat.add_eq]; omega : Nat.add lo (t - lo) = t)] at this

theorem scan_orbit {O : Array (List ℕ)} {R8 R : ℕ → ℕ} {z hx o8 dk n o0 o1 o2 : ℕ}
    (hz : canon6 a2Z7 = true ∧ pk a2Z7 = z) (hO : O.size = n)
    (hr : ∀ t < n, canon6 (O.getD t []) = true ∧ pk (O.getD t []) = recX R8 o8 t)
    (hX0 : (a2XTab 0).size = 168 ∧ ∀ t < 168, canon6 ((a2XTab 0).getD t []) = true ∧
      pk ((a2XTab 0).getD t []) = recX R o0 t)
    (hX1 : (a2XTab 1).size = 168 ∧ ∀ t < 168, canon6 ((a2XTab 1).getD t []) = true ∧
      pk ((a2XTab 1).getD t []) = recX R o1 t)
    (hX2 : (a2XTab 2).size = 168 ∧ ∀ t < 168, canon6 ((a2XTab 2).getD t []) = true ∧
      pk ((a2XTab 2).getD t []) = recX R o2 t)
    (ho : R hx = o0 ∧ R (hx + 1) = o1 ∧ R (hx + 2) = o2)
    (h : ∀ t < n, scanF R8 R z hx o8 dk t = true) :
    allCheck (scanOne (indexMap (a2XTab 0)) (indexMap (a2XTab 1)) (indexMap (a2XTab 2))) O =
      true :=
  CFSG.KC.G2Three.allCheck_of fun t ht =>
    scanOne_of hz (hr t (hO ▸ ht)) hX0 hX1 hX2 ho (h t (hO ▸ ht))

theorem inK_sound {R : ℕ → ℕ} {o n X : ℕ} (h : inK R o n X = true) :
    ∃ p < n, recX R o p = X := by
  unfold inK at h
  rw [strictB_eq] at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨_, h.1, h.2⟩

theorem found_of_inK {O : Array (List ℕ)} {R : ℕ → ℕ} {o n U : ℕ} {u : List ℕ}
    (hO : O.size = n)
    (hr : ∀ t < n, canon6 (O.getD t []) = true ∧ pk (O.getD t []) = recX R o t)
    (hu : canon6 u = true ∧ pk u = U) (h : inK R o n U = true) :
    found O (indexMap O) u = true := by
  obtain ⟨p, hp, he⟩ := inK_sound h
  obtain ⟨c, q⟩ := hr p hp
  exact CFSG.KC.G2Three.found_indexMap.2
    ⟨p, by rw [hO]; exact hp, pk_inj c hu.1 (by rw [q, he, hu.2])⟩

theorem nIf_eq' (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem sumBelow_eq_sum (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    CFSG.KC.Loop.sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have hgen : ∀ h, CFSG.KC.Loop.sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + CFSG.KC.Loop.sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, (rfl : (2 : ℕ) ^ 6 = 64)]
        omega
      simp only [e, nIf_eq', Nat.blt_eq]
  rw [hgen hi, (by omega : 64 * hi = m + (64 * hi - m)), Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem countP_range (p : List ℕ → Bool) (es : Array (List ℕ)) :
    LSideData.countP p es =
      ∑ t ∈ Finset.range es.size, if p (es.getD t []) = true then 1 else 0 := by
  unfold LSideData.countP
  rw [Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun t => if p (es.getD t []) = true then 1 else 0) es.size

theorem countP_comm {E : Array (List ℕ)} {R : ℕ → ℕ} {o n hi A : ℕ} {a : List ℕ}
    (hE : E.size = n)
    (hr : ∀ t < n, canon6 (E.getD t []) = true ∧ pk (E.getD t []) = recX R o t)
    (ha : canon6 a = true ∧ pk a = A) (hm : n ≤ 64 * hi) :
    LSideData.countP (fun y => commutes6 y a) E = cntK R o n A hi := by
  rw [countP_range, hE, cntK, sumBelow_eq_sum n hi _ hm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hx := hr t (Finset.mem_range.1 ht)
  have e : commutes6 (E.getD t []) a = commF (recX R o t) A := by
    unfold commutes6 commF
    rw [beq_pk (mulE hx ha).1 (mulE ha hx).1, (mulE hx ha).2, (mulE ha hx).2]
  rw [nIf_eq', e]

theorem dRows_at {R8 R : ℕ → ℕ} {vb oK oD lo m : ℕ} (h : dRows R8 R vb oK oD lo m = true)
    (hm : m ≤ 64) :
    ∀ i < m, ∀ j < 36, dF R8 R vb oK (recX R oD (Nat.add lo i)) (recX R oD j) = true := by
  intro i hi j hj
  have h1 := CFSG.KC.G2Three.allBelow_g2 h (by omega) i hi
  rw [strictB_eq] at h1
  have h2 := CFSG.KC.G2Three.allBelow_g2 h1 (by omega) j hj
  rw [strictB_eq] at h2
  exact h2

end CFSG.KC.Sp6A2

end
