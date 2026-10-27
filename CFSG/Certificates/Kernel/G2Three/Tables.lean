module

public import Certificates.Data.Kernel.G2Three.Defs
public import CFSG.Certificates.Kernel.G2Three.BfsReplay
public import CFSG.Certificates.Kernel.G2Three.BuildPack
public import CFSG.Certificates.Kernel.G2Three.IndexMap
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData

public section

namespace CFSG.KC.G2Three

open CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KC.Loop CFSG.RankThree.PartTwo.Census.Carrier.G2Three
  CFSG.Quasithin.G2U CFSG.KD.G2Three

theorem bAnd_g2 {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem recAnd_g2 (f : Nat → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (f i)) n = true →
    ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := bAnd_g2 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · exact recAnd_g2 f n h2 i hlt
    · exact h1

theorem allBelow_g2 {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := recAnd_g2 (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) hi h
    (i / 64) (by omega)
  have h2 := recAnd_g2 (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, (rfl : (2 : Nat) ^ 6 = 64)]
    omega
  have hb : Nat.blt i m = true := Nat.blt_eq.mpr him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem getD_irrel {α : Type} {E : Array α} {t : ℕ} (ht : t < E.size) (d d' : α) :
    E.getD t d = E.getD t d' := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht]
  rfl

theorem listGetD_irrel {α : Type} {l : List α} {s : ℕ} (hs : s < l.length) (d d' : α) :
    l.getD s d = l.getD s d' := by
  rw [List.getD_eq_getElem _ _ hs, List.getD_eq_getElem _ _ hs]

theorem all_of_getD {α : Type} {l : List α} {p : α → Bool} (d : α)
    (h : ∀ s < l.length, p (l.getD s d) = true) : l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
  have := h s hs
  rwa [List.getD_eq_getElem _ _ hs] at this

theorem flat_facts {n k h s : ℕ} (hk : 0 < k) (hh : h < n) (hs : s < k) :
    h * k + s < n * k ∧ (h * k + s) / k = h ∧ (h * k + s) % k = s := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (h + 1) * k ≤ n * k := Nat.mul_le_mul_right _ hh
    rw [Nat.succ_mul] at h1
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hs _) h1
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hs, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

variable (hc : consts3OK 14 5 196 LO RM CI ONE UP = true)

include hc in
theorem mulE {a b : List ℕ} {A B : ℕ} (ha : canon14 a = true ∧ pk a = A)
    (hb : canon14 b = true ∧ pk b = B) : canon14 (mul14 a b) = true ∧ pk (mul14 a b) = MUL A B :=
  ⟨canon14_mul14 _ _, by rw [pk_mul14 hc ha.1 hb.1, ha.2, hb.2]; rfl⟩

theorem bindE {c : List ℕ} {A V : ℕ} (h : canon14 c = true ∧ pk c = A) (e : Nat.beq A V = true) :
    canon14 c = true ∧ pk c = V :=
  ⟨h.1, h.2.trans (Nat.eq_of_beq_eq_true e)⟩

theorem take_drop_pair {a b : List ℕ} {A B : ℕ} (ha : canon14 a = true ∧ pk a = A)
    (hb : canon14 b = true ∧ pk b = B) :
    (canon14 ((a ++ b).take 196) = true ∧ pk ((a ++ b).take 196) = A) ∧
      (canon14 ((a ++ b).drop 196) = true ∧ pk ((a ++ b).drop 196) = B) := by
  have hl : a.length = 196 := (canon14_iff.1 ha.1).1
  rw [List.take_left' hl, List.drop_left' hl]
  exact ⟨ha, hb⟩

theorem beq_pk {a b : List ℕ} (ha : canon14 a = true) (hb : canon14 b = true) :
    (a == b) = Nat.beq (pk a) (pk b) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]
  exact ⟨fun h => h ▸ rfl, pk_inj ha hb⟩

include hc in
theorem pk_pow64 {m : List ℕ} (hm : canon14 m = true) :
    canon14 (pow64 m) = true ∧ pk (pow64 m) = SQ6 (pk m) := by
  have s1 := mulE hc ⟨hm, rfl⟩ ⟨hm, rfl⟩
  have s2 := mulE hc s1 s1
  have s3 := mulE hc s2 s2
  have s4 := mulE hc s3 s3
  have s5 := mulE hc s4 s4
  have s6 := mulE hc s5 s5
  refine ⟨s6.1, ?_⟩
  unfold SQ6
  simp only [strictN_eq3]
  exact s6.2

theorem build_at {X G PA PB : ℕ → ℕ} {n k hi : ℕ} (h : buildK X G PA PB n k hi = true)
    (hm : n - 1 ≤ 64 * hi) :
    ∀ i < n - 1, PA i ≤ i ∧ PB i < k ∧ X (i + 1) = MUL (X (PA i)) (G (PB i)) := by
  intro i hi'
  have := allBelow_g2 h hm i hi'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  exact ⟨h1, h2, h3⟩

theorem orb_at {X GA GB OA OB : ℕ → ℕ} {n k hi : ℕ} (h : orbK X GA GB OA OB n k hi = true)
    (hm : n - 1 ≤ 64 * hi) :
    ∀ i < n - 1, OA i ≤ i ∧ OB i < k ∧
      X (i + 1) = MUL (MUL (GA (OB i)) (X (OA i))) (GB (OB i)) := by
  intro i hi'
  have := allBelow_g2 h hm i hi'
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  exact ⟨h1, h2, h3⟩

theorem step_facts {X G PA PB C POS : ℕ → ℕ} {n k hi : ℕ}
    (h : stepK X G PA PB C POS n k hi = true) (hm : n * k ≤ 64 * hi) :
    C 0 = 1 ∧ C (n * k) = n ∧ ∀ i < n * k, i / k < C i ∧ POS i ≤ C i ∧ POS i < n ∧
      X (POS i) = MUL (X (i / k)) (G (i % k)) ∧
      (POS i = C i → C (i + 1) = C i + 1 ∧ PA (C i - 1) = i / k ∧ PB (C i - 1) = i % k) ∧
      (POS i ≠ C i → C (i + 1) = C i) := by
  unfold stepK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  refine ⟨h0, h1, fun i hi => ?_⟩
  have e := allBelow_g2 h2 hm i hi
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

theorem sort_inj {X SRT SRI : ℕ → ℕ} {n hi : ℕ} (h : sortK X SRT SRI n hi = true)
    (hm : n ≤ 64 * hi) : ∀ t < n, ∀ t' < n, X t = X t' → t = t' := by
  have hall := allBelow_g2 h hm
  refine inj_of_sorted (SRT := SRT) (SRI := SRI) (fun i hi' => ?_) (fun i hi1 => ?_)
  · have e := hall i hi'
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at e
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, -⟩ := e
    exact ⟨a, b, c, d⟩
  · have e := hall i (by omega)
    simp only [Bool.and_eq_true] at e
    have e2 := e.2
    have hb : Nat.blt (Nat.succ i) n = true := Nat.blt_eq.mpr hi1
    rw [hb, cond_true] at e2
    exact Nat.blt_eq.mp e2

include hc in
theorem table_ok {gens : List (List ℕ)} {n hiB hiS hiT : ℕ} {X G PA PB C POS SRT SRI : ℕ → ℕ}
    (hn : 0 < n) (hk : 0 < gens.length)
    (hg : ∀ s < gens.length, canon14 (gens.getD s one14) = true ∧ pk (gens.getD s one14) = G s)
    (h0 : X 0 = pk one14)
    (hB : buildK X G PA PB n gens.length hiB = true) (hBm : n - 1 ≤ 64 * hiB)
    (hS : stepK X G PA PB C POS n gens.length hiS = true) (hSm : n * gens.length ≤ 64 * hiS)
    (hT : sortK X SRT SRI n hiT = true) (hTm : n ≤ 64 * hiT) :
    (build one14 mul14 gens (bfsParents one14 mul14 gens n)).size = n ∧
    closedCheck mul14 gens (build one14 mul14 gens (bfsParents one14 mul14 gens n)) = true ∧
    distinctCheck (build one14 mul14 gens (bfsParents one14 mul14 gens n)) = true ∧
    allCheck canon14 (build one14 mul14 gens (bfsParents one14 mul14 gens n)) = true ∧
    ∀ t < n, canon14 ((build one14 mul14 gens (bfsParents one14 mul14 gens n)).getD t []) = true ∧
      pk ((build one14 mul14 gens (bfsParents one14 mul14 gens n)).getD t []) = X t := by
  have hBi := build_at hB hBm
  obtain ⟨hC0, hCn, hSi⟩ := step_facts hS hSm
  have hX := sort_inj hT hTm
  have hgm : ∀ g ∈ gens, canon14 g = true := by
    intro g hg'
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg'
    have := (hg s hs).1
    rwa [List.getD_eq_getElem _ _ hs] at this
  let PL : List (ℕ × ℕ) := (List.range (n - 1)).map fun i => (PA i, PB i)
  have hPLlen : PL.length = n - 1 := by simp [PL]
  have hPLget : ∀ i < n - 1, PL.getD i (0, 0) = (PA i, PB i) := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by rw [hPLlen]; exact hi)]
    simp [PL]
  obtain ⟨hsz, hrec⟩ := build_pk hc hgm (fun s hs => (hg s hs).2) h0 (par := PL)
    (fun i hi => by
      rw [hPLlen] at hi
      rw [hPLget i hi]
      exact hBi i hi)
  have hEsz : (build one14 mul14 gens PL).size = n := by rw [hsz, hPLlen]; omega
  have hrec' : ∀ t < n, canon14 ((build one14 mul14 gens PL).getD t []) = true ∧
      pk ((build one14 mul14 gens PL).getD t []) = X t := by
    intro t ht
    rw [getD_irrel (by rw [hEsz]; exact ht) [] one14]
    exact hrec t (by rw [hPLlen]; omega)
  have hd : ∀ t < (build one14 mul14 gens PL).size, ∀ t' < (build one14 mul14 gens PL).size,
      (build one14 mul14 gens PL).getD t [] = (build one14 mul14 gens PL).getD t' [] → t = t' := by
    intro t ht t' ht' he
    rw [hEsz] at ht ht'
    exact hX t ht t' ht' (by rw [← (hrec' t ht).2, ← (hrec' t' ht').2, he])
  have hprod : ∀ h < n, ∀ s < gens.length,
      (build one14 mul14 gens PL).getD (POS (h * gens.length + s)) [] =
        mul14 ((build one14 mul14 gens PL).getD h []) (gens.getD s []) := by
    intro h hh s hs
    obtain ⟨hi, hdiv, hmod⟩ := flat_facts hk hh hs
    obtain ⟨-, -, hp, hx, -, -⟩ := hSi _ hi
    rw [hdiv, hmod] at hx
    obtain ⟨cg, pg⟩ := hg s hs
    obtain ⟨ch, ph⟩ := hrec' h hh
    obtain ⟨cp, pp⟩ := hrec' _ hp
    rw [listGetD_irrel hs [] one14]
    refine pk_inj cp (canon14_mul14 _ _) ?_
    rw [pp, hx, pk_mul14 hc ch cg, ph, pg]
    rfl
  have hstep : ∀ h < n, ∀ s < gens.length,
      StepOK mul14 gens (build one14 mul14 gens PL) PL.toArray C POS h s (h * gens.length + s) := by
    intro h hh s hs
    obtain ⟨hi, hdiv, hmod⟩ := flat_facts hk hh hs
    obtain ⟨a, b, c, -, e, f⟩ := hSi _ hi
    rw [hdiv] at a
    unfold StepOK
    refine ⟨fun _ => ⟨b, by rw [hEsz]; exact c, hprod h hh s hs, fun hpc => ?_,
      fun hlt => f (Nat.ne_of_lt hlt)⟩, fun hn' => absurd a hn'⟩
    obtain ⟨e1, e2, e3⟩ := e hpc
    rw [hdiv] at e2
    rw [hmod] at e3
    refine ⟨e1, ?_⟩
    have hlt : C (h * gens.length + s) - 1 < n - 1 := by omega
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
      hPLget _ hlt, e2, e3]
  have hPs : PL.toArray.size + 1 = (build one14 mul14 gens PL).size := by
    rw [List.size_toArray, hPLlen, hEsz]
    omega
  have hpar : bfsParents one14 mul14 gens n = PL := by
    have := bfsParents_replay (build_getD_zero one14 mul14 gens PL) (by omega) hd hPs hC0 hstep
      (by rw [hCn, hEsz])
    simpa using this
  rw [hpar]
  refine ⟨hEsz, closedCheck_of fun v hv g hg' => ?_, distinctCheck_of hd,
    allCheck_of fun t ht => (hrec' t (by rw [← hEsz]; exact ht)).1, hrec'⟩
  obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hg'
  rw [hEsz] at hv
  refine ⟨POS (v * gens.length + s), ?_, ?_⟩
  · rw [hEsz]
    exact (hSi _ (flat_facts hk hv hs).1).2.2.1
  · rw [hprod v hv s hs, List.getD_eq_getElem _ _ hs]

include hc in
theorem orbit_ok {t0 : List ℕ} (ht0 : canon14 t0 = true) {gps : List (List ℕ)}
    {GA GB X OA OB SRT SRI : ℕ → ℕ} {n hiO hiT : ℕ} (hn : 0 < n)
    (hg : ∀ s < gps.length, (canon14 ((gps.getD s (one14 ++ one14)).take 196) = true ∧
        pk ((gps.getD s (one14 ++ one14)).take 196) = GA s) ∧
      (canon14 ((gps.getD s (one14 ++ one14)).drop 196) = true ∧
        pk ((gps.getD s (one14 ++ one14)).drop 196) = GB s))
    (h0 : X 0 = pk t0) {par : List (ℕ × ℕ)} (hlen : par.length = n - 1)
    (hget : ∀ i < n - 1, par.getD i (0, 0) = (OA i, OB i))
    (hO : orbK X GA GB OA OB n gps.length hiO = true) (hOm : n - 1 ≤ 64 * hiO)
    (hT : sortK X SRT SRI n hiT = true) (hTm : n ≤ 64 * hiT) :
    (orbitBuild t0 gps par).size = n ∧ distinctCheck (orbitBuild t0 gps par) = true ∧
      allCheck canon14 (orbitBuild t0 gps par) = true ∧
      ∀ t < n, canon14 ((orbitBuild t0 gps par).getD t []) = true ∧
        pk ((orbitBuild t0 gps par).getD t []) = X t := by
  have hOi := orb_at hO hOm
  have hX := sort_inj hT hTm
  obtain ⟨hsz, hrec⟩ := orbitBuild_pk hc ht0 (fun s hs => ⟨(hg s hs).1.1, (hg s hs).2.1⟩)
    (fun s hs => ⟨(hg s hs).1.2, (hg s hs).2.2⟩) h0
    (fun i hi => by
      rw [hlen] at hi
      rw [hget i hi]
      exact hOi i hi)
  have hEsz : (orbitBuild t0 gps par).size = n := by rw [hsz, hlen]; omega
  have hrec' : ∀ t < n, canon14 ((orbitBuild t0 gps par).getD t []) = true ∧
      pk ((orbitBuild t0 gps par).getD t []) = X t := by
    intro t ht
    rw [getD_irrel (by rw [hEsz]; exact ht) [] t0]
    exact hrec t (by rw [hlen]; omega)
  refine ⟨hEsz, distinctCheck_of fun t ht t' ht' he => ?_,
    allCheck_of fun t ht => (hrec' t (by rw [← hEsz]; exact ht)).1, hrec'⟩
  rw [hEsz] at ht ht'
  exact hX t ht t' ht' (by rw [← (hrec' t ht).2, ← (hrec' t' ht').2, he])

include hc in
theorem invTest_of {S O : Array (List ℕ)} {XS XO IDX : ℕ → ℕ} {nS nO hi : ℕ}
    (hS : S.size = nS) (hSr : ∀ t < nS, canon14 (S.getD t []) = true ∧ pk (S.getD t []) = XS t)
    (hO : O.size = nO) (hOr : ∀ t < nO, canon14 (O.getD t []) = true ∧ pk (O.getD t []) = XO t)
    (hone : pk one14 = ONE) (h : invK XS XO IDX nS nO hi = true) (hm : nS ≤ 64 * hi) :
    allCheck (fun x => !(mul14 x x == one14) || x == one14 || found O (indexMap O) x) S = true := by
  refine allCheck_of fun t ht => ?_
  rw [hS] at ht
  obtain ⟨cx, px⟩ := hSr t ht
  have hb := allBelow_g2 h hm t ht
  have e1 : (mul14 (S.getD t []) (S.getD t []) == one14) = Nat.beq (MUL (XS t) (XS t)) ONE := by
    rw [beq_pk (canon14_mul14 _ _) canon14_one14, pk_mul14 hc cx cx, px, hone]
    rfl
  have e2 : (S.getD t [] == one14) = Nat.beq (XS t) ONE := by
    rw [beq_pk cx canon14_one14, px, hone]
  rw [e1, e2]
  cases hq : Nat.beq (MUL (XS t) (XS t)) ONE
  · rfl
  · rw [hq, cond_true] at hb
    cases hq2 : Nat.beq (XS t) ONE
    · rw [hq2, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hb
      obtain ⟨hlt, heq⟩ := hb
      obtain ⟨co, po⟩ := hOr _ hlt
      have hf : found O (indexMap O) (S.getD t []) = true :=
        found_indexMap.2 ⟨IDX t, by rw [hO]; exact hlt, pk_inj co cx (by rw [po, px, heq])⟩
      rw [hf]
      rfl
    · rfl

include hc in
theorem centTest_of {E : Array (List ℕ)} {X : ℕ → ℕ} {n hi A U T : ℕ} {a u t1 : List ℕ}
    (ha : canon14 a = true ∧ pk a = A) (hu : canon14 u = true ∧ pk u = U)
    (ht1 : canon14 t1 = true ∧ pk t1 = T) (hE : E.size = n)
    (hr : ∀ t < n, canon14 (E.getD t []) = true ∧ pk (E.getD t []) = X t)
    (hone : pk one14 = ONE) (h : centK X A U T n hi = true) (hm : n ≤ 64 * hi) :
    allCheck (fun x => !(commutes x a && commutes x u && pow64 x == one14) || x == one14 ||
      x == t1) E = true := by
  refine allCheck_of fun t ht => ?_
  rw [hE] at ht
  obtain ⟨cx, px⟩ := hr t ht
  have hb := allBelow_g2 h hm t ht
  have ec : ∀ {b : List ℕ} {B : ℕ}, canon14 b = true ∧ pk b = B →
      commutes (E.getD t []) b = Nat.beq (MUL (X t) B) (MUL B (X t)) := by
    intro b B hbB
    unfold commutes
    rw [beq_pk (canon14_mul14 _ _) (canon14_mul14 _ _), pk_mul14 hc cx hbB.1,
      pk_mul14 hc hbB.1 cx, px, hbB.2]
    rfl
  have ep : (pow64 (E.getD t []) == one14) = Nat.beq (SQ6 (X t)) ONE := by
    obtain ⟨c6, p6⟩ := pk_pow64 hc cx
    rw [beq_pk c6 canon14_one14, p6, px, hone]
  have e1 : (E.getD t [] == one14) = Nat.beq (X t) ONE := by
    rw [beq_pk cx canon14_one14, px, hone]
  have e2 : (E.getD t [] == t1) = Nat.beq (X t) T := by
    rw [beq_pk cx ht1.1, px, ht1.2]
  rw [ec ha, ec hu, ep, e1, e2]
  cases hq : (Nat.beq (MUL (X t) A) (MUL A (X t)) && Nat.beq (MUL (X t) U) (MUL U (X t)) &&
      Nat.beq (SQ6 (X t)) ONE)
  · rfl
  · rw [hq, cond_true] at hb
    simpa using hb

end CFSG.KC.G2Three

end
