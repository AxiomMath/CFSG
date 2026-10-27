module

public import CFSG.Certificates.Kernel.J4.KShape.Shape
public import CFSG.Certificates.Kernel.J4.WordsSound
public import CFSG.Certificates.Kernel.J4.NClosure
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.J4KShape

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.KShape CFSG.Certificates.KB.Sound CFSG.Certificates.DceLoop
  CFSG.Certificates.DceWord CFSG.Certificates.J4Words CFSG.Certificates.J4NClosure Subgroup

variable {G : Type*} [Group G]

theorem recAnd_spec (g : ℕ → Bool) : ∀ m, Nat.rec (motive := fun _ => Bool) true
    (fun l ih => andB (g l) ih) m = true → ∀ l < m, g l = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | m + 1, h, l, hl => by
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
    · exact recAnd_spec g m h2 l hl
    · exact h1

theorem rngAll_spec {a b : ℕ} {f : ℕ → Bool} : ∀ hi, rngAll a b hi f = true →
    ∀ i, a ≤ i → i < b → i < a + 64 * hi → f i = true
  | 0, _, i, h1, _, h3 => by omega
  | hi + 1, h, i, h1, h2, h3 => by
    obtain ⟨hin, hrest⟩ := andB_iff.1 h
    by_cases hlt : i < a + 64 * hi
    · exact rngAll_spec hi hrest i h1 h2 hlt
    · have hl := recAnd_spec (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
        (Nat.blt i b)) (Nat.add a (Nat.add (Nat.shiftLeft hi 6) l))) 64 hin (i - a - 64 * hi)
        (by omega)
      have e : Nat.add a (Nat.add (Nat.shiftLeft hi 6) (i - a - 64 * hi)) = i := by
        change a + (hi <<< 6 + (i - a - 64 * hi)) = i
        rw [Nat.shiftLeft_eq]
        omega
      simp only [e] at hl
      have hb : Nat.blt i b = true := Nat.blt_eq.mpr h2
      rw [hb] at hl
      exact hl

theorem wFits_spec {w n : ℕ} (h : wFits w n = true) : w < 256 ^ n := by
  have := Nat.blt_eq.mp h
  change w < 1 <<< (8 * n) at this
  rwa [Nat.shiftLeft_eq, one_mul, two_pow_eight_mul] at this

theorem letsBelow_spec {w m : ℕ} : ∀ n, letsBelow w n m = true → ∀ q < n, wLet w q < m
  | 0, _, q, hq => absurd hq (Nat.not_lt_zero q)
  | n + 1, h, q, hq => by
    obtain ⟨h1, h2⟩ := andB_iff.1 h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with hq | rfl
    · exact letsBelow_spec n h1 q hq
    · exact Nat.blt_eq.mp h2

@[expose] noncomputable def rv (f : ℕ → G) (A : ℕ) : G := wv (lvE f) (wW A) (wN A)

@[expose] def RecOK (A : ℕ) : Prop := wW A < 256 ^ wN A ∧ ∀ d ∈ bytes (wW A) (wN A), d < 255

theorem rec_fields {w n : ℕ} (hn : n < 65536) :
    wN (Nat.lor n (Nat.shiftLeft w 32)) = n ∧ wW (Nat.lor n (Nat.shiftLeft w 32)) = w := by
  have hn' : n < 2 ^ 32 := by omega
  have e : Nat.lor n (Nat.shiftLeft w 32) = w * 2 ^ 32 + n := by
    change n ||| w <<< 32 = _
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hn', Nat.shiftLeft_eq]
  constructor
  · change Nat.lor n (Nat.shiftLeft w 32) &&& (2 ^ 16 - 1) = n
    rw [Nat.and_two_pow_sub_one_eq_mod, e]
    omega
  · change Nat.lor n (Nat.shiftLeft w 32) >>> 32 = w
    rw [Nat.shiftRight_eq_div_pow, e]
    omega

theorem wLet_mem {w n q : ℕ} (hq : q < n) : wLet w q ∈ bytes w n := by
  rw [mem_bytes]
  exact ⟨q, hq, by rw [J4Words.wLet_eq, DceWord.wLet_eq]⟩

theorem rcat_spec (f : ℕ → G) {A B : ℕ} (hA : RecOK A) (hB : RecOK B)
    (hl : wN A + wN B < 65536) :
    wN (rcat A B) = wN A + wN B ∧ RecOK (rcat A B) ∧ rv f (rcat A B) = rv f A * rv f B := by
  obtain ⟨e1, e2⟩ := rec_fields (w := wCat (wW A) (wN A) (wW B)) hl
  have e1' : wN (rcat A B) = wN A + wN B := e1
  have e2' : wW (rcat A B) = wCat (wW A) (wN A) (wW B) := e2
  refine ⟨e1', ⟨?_, ?_⟩, ?_⟩
  · rw [e1', e2']
    exact wCat_lt hA.1 hB.1
  · rw [e1', e2', bytes_wCat hA.1 hB.1]
    intro d hd
    rcases List.mem_append.1 hd with h | h
    · exact hA.2 d h
    · exact hB.2 d h
  · unfold rv
    rw [e1', e2', J4Words.wv_wCat _ hA.1 hB.1]

theorem rinv_spec (f : ℕ → G) {INV A : ℕ}
    (hI : ∀ c < 255, lInv INV c < 255 ∧ f (lInv INV c) = (f c)⁻¹) (hA : RecOK A) :
    wN (rinv INV A) = wN A ∧ RecOK (rinv INV A) ∧ rv f (rinv INV A) = (rv f A)⁻¹ := by
  have hA16 : wN A < 65536 := by
    change A &&& 65535 < 65536
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
  obtain ⟨e1, e2⟩ := rec_fields (w := wInv INV (wW A) (wN A)) hA16
  have e1' : wN (rinv INV A) = wN A := e1
  have e2' : wW (rinv INV A) = wInv INV (wW A) (wN A) := e2
  refine ⟨e1', ⟨?_, ?_⟩, ?_⟩
  · rw [e1', e2']
    exact J4Words.wInv_lt _ _ _
  · rw [e1', e2', bytes_wInv]
    intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
    exact (hI c (hA.2 c (List.mem_reverse.1 hc))).1
  · unfold rv
    rw [e1', e2']
    refine J4Words.wv_wInv _ _ _ _ fun q hq => ?_
    have hc := hA.2 _ (wLet_mem hq)
    have hc' := (hI _ hc).1
    simp only [lvE, Nat.ne_of_lt hc, Nat.ne_of_lt hc', ↓reduceIte]
    exact (hI _ hc).2

theorem lit_spec (f : ℕ → G) {c : ℕ} (hc : c < 255) :
    wN (lit c) = 1 ∧ RecOK (lit c) ∧ rv f (lit c) = f c := by
  obtain ⟨e1, e2⟩ := rec_fields (w := c) (n := 1) (by norm_num)
  have e1' : wN (lit c) = 1 := e1
  have e2' : wW (lit c) = c := e2
  have hb : bytes c 1 = [c] := by
    simp [bytes, byte_eq', Nat.mod_eq_of_lt (by omega : c < 256)]
  refine ⟨e1', ⟨?_, ?_⟩, ?_⟩
  · rw [e1', e2']
    omega
  · rw [e1', e2', hb]
    simpa using hc
  · unfold rv
    rw [e1', e2', wv_one _ (by omega)]
    simp [lvE, Nat.ne_of_lt hc]

theorem same_val (f : ℕ → G) {INV R E : ℕ} (hI : ∀ c < 255, f (lInv INV c) = (f c)⁻¹)
    (h : same INV R E = true) : rv f E = rv f R := by
  obtain ⟨-, h2⟩ := andB_iff.1 h
  exact freeRed_val' f hI (Nat.eq_of_beq_eq_true h2)

theorem wrec_ok {WT : ℕ} (hw : wordsOK WT = true) :
    wrec WT 0 = 0 ∧ ∀ i < 11, RecOK (wrec WT i) ∧ ∀ q < wN (wrec WT i), wLet (wW (wrec WT i)) q < 4 := by
  obtain ⟨h0, hall⟩ := andB_iff.1 hw
  refine ⟨Nat.eq_of_beq_eq_true h0, fun i hi => ?_⟩
  obtain ⟨hf, hb⟩ := andB_iff.1 (rngAll_spec 1 hall i (Nat.zero_le i) hi (by omega))
  have hlet := letsBelow_spec _ hb
  refine ⟨⟨wFits_spec hf, fun d hd => ?_⟩, hlet⟩
  obtain ⟨q, hq, rfl⟩ := mem_bytes.1 hd
  have h4 : wLet (wW (wrec WT i)) q < 4 := hlet q hq
  rw [J4Words.wLet_eq, DceWord.wLet_eq] at h4
  omega

@[expose] noncomputable def wi (f : ℕ → G) (WT : ℕ) (i : Fin 11) : G := rv f (wrec WT i)

@[expose] noncomputable def zi (f : ℕ → G) (WT : ℕ) (i : Fin 11) : G :=
  (wi f WT i)⁻¹ * f 5 * wi f WT i

@[expose] noncomputable def Vz (f : ℕ → G) (WT : ℕ) : Subgroup G := closure (Set.range (zi f WT))

@[expose] noncomputable def pStep (INV WT c k acc : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) acc (rcat acc (zr INV WT (Nat.sub (nat_lit 10) k) (nat_lit 5)))
    (Nat.blt (nat_lit 0) (Nat.land c (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 10) k))))

@[expose] noncomputable def pLoop (INV WT c n acc : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc) (fun k ih acc => ih (pStep INV WT c k acc))
    n acc

theorem pLoop_succ (INV WT c n acc : ℕ) :
    pLoop INV WT c (n + 1) acc = pLoop INV WT c n (pStep INV WT c n acc) := rfl

theorem prodW_eq (INV WT c : ℕ) : prodW INV WT c = pLoop INV WT c 11 0 := rfl

section Shape

variable (f : ℕ → G) {RZT : ℕ → ℕ} {INV WT C : ℕ}
  (hI : ∀ c < 255, lInv INV c < 255 ∧ f (lInv INV c) = (f c)⁻¹)
  (h6 : f 6 = (f 5)⁻¹) (hL : ∀ i < 11, wN (wrec WT i) < 1000) (hw : wordsOK WT = true)
include hI hL hw

theorem zr_spec {i e : ℕ} (hi : i < 11) (he : e < 255) :
    wN (zr INV WT i e) = 2 * wN (wrec WT i) + 1 ∧ RecOK (zr INV WT i e) ∧
      rv f (zr INV WT i e) = (rv f (wrec WT i))⁻¹ * f e * rv f (wrec WT i) := by
  obtain ⟨hW, -⟩ := (wrec_ok hw).2 i hi
  have hLi := hL i hi
  obtain ⟨a1, a2, a3⟩ := rinv_spec f hI hW
  obtain ⟨b1, b2, b3⟩ := lit_spec f he
  obtain ⟨c1, c2, c3⟩ := rcat_spec f a2 b2 (by omega)
  obtain ⟨d1, d2, d3⟩ := rcat_spec f c2 hW (by omega)
  refine ⟨by unfold zr; omega, d2, ?_⟩
  unfold zr
  rw [d3, c3, a3, b3]

theorem zr5_val {i : ℕ} (hi : i < 11) : rv f (zr INV WT i 5) = zi f WT ⟨i, hi⟩ :=
  (zr_spec f hI hL hw hi (by norm_num)).2.2

include h6 in
theorem zr6_val {i : ℕ} (hi : i < 11) : rv f (zr INV WT i 6) = (zi f WT ⟨i, hi⟩)⁻¹ := by
  rw [(zr_spec f hI hL hw hi (by norm_num)).2.2, h6]
  unfold zi wi
  group

theorem zr_len {i e : ℕ} (hi : i < 11) (he : e < 255) : wN (zr INV WT i e) ≤ 1999 := by
  rw [(zr_spec f hI hL hw hi he).1]
  have := hL i hi
  omega

theorem pStep_spec (c k : ℕ) {acc : ℕ} (h1 : RecOK acc) (h2 : rv f acc ∈ Vz f WT)
    (h3 : wN acc + 1999 < 65536) :
    RecOK (pStep INV WT c k acc) ∧ rv f (pStep INV WT c k acc) ∈ Vz f WT ∧
      wN (pStep INV WT c k acc) ≤ wN acc + 1999 := by
  have hk : 10 - k < 11 := by omega
  unfold pStep
  cases Nat.blt (nat_lit 0) (Nat.land c (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 10) k)))
  · exact ⟨h1, h2, Nat.le_add_right _ _⟩
  · obtain ⟨-, hZ, -⟩ := zr_spec f hI hL hw hk (e := 5) (by norm_num)
    have hZl := zr_len f hI hL hw hk (e := 5) (by norm_num)
    obtain ⟨r1, r2, r3⟩ := rcat_spec f h1 hZ (by omega)
    have hm : rv f (rcat acc (zr INV WT (10 - k) 5)) ∈ Vz f WT := by
      rw [r3, zr5_val f hI hL hw hk]
      exact mul_mem h2 (subset_closure ⟨_, rfl⟩)
    exact ⟨r2, hm, r1.trans_le (Nat.add_le_add_left hZl _)⟩

theorem prodW_spec (c : ℕ) :
    RecOK (prodW INV WT c) ∧ rv f (prodW INV WT c) ∈ Vz f WT ∧ wN (prodW INV WT c) ≤ 11 * 1999 := by
  have key : ∀ n acc, RecOK acc → rv f acc ∈ Vz f WT → wN acc + n * 1999 < 65536 →
      RecOK (pLoop INV WT c n acc) ∧ rv f (pLoop INV WT c n acc) ∈ Vz f WT ∧
      wN (pLoop INV WT c n acc) ≤ wN acc + n * 1999 := by
    intro n
    induction n with
    | zero => exact fun acc h1 h2 _ => ⟨h1, h2, Nat.le_add_right _ _⟩
    | succ n ih =>
      intro acc h1 h2 h3
      obtain ⟨s1, s2, s3⟩ := pStep_spec f hI hL hw c n h1 h2 (by omega)
      obtain ⟨t1, t2, t3⟩ := ih _ s1 s2 (by omega)
      rw [pLoop_succ]
      exact ⟨t1, t2, by omega⟩
  have hw0 : wW 0 = 0 := rfl
  have hn0 : wN 0 = 0 := rfl
  have h0 : RecOK 0 := ⟨by rw [hw0, hn0]; norm_num, by rw [hw0, hn0]; simp [bytes]⟩
  have hv0 : rv f 0 ∈ Vz f WT := by
    have : rv f 0 = 1 := by
      unfold rv
      rw [hw0, hn0]
      simp [wv]
    rw [this]
    exact one_mem _
  obtain ⟨k1, k2, k3⟩ := key 11 0 h0 hv0 (by rw [hn0]; norm_num)
  rw [prodW_eq]
  exact ⟨k1, k2, by rw [hn0] at k3; omega⟩

end Shape

theorem pairIdx_lt {i j : ℕ} (hij : i < j) (hj : j < 11) : pairIdx i j < 88 := by
  unfold pairIdx
  change 10 + (i * (21 - i) / 2 + j - i) < 88
  have hi : i < 11 := by omega
  interval_cases i <;> omega

theorem kshape_sound (f : ℕ → G) {RZT : ℕ → ℕ} {INV WT C : ℕ}
    (hI : ∀ c < 255, lInv INV c < 255 ∧ f (lInv INV c) = (f c)⁻¹)
    (h1 : f 1 = (f 0)⁻¹) (h3 : f 3 = (f 2)⁻¹) (h6 : f 6 = (f 5)⁻¹)
    (hL : ∀ i < 11, wN (wrec WT i) < 1000) (hR : ∀ r < 88, rv f (RZT r) = 1)
    (hw : KShape.wordsOK WT = true) (hs : KShape.sqOK RZT INV WT = true)
    (hc0 : KShape.commOK RZT INV WT 0 3 = true) (hc1 : KShape.commOK RZT INV WT 3 11 = true)
    (hj : KShape.conjOK RZT INV WT C = true) :
    (∀ a ∈ Vz f WT, ∀ b ∈ Vz f WT, a * b = b * a) ∧ (∀ a ∈ Vz f WT, a * a = 1) ∧
    Finite (Vz f WT) ∧ Nat.card (Vz f WT) ≤ 2 ^ 11 ∧ f 5 ∈ Vz f WT ∧
    Vz f WT ≤ closure ({f 0, f 2, f 5} : Set G) ∧
    closure ({f 0, f 2, f 5} : Set G) ≤ normalizer (Vz f WT) ∧
    Nat.card (closure ({f 0, f 2, f 5} : Set G)) ≤ 2 ^ 11 * Nat.card (closure ({f 0, f 2} : Set G)) := by
  have hI' : ∀ c < 255, f (lInv INV c) = (f c)⁻¹ := fun c hc => (hI c hc).2
  have hzl : ∀ i (hi : i < 11) e, e < 255 → wN (zr INV WT i e) ≤ 1999 := fun i hi e he =>
    zr_len f hI hL hw hi he
  have hzo : ∀ i (hi : i < 11) e, e < 255 → RecOK (zr INV WT i e) := fun i hi e he =>
    (zr_spec f hI hL hw hi he).2.1
  have hsq : ∀ i : Fin 11, zi f WT i * zi f WT i = 1 := by
    intro i
    have hs' : same INV (RZT i.1) (rcat (zr INV WT i.1 5) (zr INV WT i.1 5)) = true :=
      rngAll_spec 1 hs i.1 (Nat.zero_le _) i.2 (by omega)
    have hE := same_val f hI' hs'
    rw [hR i.1 (by omega)] at hE
    obtain ⟨-, -, e3⟩ := rcat_spec f (hzo i i.2 5 (by norm_num)) (hzo i i.2 5 (by norm_num))
      (by have := hzl i i.2 5 (by norm_num); omega)
    rw [e3, zr5_val f hI hL hw i.2] at hE
    exact hE
  have hcomm : ∀ i j : Fin 11, i.1 < j.1 → Commute (zi f WT i) (zi f WT j) := by
    intro i j hij
    have hs' : same INV (RZT (pairIdx i j))
        (rcat (rcat (zr INV WT i 6) (zr INV WT j 6)) (rcat (zr INV WT i 5) (zr INV WT j 5))) = true := by
      rcases Nat.lt_or_ge i.1 3 with hi | hi
      · exact rngAll_spec 1 (rngAll_spec 1 hc0 i (Nat.zero_le _) hi (by omega)) j hij j.2 (by omega)
      · exact rngAll_spec 1 (rngAll_spec 1 hc1 i hi i.2 (by omega)) j hij j.2 (by omega)
    have hE := same_val f hI' hs'
    rw [hR _ (pairIdx_lt hij j.2)] at hE
    have l6i := hzl i i.2 6 (by norm_num)
    have l6j := hzl j j.2 6 (by norm_num)
    have l5i := hzl i i.2 5 (by norm_num)
    have l5j := hzl j j.2 5 (by norm_num)
    obtain ⟨a1, a2, a3⟩ := rcat_spec f (hzo i i.2 6 (by norm_num)) (hzo j j.2 6 (by norm_num))
      (by omega)
    obtain ⟨b1, b2, b3⟩ := rcat_spec f (hzo i i.2 5 (by norm_num)) (hzo j j.2 5 (by norm_num))
      (by omega)
    obtain ⟨-, -, c3⟩ := rcat_spec f a2 b2 (by omega)
    rw [c3, a3, b3, zr6_val f hI h6 hL hw i.2, zr6_val f hI h6 hL hw j.2, zr5_val f hI hL hw i.2,
      zr5_val f hI hL hw j.2] at hE
    have e : zi f WT ⟨i, i.2⟩ = zi f WT i := rfl
    have e' : zi f WT ⟨j, j.2⟩ = zi f WT j := rfl
    rw [e, e'] at hE
    have key : zi f WT i * zi f WT j = zi f WT j * zi f WT i *
        ((zi f WT i)⁻¹ * (zi f WT j)⁻¹ * (zi f WT i * zi f WT j)) := by group
    rw [hE, mul_one] at key
    exact key
  have hc : ∀ i j : Fin 11, Commute (zi f WT i) (zi f WT j) := by
    intro i j
    rcases lt_trichotomy i.1 j.1 with h | h | h
    · exact hcomm i j h
    · rw [Fin.ext h]
    · exact (hcomm j i h).symm
  have hconj : ∀ q, (hq : q < 22) → f (2 * (q % 2) + 1) * zi f WT ⟨q / 2, by omega⟩ * f (2 * (q % 2)) ∈ Vz f WT := by
    intro q hq
    have hs' : same INV (RZT (66 + q))
        (rcat (rcat (rcat (lit (2 * (q % 2) + 1)) (zr INV WT (q / 2) 5)) (lit (2 * (q % 2))))
          (rinv INV (prodW INV WT (Nat.land (Nat.shiftRight C (Nat.mul 16 q)) 65535)))) = true :=
      rngAll_spec 1 hj q (Nat.zero_le _) hq (by omega)
    have hE := same_val f hI' hs'
    rw [hR _ (by omega)] at hE
    have hg : 2 * (q % 2) + 1 < 255 := by omega
    have hg' : 2 * (q % 2) < 255 := by omega
    have hi : q / 2 < 11 := by omega
    obtain ⟨p1, p2, p3⟩ := prodW_spec f hI hL hw
      (Nat.land (Nat.shiftRight C (Nat.mul 16 q)) 65535)
    obtain ⟨i1, i2, i3⟩ := rinv_spec f hI p1
    obtain ⟨l1, l2, l3⟩ := lit_spec f hg
    obtain ⟨m1, m2, m3⟩ := lit_spec f hg'
    have hz5 := hzl (q / 2) hi 5 (by norm_num)
    obtain ⟨a1, a2, a3⟩ := rcat_spec f l2 (hzo (q / 2) hi 5 (by norm_num)) (by omega)
    obtain ⟨b1, b2, b3⟩ := rcat_spec f a2 m2 (by omega)
    obtain ⟨-, -, c3⟩ := rcat_spec f b2 i2 (by omega)
    rw [c3, b3, a3, l3, m3, i3, zr5_val f hI hL hw hi] at hE
    rw [mul_inv_eq_one.1 hE]
    exact p2
  have hx : ∀ i : Fin 11, (f 0)⁻¹ * zi f WT i * f 0 ∈ Vz f WT := by
    intro i
    have := hconj (2 * i) (by omega)
    have e1 : 2 * (2 * i.1 % 2) + 1 = 1 := by omega
    have e2 : 2 * (2 * i.1 % 2) = 0 := by omega
    have e3 : (⟨2 * i.1 / 2, by omega⟩ : Fin 11) = i := Fin.ext (by simp)
    rwa [e1, e2, e3, h1] at this
  have hy : ∀ i : Fin 11, (f 2)⁻¹ * zi f WT i * f 2 ∈ Vz f WT := by
    intro i
    have := hconj (2 * i + 1) (by omega)
    have e1 : 2 * ((2 * i.1 + 1) % 2) + 1 = 3 := by omega
    have e2 : 2 * ((2 * i.1 + 1) % 2) = 2 := by omega
    have e3 : (⟨(2 * i.1 + 1) / 2, by omega⟩ : Fin 11) = i := Fin.ext (by simp; omega)
    rwa [e1, e2, e3, h3] at this
  obtain ⟨hw0, hwok⟩ := wrec_ok hw
  have hwN : ∀ i : Fin 11, wi f WT i ∈ closure ({f 0, f 2} : Set G) := by
    intro i
    obtain ⟨-, hlet⟩ := hwok i i.2
    unfold wi rv wv
    refine list_prod_mem fun g hg => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hg
    have hq' : wLet (wW (wrec WT i)) q < 4 := hlet q (List.mem_range.1 hq)
    rw [← wLet_byteG]
    have hx0 : f 0 ∈ closure ({f 0, f 2} : Set G) := subset_closure (by simp)
    have hy0 : f 2 ∈ closure ({f 0, f 2} : Set G) := subset_closure (by simp)
    generalize wLet (wW (wrec WT i)) q = c at hq' ⊢
    have hne : c ≠ 255 := by omega
    simp only [lvE, hne, ↓reduceIte]
    interval_cases c
    · exact hx0
    · rw [h1]
      exact inv_mem hx0
    · exact hy0
    · rw [h3]
      exact inv_mem hy0
  have hw0' : wi f WT 0 = 1 := by
    unfold wi rv
    change wv (lvE f) (wW (wrec WT 0)) (wN (wrec WT 0)) = 1
    have hn0 : wN 0 = 0 := rfl
    rw [hw0, hn0]
    simp [wv]
  obtain ⟨hab, hsq', hfin, hcard⟩ := elemAb (z := zi f WT) hsq hc
  obtain ⟨hVK, hKN, hKc⟩ := nclosure_bound (f 0) (f 2) (f 5) (wi f WT) hwN hw0' hsq hc hx hy
  have hz : f 5 ∈ Vz f WT := by
    have : zi f WT 0 = f 5 := by simp [zi, hw0']
    rw [← this]
    exact subset_closure ⟨0, rfl⟩
  exact ⟨hab, hsq', hfin, hcard, hz, hVK, hKN, hKc⟩

theorem krs_inv : CFSG.KJ4.KRS.INV = invJ := Nat.eq_of_beq_eq_true inv_ok

theorem wrec_len : ∀ i < 11, wN (wrec WREC i) < 1000 := by decide +kernel

theorem kshape_krs (x y t z : G) (ht : t * t = 1)
    (hR : ∀ r < 88, rv (jv x y t z) (CFSG.KJ4.KRS.RZT r) = 1) :
    (∀ a ∈ Vz (jv x y t z) WREC, ∀ b ∈ Vz (jv x y t z) WREC, a * b = b * a) ∧
    (∀ a ∈ Vz (jv x y t z) WREC, a * a = 1) ∧ Finite (Vz (jv x y t z) WREC) ∧
    Nat.card (Vz (jv x y t z) WREC) ≤ 2 ^ 11 ∧ z ∈ Vz (jv x y t z) WREC ∧
    Vz (jv x y t z) WREC ≤ closure ({x, y, z} : Set G) ∧
    closure ({x, y, z} : Set G) ≤ normalizer (Vz (jv x y t z) WREC) ∧
    Nat.card (closure ({x, y, z} : Set G)) ≤ 2 ^ 11 * Nat.card (closure ({x, y} : Set G)) := by
  have hI : ∀ c < 255, lInv CFSG.KJ4.KRS.INV c < 255 ∧
      jv x y t z (lInv CFSG.KJ4.KRS.INV c) = (jv x y t z c)⁻¹ := fun c _ => by
    rw [krs_inv]
    exact jv_inv x y t z ht c
  have := kshape_sound (jv x y t z) hI (by simp [jv]) (by simp [jv]) (by simp [jv]) wrec_len hR
    words_ok sq_ok comm_ok0 comm_ok1 conj_ok
  have e0 : jv x y t z 0 = x := by simp [jv]
  have e2 : jv x y t z 2 = y := by simp [jv]
  have e5 : jv x y t z 5 = z := by simp [jv]
  rw [e0, e2, e5] at this
  exact this

end CFSG.Certificates.J4KShape

end
