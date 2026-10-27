module

public import Certificates.Data.Kernel.Co3Bfs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentModelInputs
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Std.Data.HashSet
import CFSG.Certificates.Kernel.Spor.KeyBfsGen
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.KC.Co3Bfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident

@[expose] def bfsR (N : ℕ) (G : Array (Array ℕ)) :
    Array (Array ℕ) × Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut HL : Array (Array ℕ) := #[idA 276]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  let mut pos : Array ℕ := (Array.replicate (276 * 276) 0).set! (hKey (idA 276)) 1
  for q in [0:N] do
    if q < HL.size then
      for i in [0:3] do
        let y := compA 276 HL[q]! G[i]!
        let k := hKey y
        if pos[k]! == 0 then
          HL := HL.push y
          par := par.push q
          lab := lab.push i
          pos := pos.set! k HL.size
  return (HL, par, lab, pos)

@[expose] def bfsC (N : ℕ) (G : Array (Array ℕ)) (t₀ : Array ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ := Id.run do
  let mut CL : Array (Array ℕ) := #[t₀]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  let mut seen : Std.HashSet ℕ := (∅ : Std.HashSet ℕ).insert (keyOf [0, 1, 2, 3] t₀)
  for q in [0:N] do
    if q < CL.size then
      for k in [0:7] do
        let m := G[k]!
        let y := compA 276 (invCand 276 m) (compA 276 CL[q]! m)
        let key := keyOf [0, 1, 2, 3] y
        if !seen.contains key then
          seen := seen.insert key
          CL := CL.push y
          par := par.push q
          lab := lab.push k
  return (CL, par, lab)

theorem eqA_unpack {p q : ℕ} (hp : canonK 276 9 (mask 9) (276 * 9) p = true)
    (hq : canonK 276 9 (mask 9) (276 * 9) q = true) :
    eqA 276 (unpack 276 9 p) (unpack 276 9 q) = Nat.beq p q := by
  cases h : Nat.beq p q
  · refine neK_sound ?_
    unfold neK
    rw [hp, hq, h]
  · exact eqK_sound h

theorem canon_pc {p q : ℕ} (hp : canonK 276 9 (mask 9) (276 * 9) p = true)
    (hq : canonK 276 9 (mask 9) (276 * 9) q = true) :
    canonK 276 9 (mask 9) (276 * 9) (pc p q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem unpack_get' (P : ℕ) {p : ℕ} (hp : p < 276) : (unpack 276 9 P)[p]! = pt P p := by
  unfold unpack
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]
  rfl

private theorem compA_get (t u : Array ℕ) {p : ℕ} (hp : p < 276) :
    (compA 276 t u)[p]! = t[u[p]!]! := by
  unfold compA
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]

private theorem pt_lt {P : ℕ} (h : canonK 276 9 (mask 9) (276 * 9) P = true) {p : ℕ}
    (hp : p < 276) : pt P p < 276 :=
  Nat.blt_eq.mp (allN_spec (range_of_canonK h) p hp)

private theorem keyOf2 (t : Array ℕ) : keyOf [0, 1] t = t[0]! * 276 + t[1]! := by
  simp [keyOf]

private theorem keyOf4 (t : Array ℕ) :
    keyOf [0, 1, 2, 3] t = ((t[0]! * 276 + t[1]!) * 276 + t[2]!) * 276 + t[3]! := by
  simp [keyOf]

private theorem hKey_unpack (X : ℕ) : hKey (unpack 276 9 X) = keyR X := by
  unfold hKey
  rw [keyOf2, unpack_get' X (p := 0) (by norm_num), unpack_get' X (p := 1) (by norm_num)]
  rfl

private theorem key4_unpack (X : ℕ) : keyOf [0, 1, 2, 3] (unpack 276 9 X) = key4 X := by
  rw [keyOf4, unpack_get' X (p := 0) (by norm_num), unpack_get' X (p := 1) (by norm_num),
    unpack_get' X (p := 2) (by norm_num), unpack_get' X (p := 3) (by norm_num)]
  rfl

private theorem lex_iff (a b c d : ℕ) : lexLtK a b c d = true ↔ a < c ∨ (a = c ∧ b < d) := by
  have e1 : Nat.blt a c = decide (a < c) :=
    Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_iff])
  have e2 : Nat.beq a c = decide (a = c) :=
    Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, decide_eq_true_iff])
  have e3 : Nat.blt b d = decide (b < d) :=
    Bool.eq_iff_iff.mpr (by rw [Nat.blt_eq, decide_eq_true_iff])
  unfold lexLtK
  rw [e1, e2, e3]
  by_cases p : a < c <;> by_cases q : a = c <;> by_cases r : b < d <;> simp [p, q, r]

private theorem injSort {key E S SI : Nat → Nat} {c : Nat}
    (h : ∀ m < c, sortK key E S SI c m = true) :
    ∀ a < c, ∀ b < c, key (E a) = key (E b) → a = b := by
  have hS : ∀ m < c, S m < c ∧ SI m < c ∧ S (SI m) = m ∧
      (m + 1 < c → key (E (S m)) < key (E (S (m + 1)))) := by
    intro m hm
    have hm' := h m hm
    unfold sortK at hm'
    obtain ⟨h1, hm'⟩ := (bAnd_iff _ _).1 hm'
    obtain ⟨h2, hm'⟩ := (bAnd_iff _ _).1 hm'
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 hm'
    refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3,
      fun hm1 => ?_⟩
    have hb : Nat.blt (Nat.succ m) c = true := Nat.ble_eq_true_of_le hm1
    rw [hb] at h4
    exact Nat.le_of_ble_eq_true h4
  have mono : ∀ m1 m2, m1 < m2 → m2 < c → key (E (S m1)) < key (E (S m2)) := by
    intro m1 m2 h12 h2c
    induction m2 with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 h12 with h | h
      · exact Nat.lt_trans (ih h (by omega)) ((hS m (by omega)).2.2.2 h2c)
      · subst h
        exact (hS m1 (by omega)).2.2.2 h2c
  intro a ha b hb e
  obtain ⟨-, ha1, ha2, -⟩ := hS a ha
  obtain ⟨-, hb1, hb2, -⟩ := hS b hb
  rcases Nat.lt_trichotomy (SI a) (SI b) with hlt | heq | hgt
  · have := mono _ _ hlt hb1
    rw [ha2, hb2] at this
    omega
  · rw [← ha2, ← hb2, heq]
  · have := mono _ _ hgt ha1
    rw [ha2, hb2] at this
    omega

private theorem arr_eq {α : Type} [Inhabited α] {A : Array α} {c : ℕ} {f : ℕ → α}
    (hs : A.size = c) (he : ∀ i < c, A[i]! = f i) :
    A = Array.ofFn (n := c) fun k => f k.val := by
  apply Array.ext
  · rw [hs, Array.size_ofFn]
  · intro i h1 h2
    rw [Array.getElem_ofFn, ← getElem!_pos A i h1]
    exact he i (by omega)

private theorem last_par {P : ℕ → ℕ} {c N : ℕ} (hc : 0 < c) (hN : c ≤ N) (hP0 : P 0 = 0)
    (hp : ∀ k, 0 < k → k < c → P k < k) : P (c - 1) < N := by
  rcases Nat.eq_zero_or_pos (c - 1) with h | h
  · rw [h, hP0]
    omega
  · have := hp (c - 1) h (by omega)
    omega

private def stC (G : Array (Array ℕ)) (s : ℕ) (x : Array ℕ) : Array ℕ :=
  compA 276 (invCand 276 G[s]!) (compA 276 x G[s]!)

private theorem bfsC_eq (N : ℕ) (G : Array (Array ℕ)) (t₀ : Array ℕ) :
    bfsC N G t₀ = CFSG.KS.KeyBfsG.keyBfsG (keyOf [0, 1, 2, 3]) (stC G) 7 t₀
      (keyOf [0, 1, 2, 3] t₀) N := rfl

theorem bfsC_sound {N c : ℕ} {G : Array (Array ℕ)} {t₀ : Array ℕ}
    {GP GIP E P L K S SI : ℕ → ℕ}
    (hG : ∀ i < 7, G[i]! = unpack 276 9 (GP i))
    (hGI : ∀ i < 7, invCand 276 G[i]! = unpack 276 9 (GIP i))
    (hGc : ∀ i < 7, canonK 276 9 (mask 9) (276 * 9) (GP i) = true ∧
      canonK 276 9 (mask 9) (276 * 9) (GIP i) = true)
    (hc : 0 < c) (hN : c ≤ N) (h0 : t₀ = unpack 276 9 (E 0)) (hP0 : P 0 = 0) (hL0 : L 0 = 0)
    (hE : ∀ k < c, canonE E k = true)
    (hs : ∀ k, 0 < k → k < c → stepC GP GIP E P L k = true)
    (hl : ∀ k, 0 < k → k + 1 < c → lexOK P L k = true)
    (hk : ∀ m < c, sortK key4 E S SI c m = true)
    (hcl : ∀ q < c, ∀ i < 7, cloC GP GIP E P L K c q i = true) :
    (bfsC N G t₀).1 = Array.ofFn (n := c) (fun k => unpack 276 9 (E k.val)) ∧
      (bfsC N G t₀).2.1 = Array.ofFn (n := c) (fun k => P k.val) ∧
      (bfsC N G t₀).2.2 = Array.ofFn (n := c) (fun k => L k.val) := by
  have step : ∀ k, 0 < k → k < c → P k < k ∧ L k < 7 ∧
      unpack 276 9 (E k) = stC G (L k) (unpack 276 9 (E (P k))) := by
    intro k hk0 hkc
    have h := hs k hk0 hkc
    unfold stepC at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h⟩ := (bAnd_iff _ _).1 h
    rw [strictB_eq'] at h
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h
    have hL : L k < 7 := Nat.blt_eq.mp h2
    refine ⟨Nat.blt_eq.mp h1, hL, ?_⟩
    unfold stC
    rw [hGI _ hL, hG _ hL, compEqK_sound (n := 276) (w := 9) h3]
    exact (compEqK_sound (n := 276) (w := 9) h4).symm
  have stC_get : ∀ q < c, ∀ i < 7, ∀ p < 276,
      (stC G i (unpack 276 9 (E q)))[p]! = cpt GP GIP E q i p := by
    intro q hq i hi p hp
    unfold stC
    rw [hGI i hi, hG i hi, compA_get _ _ hp, compA_get _ _ hp, unpack_get' (GP i) hp,
      unpack_get' (E q) (pt_lt (hGc i hi).1 hp),
      unpack_get' (GIP i) (pt_lt (hE q hq) (pt_lt (hGc i hi).1 hp))]
    rfl
  have R : CFSG.KS.KeyBfsG.GRec (keyOf [0, 1, 2, 3]) (stC G) 7 t₀ (keyOf [0, 1, 2, 3] t₀) c
      (7 * c) (fun i => unpack 276 9 (E i)) P L K := by
    refine ⟨by norm_num, hc, h0.symm, rfl, hP0, hL0, fun a ha b hb e => ?_,
      fun i hi0 hi => step i hi0 hi, fun i hi0 hi => ?_, ?_, fun e he => ?_⟩
    · rw [key4_unpack, key4_unpack] at e
      exact injSort hk a ha b hb e
    · obtain ⟨-, hL1, -⟩ := step i hi0 (by omega)
      obtain ⟨-, hL2, -⟩ := step (i + 1) (by omega) hi
      have := (lex_iff (P i) (L i) (P (i + 1)) (L (i + 1))).1 (hl i hi0 hi)
      omega
    · rcases Nat.eq_zero_or_pos (c - 1) with h | h
      · rw [h, hP0, hL0]
        omega
      · obtain ⟨h1, h2, -⟩ := step (c - 1) h (by omega)
        omega
    · have hq : e / 7 < c := by omega
      have hi : e % 7 < 7 := Nat.mod_lt _ (by norm_num)
      have h := hcl (e / 7) hq (e % 7) hi
      unfold cloC at h
      have ee : Nat.add (Nat.mul 7 (e / 7)) (e % 7) = e := Nat.div_add_mod e 7
      rw [ee, strictB_eq'] at h
      obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
      have hKc : K e < c := Nat.blt_eq.mp h1
      refine ⟨hKc, ?_, ?_⟩
      · rw [keyOf4, stC_get _ hq _ hi 0 (by norm_num), stC_get _ hq _ hi 1 (by norm_num),
          stC_get _ hq _ hi 2 (by norm_num), stC_get _ hq _ hi 3 (by norm_num), key4_unpack,
          Nat.eq_of_beq_eq_true h2]
        rfl
      · rcases Nat.eq_zero_or_pos (K e) with hz | hz
        · exact Or.inl hz
        · right
          have hb0 : Nat.beq (K e) 0 = false :=
            Bool.eq_false_iff.2 fun hb => by have := Nat.eq_of_beq_eq_true hb; omega
          rw [hb0] at h3
          obtain ⟨-, hL, -⟩ := step (K e) hz hKc
          cases hx : lexLtK (e / 7) (e % 7) (P (K e)) (L (K e))
          · have := (lex_iff (e / 7) (e % 7) (P (K e)) (L (K e))).not.1
              (by rw [hx]; exact Bool.false_ne_true)
            omega
          · rw [hx] at h3
            exact absurd h3 Bool.false_ne_true
  obtain ⟨-, hget, hsz, hps, hls⟩ := CFSG.KS.KeyBfsG.keyBfsG_rec R
    (last_par hc hN hP0 fun k hk0 hkc => (step k hk0 hkc).1)
  have hsz' := hsz (Nat.le_refl _)
  rw [bfsC_eq]
  exact ⟨arr_eq (f := fun i => unpack 276 9 (E i)) hsz' fun i hi => (hget i hi).1,
    arr_eq (f := P) (by rw [hps, hsz']) fun i hi => (hget i hi).2.1,
    arr_eq (f := L) (by rw [hls, hsz']) fun i hi => (hget i hi).2.2⟩

private abbrev RSt := Array (Array ℕ) × Array ℕ × Array ℕ × Array ℕ

private def innerR (G : Array (Array ℕ)) (h j : ℕ) (s : RSt) : Id (ForInStep RSt) :=
  if (s.2.2.2[hKey (compA 276 s.1[h]! G[j]!)]! == 0) = true then
    pure (ForInStep.yield (s.1.push (compA 276 s.1[h]! G[j]!), s.2.1.push h, s.2.2.1.push j,
      s.2.2.2.set! (hKey (compA 276 s.1[h]! G[j]!)) (s.1.push (compA 276 s.1[h]! G[j]!)).size))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private def outerR (G : Array (Array ℕ)) (h : ℕ) (s : RSt) : Id (ForInStep RSt) :=
  if h < s.1.size then
    pure (ForInStep.yield (Id.run (forIn (List.range' 0 3) (s.1, s.2.1, s.2.2.1, s.2.2.2)
      (innerR G h))))
  else pure (ForInStep.yield (s.1, s.2.1, s.2.2.1, s.2.2.2))

private def initR : RSt :=
  (#[idA 276], #[0], #[0], (Array.replicate (276 * 276) 0).set! (hKey (idA 276)) 1)

private theorem bfsR_eq (N : ℕ) (G : Array (Array ℕ)) :
    bfsR N G = ((Id.run (forIn (List.range' 0 N) initR (outerR G))).1,
      (Id.run (forIn (List.range' 0 N) initR (outerR G))).2.1,
      (Id.run (forIn (List.range' 0 N) initR (outerR G))).2.2.1,
      (Id.run (forIn (List.range' 0 N) initR (outerR G))).2.2.2) := by
  unfold bfsR
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def stR (G : Array (Array ℕ)) (s : ℕ) (x : Array ℕ) : Array ℕ := compA 276 x G[s]!

private theorem forIn_rel {β γ : Type} (Rl : β → γ → Prop) (l : List ℕ)
    (f : ℕ → β → Id (ForInStep β)) (g : ℕ → γ → Id (ForInStep γ))
    (h : ∀ x ∈ l, ∀ b c, Rl b c → ∃ b' c', f x b = pure (ForInStep.yield b') ∧
      g x c = pure (ForInStep.yield c') ∧ Rl b' c') :
    ∀ b c, Rl b c → Rl (Id.run (forIn l b f)) (Id.run (forIn l c g)) := by
  induction l with
  | nil => exact fun b c hbc => hbc
  | cons x l ih =>
    intro b c hbc
    obtain ⟨b', c', hf, hg, hr⟩ := h x (List.mem_cons_self ..) b c hbc
    rw [List.forIn_cons, List.forIn_cons, hf, hg]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) b' c' hr

private abbrev Small (y : Array ℕ) : Prop := ∀ p : ℕ, y[p]! < 276

private theorem small_hKey {y : Array ℕ} (hy : Small y) : hKey y < 276 * 276 := by
  unfold hKey
  rw [keyOf2]
  have := hy 0
  have := hy 1
  omega

private abbrev RelR (s : CFSG.KS.KeyBfsG.GSt (Array ℕ)) (t : RSt) : Prop :=
  t.1 = s.1 ∧ t.2.1 = s.2.1 ∧ t.2.2.1 = s.2.2.1 ∧ t.2.2.2.size = 276 * 276 ∧
    (∀ i < t.1.size, Small t.1[i]!) ∧
    (∀ x < 276 * 276, (t.2.2.2[x]! ≠ 0 ↔ s.2.2.2.contains x = true)) ∧
    (∀ x < 276 * 276, t.2.2.2[x]! ≠ 0 →
      t.2.2.2[x]! - 1 < t.1.size ∧ hKey t.1[t.2.2.2[x]! - 1]! = x) ∧
    (∀ i < t.1.size, t.2.2.2[hKey t.1[i]!]! ≠ 0)

private theorem small_compA {t : Array ℕ} (ht : Small t) (u : Array ℕ) : Small (compA 276 t u) := by
  intro p
  by_cases hp : p < 276
  · rw [compA_get _ _ hp]
    exact ht _
  · rw [getElem!_neg _ p (by unfold compA; rw [Array.size_ofFn]; exact hp)]
    exact Nat.zero_lt_succ _

private theorem idA_get {p : ℕ} (hp : p < 276) : (idA 276)[p]! = p := by
  unfold idA
  rw [getElem!_pos _ p (by rw [Array.size_ofFn]; exact hp), Array.getElem_ofFn]

private theorem small_idA : Small (idA 276) := by
  intro p
  by_cases hp : p < 276
  · rw [idA_get hp]
    exact hp
  · rw [getElem!_neg _ p (by unfold idA; rw [Array.size_ofFn]; exact hp)]
    exact Nat.zero_lt_succ _

private theorem rel_init_gen (I A : Array ℕ) (hI : Small I) (hA : A.size = 276 * 276)
    (hA0 : ∀ x < 276 * 276, A[x]! = 0) :
    RelR (CFSG.KS.KeyBfsG.initG I (hKey I)) (#[I], #[0], #[0], A.set! (hKey I) 1) := by
  have hk := small_hKey hI
  have hpos : ∀ x < 276 * 276, (A.set! (hKey I) 1)[x]! = if x = hKey I then 1 else 0 := by
    intro x hx
    by_cases e : x = hKey I
    · rw [e, Array.getElem!_set!_self _ _ _ (by omega), ite_eq_left rfl]
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), hA0 x hx, ite_eq_right e]
  have h0 : (#[I] : Array (Array ℕ))[0]! = I := rfl
  unfold CFSG.KS.KeyBfsG.initG
  refine ⟨rfl, rfl, rfl, ?_, fun i hi => ?_, fun x hx => ?_, fun x hx hne => ?_, fun i hi => ?_⟩
  · change (A.set! (hKey I) 1).size = 276 * 276
    rw [Array.size_set!, hA]
  · have : i = 0 := by simp at hi; omega
    subst this
    change Small (#[I] : Array (Array ℕ))[0]!
    rw [h0]
    exact hI
  · change (A.set! (hKey I) 1)[x]! ≠ 0 ↔ ((∅ : Std.HashSet ℕ).insert (hKey I)).contains x = true
    rw [hpos x hx, Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false,
      beq_iff_eq]
    by_cases e : x = hKey I
    · simp [e]
    · simp [e, Ne.symm e]
  · change (A.set! (hKey I) 1)[x]! ≠ 0 at hne
    change (A.set! (hKey I) 1)[x]! - 1 < (#[I] : Array (Array ℕ)).size ∧
      hKey (#[I] : Array (Array ℕ))[(A.set! (hKey I) 1)[x]! - 1]! = x
    rw [hpos x hx] at hne ⊢
    by_cases e : x = hKey I
    · rw [ite_eq_left e]
      refine ⟨by simp, ?_⟩
      rw [Nat.sub_self, h0, e]
    · rw [ite_eq_right e] at hne
      exact absurd rfl hne
  · have : i = 0 := by simp at hi; omega
    subst this
    change (A.set! (hKey I) 1)[hKey (#[I] : Array (Array ℕ))[0]!]! ≠ 0
    rw [h0, hpos _ hk, ite_eq_left rfl]
    exact Nat.one_ne_zero

private theorem rel_init :
    RelR (CFSG.KS.KeyBfsG.initG (idA 276) (hKey (idA 276))) initR :=
  rel_init_gen (idA 276) (Array.replicate (276 * 276) 0) small_idA Array.size_replicate
    (fun x hx => by
      rw [getElem!_pos _ x (by rw [Array.size_replicate]; exact hx), Array.getElem_replicate])

private theorem rel_inner (G : Array (Array ℕ)) {h j : ℕ} {s : CFSG.KS.KeyBfsG.GSt (Array ℕ)}
    {t : RSt} (hr : RelR s t) (hh : h < s.1.size) :
    ∃ s' t', CFSG.KS.KeyBfsG.innerG hKey (stR G) h j s = pure (ForInStep.yield s') ∧
      innerR G h j t = pure (ForInStep.yield t') ∧ RelR s' t' ∧ h < s'.1.size := by
  obtain ⟨HL, par, lab, seen⟩ := s
  obtain ⟨HL', par', lab', pos⟩ := t
  obtain ⟨e1, e2, e3, hsz, hsm, hS, hP2, hP1⟩ := hr
  dsimp only at e1 e2 e3 hsz hsm hS hP2 hP1 hh
  subst e1 e2 e3
  have hy : Small (compA 276 HL'[h]! G[j]!) := small_compA (hsm h hh) _
  have hk := small_hKey hy
  generalize hyv : compA 276 HL'[h]! G[j]! = y at hy hk
  have hst : stR G j HL'[h]! = y := hyv
  by_cases hc : seen.contains (hKey y) = true
  · have hpz : (pos[hKey y]! == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact (hS _ hk).2 hc
    refine ⟨(HL', par', lab', seen), (HL', par', lab', pos), ?_, ?_,
      ⟨rfl, rfl, rfl, hsz, hsm, hS, hP2, hP1⟩, hh⟩
    · unfold CFSG.KS.KeyBfsG.innerG
      dsimp only
      rw [hst, hc]
      rfl
    · unfold innerR
      dsimp only
      rw [hyv, hpz]
      rfl
  · have hnc : seen.contains (hKey y) = false := Bool.eq_false_iff.2 hc
    have hpz : (pos[hKey y]! == 0) = true := by
      rw [beq_iff_eq]
      by_contra hne
      exact hc ((hS _ hk).1 hne)
    have hsz' : (pos.set! (hKey y) (HL'.push y).size).size = 276 * 276 := by
      rw [Array.size_set!, hsz]
    have hget : ∀ x < 276 * 276, (pos.set! (hKey y) (HL'.push y).size)[x]! =
        if x = hKey y then HL'.size + 1 else pos[x]! := by
      intro x _
      by_cases e : x = hKey y
      · subst e
        rw [Array.getElem!_set!_self _ _ _ (by omega), ite_eq_left rfl, Array.size_push]
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), ite_eq_right e]
    refine ⟨(HL'.push y, par'.push h, lab'.push j, seen.insert (hKey y)),
      (HL'.push y, par'.push h, lab'.push j, pos.set! (hKey y) (HL'.push y).size), ?_, ?_,
      ⟨rfl, rfl, rfl, hsz', fun i hi => ?_, fun x hx => ?_, fun x hx hne => ?_, fun i hi => ?_⟩,
      by dsimp only; rw [Array.size_push]; omega⟩
    · unfold CFSG.KS.KeyBfsG.innerG
      dsimp only
      rw [hst, hnc]
      rfl
    · unfold innerR
      dsimp only
      rw [hyv, hpz]
      rfl
    · dsimp only at hi ⊢
      rw [Array.size_push] at hi
      rcases Nat.lt_or_ge i HL'.size with a | a
      · rw [CFSG.KS.KeyBfs.push_lt a]
        exact hsm i a
      · have : i = HL'.size := by omega
        rw [this, CFSG.KS.KeyBfs.push_eq]
        exact hy
    · dsimp only
      rw [hget x hx, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
      by_cases e : x = hKey y
      · simp [e]
      · rw [ite_eq_right e, hS x hx]
        constructor
        · exact Or.inr
        · rintro (a | a)
          · exact absurd a.symm e
          · exact a
    · dsimp only at hne ⊢
      rw [hget x hx] at hne ⊢
      rw [Array.size_push]
      by_cases e : x = hKey y
      · rw [ite_eq_left e, Nat.add_sub_cancel, CFSG.KS.KeyBfs.push_eq]
        exact ⟨Nat.lt_succ_self _, e.symm⟩
      · rw [ite_eq_right e] at hne ⊢
        obtain ⟨a, b⟩ := hP2 x hx hne
        rw [CFSG.KS.KeyBfs.push_lt a]
        exact ⟨by omega, b⟩
    · dsimp only at hi ⊢
      rw [Array.size_push] at hi
      have hz : ∀ z < 276 * 276, z ≠ hKey y → pos[z]! ≠ 0 →
          (pos.set! (hKey y) (HL'.push y).size)[z]! ≠ 0 := by
        intro z hz e hne
        rw [hget z hz, ite_eq_right e]
        exact hne
      rcases Nat.lt_or_ge i HL'.size with a | a
      · rw [CFSG.KS.KeyBfs.push_lt a]
        have hzk := small_hKey (hsm i a)
        by_cases e : hKey HL'[i]! = hKey y
        · rw [hget _ hzk, ite_eq_left e]
          omega
        · exact hz _ hzk e (hP1 i a)
      · have : i = HL'.size := by omega
        rw [this, CFSG.KS.KeyBfs.push_eq, hget _ hk, ite_eq_left rfl]
        omega

private theorem rel_outer (G : Array (Array ℕ)) {h : ℕ} {s : CFSG.KS.KeyBfsG.GSt (Array ℕ)}
    {t : RSt} (hr : RelR s t) :
    ∃ s' t', CFSG.KS.KeyBfsG.outerG hKey (stR G) 3 h s = pure (ForInStep.yield s') ∧
      outerR G h t = pure (ForInStep.yield t') ∧ RelR s' t' := by
  have e1 : t.1 = s.1 := hr.1
  by_cases hh : h < s.1.size
  · have ht : h < t.1.size := by rw [e1]; exact hh
    refine ⟨Id.run (forIn (List.range' 0 3) (s.1, s.2.1, s.2.2.1, s.2.2.2)
        (CFSG.KS.KeyBfsG.innerG hKey (stR G) h)),
      Id.run (forIn (List.range' 0 3) (t.1, t.2.1, t.2.2.1, t.2.2.2) (innerR G h)),
      by simp only [CFSG.KS.KeyBfsG.outerG, hh, ↓reduceIte],
      by simp only [outerR, ht, ↓reduceIte], ?_⟩
    have := forIn_rel (fun (b : CFSG.KS.KeyBfsG.GSt (Array ℕ)) (c : RSt) => RelR b c ∧ h < b.1.size)
      (List.range' 0 3) (CFSG.KS.KeyBfsG.innerG hKey (stR G) h) (innerR G h)
      (fun j _ b c hbc => by
        obtain ⟨b', c', hb, hc, hr', hh'⟩ := rel_inner G (j := j) hbc.1 hbc.2
        exact ⟨b', c', hb, hc, hr', hh'⟩)
      (s.1, s.2.1, s.2.2.1, s.2.2.2) (t.1, t.2.1, t.2.2.1, t.2.2.2) ⟨hr, hh⟩
    exact this.1
  · have ht : ¬ h < t.1.size := by rw [e1]; exact hh
    exact ⟨_, _, by simp only [CFSG.KS.KeyBfsG.outerG, hh, ↓reduceIte],
      by simp only [outerR, ht, ↓reduceIte], hr⟩

private theorem bfsR_rel (N : ℕ) (G : Array (Array ℕ)) :
    RelR (Id.run (forIn (List.range' 0 N)
        (CFSG.KS.KeyBfsG.initG (idA 276) (hKey (idA 276))) (CFSG.KS.KeyBfsG.outerG hKey (stR G) 3)))
      (Id.run (forIn (List.range' 0 N) initR (outerR G))) :=
  forIn_rel RelR (List.range' 0 N) (CFSG.KS.KeyBfsG.outerG hKey (stR G) 3) (outerR G)
    (fun x _ _ _ hbc => rel_outer G (h := x) hbc) _ _ rel_init

private theorem bfsR_main {N c : ℕ} {G : Array (Array ℕ)} {GP E P L K S SI : ℕ → ℕ}
    (hG : ∀ i < 3, G[i]! = unpack 276 9 (GP i))
    (hGc : ∀ i < 3, canonK 276 9 (mask 9) (276 * 9) (GP i) = true)
    (hc : 0 < c) (hN : c ≤ N) (h0 : E 0 = pidn 276 9) (hP0 : P 0 = 0) (hL0 : L 0 = 0)
    (hE : ∀ k < c, canonE E k = true)
    (hs : ∀ k, 0 < k → k < c → stepR GP E P L k = true)
    (hl : ∀ k, 0 < k → k + 1 < c → lexOK P L k = true)
    (hk : ∀ m < c, sortK keyR E S SI c m = true)
    (hcl : ∀ q < c, ∀ i < 3, cloR GP E P L K c q i = true) :
    (bfsR N G).1 = Array.ofFn (n := c) (fun k => unpack 276 9 (E k.val)) ∧
      (bfsR N G).2.1 = Array.ofFn (n := c) (fun k => P k.val) ∧
      (bfsR N G).2.2.1 = Array.ofFn (n := c) (fun k => L k.val) ∧
      ∀ k < c, (bfsR N G).2.2.2[keyR (E k)]! = k + 1 := by
  have step : ∀ k, 0 < k → k < c → P k < k ∧ L k < 3 ∧
      unpack 276 9 (E k) = stR G (L k) (unpack 276 9 (E (P k))) := by
    intro k hk0 hkc
    have h := hs k hk0 hkc
    unfold stepR at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
    have hL : L k < 3 := Nat.blt_eq.mp h2
    refine ⟨Nat.blt_eq.mp h1, hL, ?_⟩
    unfold stR
    rw [hG _ hL]
    exact (compEqK_sound (n := 276) (w := 9) h3).symm
  have hid : unpack 276 9 (pidn 276 9) = idA 276 :=
    idK_sound (by quickRfl : idK 276 9 (mask 9) = true)
  have R : CFSG.KS.KeyBfsG.GRec hKey (stR G) 3 (idA 276) (hKey (idA 276)) c
      (3 * c) (fun i => unpack 276 9 (E i)) P L K := by
    refine ⟨by norm_num, hc, by rw [h0, hid], rfl, hP0, hL0, fun a ha b hb e => ?_,
      fun i hi0 hi => step i hi0 hi, fun i hi0 hi => ?_, ?_, fun e he => ?_⟩
    · rw [hKey_unpack, hKey_unpack] at e
      exact injSort hk a ha b hb e
    · obtain ⟨-, hL1, -⟩ := step i hi0 (by omega)
      obtain ⟨-, hL2, -⟩ := step (i + 1) (by omega) hi
      have := (lex_iff (P i) (L i) (P (i + 1)) (L (i + 1))).1 (hl i hi0 hi)
      omega
    · rcases Nat.eq_zero_or_pos (c - 1) with h | h
      · rw [h, hP0, hL0]
        omega
      · obtain ⟨h1, h2, -⟩ := step (c - 1) h (by omega)
        omega
    · have hq : e / 3 < c := by omega
      have hi : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have h := hcl (e / 3) hq (e % 3) hi
      unfold cloR at h
      have ee : Nat.add (Nat.mul 3 (e / 3)) (e % 3) = e := Nat.div_add_mod e 3
      rw [ee, strictB_eq'] at h
      obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
      have hKc : K e < c := Nat.blt_eq.mp h1
      refine ⟨hKc, ?_, ?_⟩
      · change hKey (compA 276 (unpack 276 9 (E (e / 3))) G[e % 3]!) =
          hKey (unpack 276 9 (E (K e)))
        have hp0 := pt_lt (hGc _ hi) (p := 0) (by norm_num)
        have hp1 := pt_lt (hGc _ hi) (p := 1) (by norm_num)
        rw [hKey_unpack, hG _ hi]
        unfold hKey
        rw [keyOf2, compA_get _ _ (p := 0) (by norm_num), compA_get _ _ (p := 1) (by norm_num),
          unpack_get' (GP _) (p := 0) (by norm_num), unpack_get' (GP _) (p := 1) (by norm_num),
          unpack_get' (E _) hp0, unpack_get' (E _) hp1, Nat.eq_of_beq_eq_true h2]
        rfl
      · rcases Nat.eq_zero_or_pos (K e) with hz | hz
        · exact Or.inl hz
        · right
          have hb0 : Nat.beq (K e) 0 = false :=
            Bool.eq_false_iff.2 fun hb => by have := Nat.eq_of_beq_eq_true hb; omega
          rw [hb0] at h3
          obtain ⟨-, hL, -⟩ := step (K e) hz hKc
          cases hx : lexLtK (e / 3) (e % 3) (P (K e)) (L (K e))
          · have := (lex_iff (e / 3) (e % 3) (P (K e)) (L (K e))).not.1
              (by rw [hx]; exact Bool.false_ne_true)
            omega
          · rw [hx] at h3
            exact absurd h3 Bool.false_ne_true
  obtain ⟨-, hget, hsz, hps, hls⟩ := CFSG.KS.KeyBfsG.keyBfsG_rec (cap := N) R
    (last_par hc hN hP0 fun k hk0 hkc => (step k hk0 hkc).1)
  have hsz' := hsz (Nat.le_refl _)
  rw [CFSG.KS.KeyBfsG.keyBfsG_eq] at hget hsz' hps hls
  dsimp only at hget hsz' hps hls
  obtain ⟨e1, e2, e3, -, -, -, hP2, hP1⟩ := bfsR_rel N G
  rw [bfsR_eq]
  dsimp only
  rw [e1, e2, e3]
  refine ⟨arr_eq (f := fun i => unpack 276 9 (E i)) hsz' fun i hi => (hget i hi).1,
    arr_eq (f := P) (by rw [hps, hsz']) fun i hi => (hget i hi).2.1,
    arr_eq (f := L) (by rw [hls, hsz']) fun i hi => (hget i hi).2.2, fun k hkc => ?_⟩
  have hkt : k < (Id.run (forIn (List.range' 0 N) initR (outerR G))).1.size := by
    rw [e1, hsz']
    exact hkc
  have hEk : (Id.run (forIn (List.range' 0 N) initR (outerR G))).1[k]! = unpack 276 9 (E k) := by
    rw [e1]
    exact (hget k hkc).1
  have hne := hP1 k hkt
  rw [hEk, hKey_unpack] at hne
  have hx : keyR (E k) < 276 * 276 := by
    rw [← hKey_unpack]
    refine small_hKey (y := unpack 276 9 (E k)) fun p => ?_
    by_cases hp : p < 276
    · rw [unpack_get' _ hp]
      exact pt_lt (hE k hkc) hp
    · rw [getElem!_neg _ p (by unfold unpack; rw [Array.size_ofFn]; exact hp)]
      exact Nat.zero_lt_succ _
  obtain ⟨a, b⟩ := hP2 _ hx hne
  have hjc : (Id.run (forIn (List.range' 0 N) initR (outerR G))).2.2.2[keyR (E k)]! - 1 < c := by
    rw [e1, hsz'] at a
    exact a
  rw [e1, (hget _ hjc).1, hKey_unpack] at b
  have := injSort hk _ hjc k hkc b
  omega

theorem bfsR_sound {N c : ℕ} {G : Array (Array ℕ)} {GP E P L K S SI : ℕ → ℕ}
    (hG : ∀ i < 3, G[i]! = unpack 276 9 (GP i))
    (hGc : ∀ i < 3, canonK 276 9 (mask 9) (276 * 9) (GP i) = true)
    (hc : 0 < c) (hN : c ≤ N) (h0 : E 0 = pidn 276 9) (hP0 : P 0 = 0) (hL0 : L 0 = 0)
    (hE : ∀ k < c, canonE E k = true)
    (hs : ∀ k, 0 < k → k < c → stepR GP E P L k = true)
    (hl : ∀ k, 0 < k → k + 1 < c → lexOK P L k = true)
    (hk : ∀ m < c, sortK keyR E S SI c m = true)
    (hcl : ∀ q < c, ∀ i < 3, cloR GP E P L K c q i = true) :
    (bfsR N G).1 = Array.ofFn (n := c) (fun k => unpack 276 9 (E k.val)) ∧
      (bfsR N G).2.1 = Array.ofFn (n := c) (fun k => P k.val) ∧
      (bfsR N G).2.2.1 = Array.ofFn (n := c) (fun k => L k.val) := by
  obtain ⟨a, b, c', -⟩ := bfsR_main hG hGc hc hN h0 hP0 hL0 hE hs hl hk hcl
  exact ⟨a, b, c'⟩

theorem bfsR_pos {N c : ℕ} {G : Array (Array ℕ)} {GP E P L K S SI : ℕ → ℕ}
    (hG : ∀ i < 3, G[i]! = unpack 276 9 (GP i))
    (hGc : ∀ i < 3, canonK 276 9 (mask 9) (276 * 9) (GP i) = true)
    (hc : 0 < c) (hN : c ≤ N) (h0 : E 0 = pidn 276 9) (hP0 : P 0 = 0) (hL0 : L 0 = 0)
    (hE : ∀ k < c, canonE E k = true)
    (hs : ∀ k, 0 < k → k < c → stepR GP E P L k = true)
    (hl : ∀ k, 0 < k → k + 1 < c → lexOK P L k = true)
    (hk : ∀ m < c, sortK keyR E S SI c m = true)
    (hcl : ∀ q < c, ∀ i < 3, cloR GP E P L K c q i = true) :
    ∀ k < c, (bfsR N G).2.2.2[keyR (E k)]! = k + 1 :=
  (bfsR_main hG hGc hc hN h0 hP0 hL0 hE hs hl hk hcl).2.2.2

end CFSG.KC.Co3Bfs

end
