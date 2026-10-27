module

public import Certificates.Data.Kernel.Cert690.SqPglT
public import CFSG.Certificates.Kernel.Cert690.SqA8S5Sound
public import CFSG.Certificates.Kernel.Cert690.SqPglSound

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62 CFSG.KC.Enum

theorem pqAll_succ (n : ℕ) (p : ℕ → Bool) : pqAll (n + 1) p = (p n && pqAll n p) := by
  change Bool.rec (motive := fun _ => Bool) false (pqAll n p) (p n) = _
  rw [bAnd_eq]

theorem pqAll_spec {p : ℕ → Bool} : ∀ {n : ℕ}, pqAll n p = true → ∀ i < n, p i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    rw [pqAll_succ, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact pqAll_spec h.2 i hi
    · exact h.1

theorem pqAllL_spec {α : Type} {p : α → Bool} :
    ∀ {l : List α}, pqAllL p l = true → ∀ a ∈ l, p a = true
  | [], _, a, ha => absurd ha List.not_mem_nil
  | b :: l, h, a, ha => by
    have e : pqAllL p (b :: l) = (p b && pqAllL p l) := by
      change Bool.rec (motive := fun _ => Bool) false (pqAllL p l) (p b) = _
      rw [bAnd_eq]
    rw [e, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h.1
    · exact pqAllL_spec h.2 a ha

theorem pqBit_lt (n i : ℕ) : pqBit n i < 2 := Nat.and_lt_two_pow (n := 1) _ (by norm_num)

theorem pqL6_lt (A i : ℕ) : pqL6 A i < 64 := Nat.and_lt_two_pow (n := 6) _ (by norm_num)

theorem pqL7_lt (T i : ℕ) : pqL7 T i < 128 := Nat.and_lt_two_pow (n := 7) _ (by norm_num)

theorem pqB0_lt (v w : ℕ) : pqB0 v w < 2 := pqBit_lt _ _

theorem pqDot_lt (f v : ℕ) : pqDot f v < 2 := pqBit_lt _ _

theorem mk_lt128 {a c : ℕ} (ha : a < 2) (hc : c < 64) : Nat.add a (Nat.mul 2 c) < 128 := by
  change a + 2 * c < 128
  omega

theorem pqLift_lt (F A f x : ℕ) : pqLift F A f x < 128 :=
  mk_lt128 (xor_lt2 (Nat.mod_lt x (by norm_num)) (xor_lt2 (pqBit_lt _ _) (pqDot_lt _ _)))
    (pqL6_lt _ _)

theorem pqInv_lt (F A f y : ℕ) : pqInv F A f y < 128 :=
  mk_lt128 (xor_lt2 (Nat.mod_lt y (by norm_num)) (xor_lt2 (pqBit_lt _ _) (pqDot_lt _ _)))
    (pqL6_lt _ _)

theorem pqMul_lt {x y : ℕ} (hx : x < 128) (hy : y < 128) : pqMul x y < 128 :=
  mk_lt128 (xor_lt2 (xor_lt2 (Nat.mod_lt x (by norm_num)) (Nat.mod_lt y (by norm_num)))
    (pqB0_lt _ _)) (xor_lt64 (by change x / 2 < 64; omega) (by change y / 2 < 64; omega))

theorem pqInvQ_lt {x : ℕ} (hx : x < 128) : pqInvQ x < 128 :=
  mk_lt128 (xor_lt2 (Nat.mod_lt x (by norm_num)) (pqB0_lt _ _)) (by change x / 2 < 64; omega)

theorem b0n_pqAll : pqAll 64 (fun v => pqAll 64 fun w => b0n v w == Nat.beq (pqB0 v w) 1) = true := by
  decide +kernel

theorem dotN_pqAll : pqAll 64 (fun f => pqAll 64 fun v => dotN f v == Nat.beq (pqDot f v) 1) =
    true := by
  decide +kernel

theorem low_pqAll : pqAll 63 (fun i => Nat.beq (1 <<< lowIdx (i + 1))
    (Nat.land (i + 1) (Nat.sub 64 (i + 1)))) = true := by
  decide +kernel

theorem b0n_pq {v w : ℕ} (hv : v < 64) (hw : w < 64) : b0n v w = Nat.beq (pqB0 v w) 1 :=
  beq_iff_eq.1 (pqAll_spec (pqAll_spec b0n_pqAll v hv) w hw)

theorem dotN_pq {f v : ℕ} (hf : f < 64) (hv : v < 64) : dotN f v = Nat.beq (pqDot f v) 1 :=
  beq_iff_eq.1 (pqAll_spec (pqAll_spec dotN_pqAll f hf) v hv)

theorem low_pq {v : ℕ} (hv : v ≠ 0) (h64 : v < 64) :
    1 <<< lowIdx v = Nat.land v (Nat.sub 64 v) := by
  obtain ⟨i, rfl⟩ : ∃ i, v = i + 1 := ⟨v - 1, by omega⟩
  exact Nat.eq_of_beq_eq_true (pqAll_spec low_pqAll i (by omega))

theorem ite_beq {c : ℕ} (hc : c < 2) : (if Nat.beq c 1 = true then 1 else 0) = c := by
  interval_cases c <;> rfl

theorem ite_beq_xor {a b : ℕ} (ha : a < 2) (hb : b < 2) :
    (if (Nat.beq a 1 ^^ Nat.beq b 1) = true then 1 else 0) = Nat.xor a b := by
  interval_cases a <;> interval_cases b <;> rfl

theorem beq_xor3 {a b c : ℕ} (ha : a < 2) (hb : b < 2) (hc : c < 2) :
    Nat.beq (Nat.xor (Nat.xor a b) c) 1 = (Nat.beq a 1 ^^ Nat.beq b 1 ^^ Nat.beq c 1) := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> rfl

section Masks

variable {g F A : ℕ} (hF : pqFOK F A = true) (hA : ∀ v < 64, Code.act g v = pqL6 A v)
include hF

theorem pqFOK_zero : pqBit F 0 = 0 := by
  have e := hF
  unfold pqFOK at e
  rw [bAnd_eq, Bool.and_eq_true] at e
  exact Nat.eq_of_beq_eq_true e.1

theorem pqFOK_step {v : ℕ} (hv : v ≠ 0) (h64 : v < 64) : pqFStep F A v = true := by
  have e := hF
  unfold pqFOK at e
  rw [bAnd_eq, Bool.and_eq_true] at e
  obtain ⟨i, rfl⟩ : ∃ i, v = i + 1 := ⟨v - 1, by omega⟩
  exact pqAll_spec e.2 i (by omega)

include hA in
theorem fB_pq : ∀ n v, v < 64 → v ≤ n → fB g n v = Nat.beq (pqBit F v) 1
  | 0, v, _, hv => by
    obtain rfl : v = 0 := by omega
    rw [pqFOK_zero hF]
    rfl
  | n + 1, v, h64, hv => by
    have e : fB g (n + 1) v = if v = 0 then false else
        (fB g n (v ^^^ (1 <<< lowIdx v)) ^^
          b0n (Code.act g (v ^^^ (1 <<< lowIdx v))) (Code.act g (1 <<< lowIdx v)) ^^
          b0n (v ^^^ (1 <<< lowIdx v)) (1 <<< lowIdx v)) := rfl
    rw [e]
    by_cases h0 : v = 0
    · subst h0
      rw [if_pos rfl, pqFOK_zero hF]
      rfl
    · have hlt := lowIdx_xor_lt h0 h64
      have he : 1 <<< lowIdx v < 64 := by
        rw [Nat.one_shiftLeft]
        exact two_pow_lowIdx_lt v
      have hw : v ^^^ (1 <<< lowIdx v) < 64 := by omega
      rw [if_neg h0, fB_pq n _ hw (by omega), hA _ hw, hA _ he, b0n_pq (pqL6_lt _ _) (pqL6_lt _ _),
        b0n_pq hw he]
      have hs := pqFOK_step hF h0 h64
      unfold pqFStep at hs
      rw [Nat.beq_eq] at hs
      rw [hs, low_pq h0 h64, beq_xor3 (pqBit_lt _ _) (pqB0_lt _ _) (pqB0_lt _ _)]
      rfl

include hA in
theorem liftF_pq {f x : ℕ} (hf : f < 64) (hx : x < 128) : liftF g f x = pqLift F A f x := by
  unfold liftF
  rw [fB_pq hF hA 64 (x / 2) (by omega) (by omega), dotN_pq hf (by omega : x / 2 < 64),
    ite_beq_xor (pqBit_lt _ _) (pqDot_lt _ _), hA _ (by omega)]
  rfl

include hA in
theorem invF_pq {g' A' : ℕ} (hA' : ∀ v < 64, Code.act g' v = pqL6 A' v) {f y : ℕ} (hf : f < 64)
    (hy : y < 128) : invF g g' f y = pqInv F A' f y := by
  unfold invF
  rw [hA' _ (by omega), fB_pq hF hA 64 _ (pqL6_lt _ _) (pqL6_lt _ _).le,
    dotN_pq hf (pqL6_lt _ _), ite_beq_xor (pqBit_lt _ _) (pqDot_lt _ _)]
  rfl

end Masks

theorem qmulN_pq (x y : ℕ) (hx : x < 128) (hy : y < 128) : qmulN x y = pqMul x y := by
  unfold qmulN
  dsimp only
  rw [b0n_pq (by omega) (by omega), ite_beq (pqB0_lt _ _)]
  rfl

theorem qinvN_pq (x : ℕ) (hx : x < 128) : qinvN x = pqInvQ x := by
  unfold qinvN
  dsimp only
  rw [b0n_pq (by omega) (by omega), ite_beq (pqB0_lt _ _)]
  rfl

theorem pqAOK_spec {g A : ℕ} (h : pqAOK g A = true) : ∀ v < 64, Code.act g v = pqL6 A v := by
  intro v hv
  rw [act_eq_actF]
  exact Nat.eq_of_beq_eq_true (pqAll_spec h v hv)

abbrev PqRec := (ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × List (ℕ × ℕ)

structure RecFacts (Fr Ar : ℕ) (X : PqRec) : Prop where
  i1 : X.1.2.1 = 1
  aU : ∀ v < 64, Code.act X.1.1 v = pqL6 X.2.2.1 v
  fU : pqFOK X.2.1 X.2.2.1 = true
  aK : ∀ v < 64, Code.act X.1.2.2.1 v = pqL6 X.2.2.2.2.1 v
  fK : pqFOK X.2.2.2.1 X.2.2.2.2.1 = true
  aK' : ∀ v < 64, Code.act X.1.2.2.2 v = pqL6 X.2.2.2.2.2.1 v
  kk : ∀ v < 64, pqL6 X.2.2.2.2.1 (pqL6 X.2.2.2.2.2.1 v) = v ∧
    pqL6 X.2.2.2.2.2.1 (pqL6 X.2.2.2.2.1 v) = v
  cs : ∀ p ∈ X.2.2.2.2.2.2.2, ∀ v < 64, Code.act p.1 v = pqL6 p.2 v
  tab : ∀ x < 128, pqL7 X.2.2.2.2.2.2.1 x =
    pqLift X.2.2.2.1 X.2.2.2.2.1 0 (pqInv Fr Ar 0 (pqInv X.2.2.2.1 X.2.2.2.2.2.1 0 x))
  inn : ∀ f < 64, pqInnOK X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 (pqE X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 f)
    (pqInvQ (pqE X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 f)) f = true

theorem recFacts_of {Fr Ar : ℕ} {X : PqRec} (h : pqRecOK Fr Ar X = true) : RecFacts Fr Ar X := by
  unfold pqRecOK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hi, hau, hfu, hak, hfk, hak', hkk, hcs, htab, hinn⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true hi, pqAOK_spec hau, hfu, pqAOK_spec hak, hfk, pqAOK_spec hak',
    fun v hv => ?_, fun p hp => pqAOK_spec (pqAllL_spec hcs p hp),
    fun x hx => Nat.eq_of_beq_eq_true (pqAll_spec htab x hx), pqAll_spec hinn⟩
  have e := pqAll_spec hkk v hv
  rw [Bool.and_eq_true] at e
  exact ⟨Nat.eq_of_beq_eq_true e.1, Nat.eq_of_beq_eq_true e.2⟩

theorem guessF_congr {φ ψ : ℕ → ℕ} (h : ∀ x < 128, φ x = ψ x) : guessF φ = guessF ψ := by
  have hw : innWF φ = innWF ψ := by
    unfold innWF
    rw [h 2 (by norm_num), h 4 (by norm_num), h 8 (by norm_num), h 16 (by norm_num),
      h 32 (by norm_num), h 64 (by norm_num)]
  have hc : ((List.range 128).all fun x =>
      qmulN (qmulN (qinvN (2 * innWF ψ)) x) (2 * innWF ψ) == φ x) =
      (List.range 128).all fun x => qmulN (qmulN (qinvN (2 * innWF ψ)) x) (2 * innWF ψ) == ψ x :=
    all_range_congr fun x hx => by rw [h x hx]
  unfold guessF
  rw [hw, hc]

theorem pqE_lt (Fu Au T f : ℕ) : pqE Fu Au T f < 128 := by
  have := innWF_lt (pqPhi Fu Au T f)
  change 2 * innWF (pqPhi Fu Au T f) < 128
  omega

theorem guessF_pq {Fu Au T f : ℕ}
    (h : pqInnOK Fu Au T (pqE Fu Au T f) (pqInvQ (pqE Fu Au T f)) f = true) :
    guessF (pqPhi Fu Au T f) = some (pqE Fu Au T f) := by
  unfold guessF
  rw [if_pos]
  · rfl
  · rw [List.all_eq_true]
    intro x hx
    have hx' := List.mem_range.1 hx
    have e := Nat.eq_of_beq_eq_true (pqAll_spec h x hx')
    have he := pqE_lt Fu Au T f
    change (qmulN (qmulN (qinvN (pqE Fu Au T f)) x) (pqE Fu Au T f) == pqPhi Fu Au T f x) = true
    rw [qinvN_pq _ he, qmulN_pq _ _ (pqInvQ_lt he) hx', qmulN_pq _ _ (pqMul_lt (pqInvQ_lt he) hx') he,
      e, beq_self_eq_true]

theorem sOf_pq (r₁ : ℕ) {r₂ : ℕ} (hroot : rootF r₂ = 0) (b : Bool × Bool) :
    sOf #[rootF r₁, rootF r₂] b.1 b.2 1 = if b.2 then 1 else 0 := by
  have hq : qmulN 0 z0N = 1 := by decide
  have h1 : (#[rootF r₁, rootF r₂] : Array ℕ)[1]! = 0 := by simp [hroot]
  have h10 : ((1 : ℕ) == 0) = false := rfl
  unfold sOf
  simp only [h1, hq, h10]
  cases b.2 <;> rfl

theorem candT_pq {Fr Ar : ℕ} (hFr : pqFOK Fr Ar = true)
    (hAr : ∀ v < 64, Code.act 1108378656 v = pqL6 Ar v) {X : PqRec} (hX : RecFacts Fr Ar X)
    (r₁ : ℕ) (hroot : rootF 1108378656 = 0) {f : ℕ} (hf : f < 64) (b : Bool × Bool) :
    candT r₁ 1108378656 X.1 f b = some (pqVal Fr Ar X (if b.2 then 1 else 0) f) := by
  unfold candT
  rw [hX.i1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
  have hphi : ∀ x < 128, liftF X.1.1 f (liftF X.1.2.2.1 0 (invF 1108378656 1108378656 0
      (invF X.1.2.2.1 X.1.2.2.2 0 x))) = pqPhi X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 f x := by
    intro x hx
    rw [invF_pq hX.fK hX.aK hX.aK' (by norm_num) hx, invF_pq hFr hAr hAr (by norm_num) (pqInv_lt _ _ _ _),
      liftF_pq hX.fK hX.aK (by norm_num) (pqInv_lt _ _ _ _), ← hX.tab x hx,
      liftF_pq hX.fU hX.aU hf (pqL7_lt _ _)]
    rfl
  rw [guessF_congr hphi, guessF_pq (hX.inn f hf)]
  dsimp only
  have he := pqE_lt X.2.1 X.2.2.1 X.2.2.2.2.2.2.1 f
  rw [if_pos he, sOf_pq r₁ hroot b]
  have hs : (if b.2 then 1 else 0) < 128 := by split <;> norm_num
  rw [invF_pq hX.fK hX.aK hX.aK' (by norm_num) he,
    liftF_pq hFr hAr (by norm_num) (pqInv_lt _ _ _ _),
    liftF_pq hX.fK hX.aK (by norm_num) (pqLift_lt _ _ _ _), liftF_pq hX.fK hX.aK (by norm_num) hs,
    qmulN_pq _ _ (pqLift_lt _ _ _ _) (pqLift_lt _ _ _ _),
    qmulN_pq _ _ (pqMul_lt (pqLift_lt _ _ _ _) (pqLift_lt _ _ _ _)) he]
  rfl

theorem liftTab_ne (g : ℕ) {f f' : ℕ} (hf : f < 64) (hf' : f' < 64) (hne : f ≠ f') :
    liftTab g f ≠ liftTab g f' := by
  intro e
  apply hne
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 6
  · have h1 := congrArg (fun t : Array ℕ => t[2 * 2 ^ j]!) e
    have hp := two_pow_lt64 hj
    have hx : 2 * 2 ^ j < 128 := by omega
    have hm : 2 * 2 ^ j % 2 = 0 := by omega
    have hd : 2 * 2 ^ j / 2 = 2 ^ j := by omega
    rw [liftTab_getElem! hx, liftTab_getElem! hx, hm, hd, fTable_twist g f _ hp,
      fTable_twist g f' _ hp, dotB_two_pow f hj, dotB_two_pow f' hj] at h1
    revert h1
    cases (fTable g 0)[2 ^ j]! <;> cases f.testBit j <;> cases f'.testBit j <;> simp
  · have h6 : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem distinctTabs_lift (g : ℕ) :
    distinctTabs ((List.range 64).map fun f => liftTab g f).toArray = true := by
  unfold distinctTabs
  rw [Array.all_eq_true]
  intro i hi
  rw [Array.all_eq_true]
  intro j hj
  simp only [Array.size_range, List.size_toArray, List.length_map, List.length_range] at hi hj
  simp only [Array.getElem_range]
  by_cases hij : i ≤ j
  · simp [hij]
  · have hi' : i < ((List.range 64).map fun f => liftTab g f).length := by simpa using hi
    have hj' : j < ((List.range 64).map fun f => liftTab g f).length := by simpa using hj
    rw [List.getElem!_toArray, List.getElem!_toArray, getElem!_pos _ i hi', getElem!_pos _ j hj']
    simp only [List.getElem_map, List.getElem_range]
    simpa [hij] using liftTab_ne g hi hj (by omega)

theorem all_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun H a ha => (h a ha) ▸ H a ha, fun H a ha => (h a ha).symm ▸ H a ha⟩

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, (h a ha) ▸ e⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, (h a ha).symm ▸ e⟩⟩

theorem filterMap_some_map (v : ℕ → ℕ) :
    ∀ l : List ℕ, (l.map fun f => some (v f)).filterMap (fun o => o) = l.map v
  | [] => rfl
  | a :: l => by
    simp [filterMap_some_map v l]

theorem getElem!_map_range {α : Type} [Inhabited α] {n f : ℕ} (g : ℕ → α) (hf : f < n) :
    ((List.range n).map g)[f]! = g f := by
  rw [getElem!_pos _ f (by simpa using hf)]
  simp

namespace PglHyp

variable {K K0 : List ℕ} {P P0 : List (ℕ × ℕ)} {T W1 W2 : IT} {M1 M2 : ℕ}
  (h : PglHyp K K0 P P0 T W1 W2 M1 M2)
include h

theorem cm_get_of {w : ℕ × ℕ × ℕ × ℕ} (hw : cmK T W1 W2 K.length M1 M2 w = true) :
    (classMapOfReps K.toArray (invsL K).toArray #[2166376464, 1108378656]).get? w.1 =
      some (w.2.1, w.2.2.1) ∧ w.2.1 < 2 := by
  unfold cmK at hw
  rw [Bool.and_eq_true, Nat.blt_eq] at hw
  obtain ⟨hq, hw⟩ := hw
  have hkL : K[T.find w.2.2.1 K.length]! = w.2.2.1 := by
    rw [h.ix] at hq ⊢
    rw [getElem!_pos K _ hq]
    exact List.getElem_idxOf hq
  rw [classMapOfReps_two_get?, h.fc1, h.fc2]
  split at hw
  · next hi =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    rw [if_pos hw.1, hw.2, hkL]
    simp [hi]
  · next hi =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hw
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
    rw [if_neg (by simp [h2]), if_pos h3, h4, hkL]
    simp [h1]

theorem sq_witMap' : (pglSquareData ()).witMap = witMapOf (sqWitData
    (classMapOfReps K.toArray (invsL K).toArray #[2166376464, 1108378656])
    #[liftTab 2166376464 0, liftTab 1108378656 0] (involL K).toArray) := by
  have e : (pglSquareData ()).witMap = witMapOf (pglSquareData ()).wits := by
    simp only [pglSquareData]
  rw [e, sq_wits, h.elems, h.invs, h.involutions]

theorem wit_get {w : ℕ × ℕ × ℕ × ℕ} (hw : cmK T W1 W2 K.length M1 M2 w = true)
    (hu : w.1 ∈ involL K) : (pglSquareData ()).witMap.get? w.1 = some
      { g := w.1, repIdx := w.2.1, k := w.2.2.1, psi := liftTab w.2.2.1 0,
        tp := compTab (compTab (liftTab w.2.2.1 0)
          ((#[liftTab 2166376464 0, liftTab 1108378656 0] : Array (Array ℕ))[w.2.1]!))
          (invTab (liftTab w.2.2.1 0)),
        itp := invTab (compTab (compTab (liftTab w.2.2.1 0)
          ((#[liftTab 2166376464 0, liftTab 1108378656 0] : Array (Array ℕ))[w.2.1]!))
          (invTab (liftTab w.2.2.1 0))) } := by
  obtain ⟨hcmw, hi⟩ := h.cm_get_of hw
  rw [h.sq_witMap']
  unfold witMapOf sqWitData
  rw [List.map_toArray, List.foldl_toArray]
  refine witMap_foldl_get? ?_ ?_ _ _ (Or.inl hu)
  · intro g w' e
    split at e
    · split at e
      · cases e
        rfl
      · cases e
    · cases e
  · rw [hcmw]
    dsimp only
    rw [if_pos (by simpa using hi)]

theorem sq_root : (pglSquareData ()).root = #[rootF 2166376464, rootF 1108378656] := by
  have e : (pglSquareData ()).root =
      repRoot (innTabs ()) #[liftTab 2166376464 0, liftTab 1108378656 0] := by
    simp [pglSquareData, pglReps, repThetas]
  rw [e]
  unfold repRoot
  simp only [List.map_toArray, List.map_cons, List.map_nil]
  rw [root_eqF h.root1, root_eqF h.root2]

set_option maxHeartbeats 1000000 in
theorem s4 (hout : pglOutersOK (pglData ()) = true) {Fr Ar : ℕ} {I0 : List ℕ} {Xs : List PqRec}
    (hsel : (outersL K K0 == Xs.map fun X => X.1.1) = true) (hi0 : (involL K0 == I0) = true)
    (hcm : Xs.all (fun X => cmK T W1 W2 K.length M1 M2 X.1) = true)
    (hfr : bAnd(pqFOK Fr Ar, bAnd(pqAOK 1108378656 Ar,
      pqAll 64 fun v => Nat.beq (pqL6 Ar (pqL6 Ar v)) v)) = true)
    (hrec : pqAllL (pqRecOK Fr Ar) Xs = true) (hcs : pqAllL (pqCs I0) Xs = true)
    (hbody : certBits.all (fun b => Xs.all (pqBody Fr Ar b)) = true)
    (hroot : rootF 1108378656 = 0) :
    pglS4Of (pglSquareData ()) = true := by
  simp only [bAnd_eq, Bool.and_eq_true] at hfr
  obtain ⟨hFr, hAr0, hrr0⟩ := hfr
  have hAr := pqAOK_spec hAr0
  have hrr : ∀ u < 64, Code.act 1108378656 (Code.act 1108378656 u) = u := by
    intro u hu
    rw [hAr u hu, hAr _ (pqL6_lt _ _)]
    exact Nat.eq_of_beq_eq_true (pqAll_spec hrr0 u hu)
  have hXs : outersL K K0 = Xs.map fun X => X.1.1 := beq_iff_eq.1 hsel
  have hI0 : involL K0 = I0 := beq_iff_eq.1 hi0
  rw [List.all_eq_true] at hcm hbody
  unfold pglS4Of
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by rw [sq_pgl]; exact hout, ?_⟩, ?_⟩, ?_⟩
  · have e := h.s2
    unfold pglS2Of at e
    rw [Bool.and_eq_true] at e
    exact e.2
  · rw [sq_pgl, sq_reps, sq_theta, sq_wits]
    exact h.witOK_ok
  rw [List.all_eq_true]
  intro b hb
  have hB0 := hbody b hb
  rw [List.all_eq_true] at hB0
  rw [sq_pgl, pgl_outers h.enum h.enum0, hXs, List.all_toArray, List.all_map, List.all_eq_true]
  intro X hX
  have hR := recFacts_of (pqAllL_spec hrec X hX)
  have hc : cmK T W1 W2 K.length M1 M2 X.1 = true := hcm X hX
  have hu : X.1.1 ∈ involL K := by
    have e : X.1.1 ∈ outersL K K0 := by
      rw [hXs]
      exact List.mem_map_of_mem hX
    unfold outersL at e
    exact (List.mem_filter.1 e).1
  have hi : X.1.2.1 < 2 := (h.cm_get_of hc).2
  have hB : pqBody Fr Ar b X = true := hB0 X hX
  have hk : ∀ u < 64, Code.act X.1.2.2.1 (Code.act X.1.2.2.2 u) = u := by
    intro u hu
    rw [hR.aK' u hu, hR.aK _ (pqL6_lt _ _)]
    exact (hR.kk u hu).1
  have hk' : ∀ u < 64, Code.act X.1.2.2.2 (Code.act X.1.2.2.1 u) = u := by
    intro u hu
    rw [hR.aK u hu, hR.aK' _ (pqL6_lt _ _)]
    exact (hR.kk u hu).2
  have hr : ∀ u < 64, Code.act (if X.1.2.1 = 0 then 2166376464 else 1108378656)
      (Code.act (if X.1.2.1 = 0 then 2166376464 else 1108378656) u) = u := by
    rw [hR.i1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    exact hrr
  have hsv : ∀ f ∈ List.range 64, candVal (innTabs ()) (liftTab X.1.1 f) (liftTab X.1.2.2.1 0)
      (compTab (compTab (liftTab X.1.2.2.1 0)
        (liftTab (if X.1.2.1 = 0 then 2166376464 else 1108378656) 0)) (invTab (liftTab X.1.2.2.1 0)))
      (invTab (compTab (compTab (liftTab X.1.2.2.1 0)
        (liftTab (if X.1.2.1 = 0 then 2166376464 else 1108378656) 0)) (invTab (liftTab X.1.2.2.1 0))))
      (sOf #[rootF 2166376464, rootF 1108378656] b.1 b.2 X.1.2.1) =
      some (pqVal Fr Ar X (if b.2 then 1 else 0) f) := fun f hf =>
    (candVal_eqT _ _ X.1 f b hk hk' hr (sOf_lt _ _ _ _ hi)).trans
      (candT_pq hFr hAr hR 2166376464 hroot (List.mem_range.1 hf) b)
  simp only [Function.comp_apply]
  rw [h.wit_get hc hu]
  dsimp only
  rw [sq_innTabs, h.sq_root, theta_get hi, List.map_congr_left hsv, filterMap_some_map]
  unfold pqBody at hB
  dsimp only at hB
  simp only [Bool.and_eq_true] at hB ⊢
  refine ⟨⟨⟨⟨beq_self_eq_true _, by simp⟩, hB.1⟩, ?_⟩, distinctTabs_lift _⟩
  rw [List.all_eq_true]
  intro f hf
  have hf' := List.mem_range.1 hf
  have hB2 := List.all_eq_true.1 hB.2 f hf
  rw [getElem!_map_range _ hf']
  dsimp only
  by_cases hv : (pqVal Fr Ar X (if b.2 then 1 else 0) f == 0 ||
    pqVal Fr Ar X (if b.2 then 1 else 0) f == z0N) = true
  · rw [if_pos hv] at hB2 ⊢
    rw [List.getElem!_toArray, getElem!_map_range _ hf']
    have hfx : ((List.range 128).filter fun x => (liftTab X.1.1 f)[x]! == x) =
        (List.range 128).filter fun x => pqLift X.2.1 X.2.2.1 f x == x :=
      List.filter_congr fun x hx => by
        rw [liftTab_eqF _ _ (List.mem_range.1 hx), liftF_pq hR.fU hR.aU hf' (List.mem_range.1 hx)]
    have hmem : ∀ x ∈ (List.range 128).filter (fun x => pqLift X.2.1 X.2.2.1 f x == x), x < 128 :=
      fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1
    have hq : (((List.range 128).filter fun x => pqLift X.2.1 X.2.2.1 f x == x).all
        fun x => qmulN x x == 0) =
        ((List.range 128).filter fun x => pqLift X.2.1 X.2.2.1 f x == x).all
        fun x => pqMul x x == 0 :=
      all_congr_mem fun x hx => by rw [qmulN_pq _ _ (hmem x hx) (hmem x hx)]
    have hcsX : (I0.filter fun w0 => mulF w0 X.1.1 == mulF X.1.1 w0) =
        X.2.2.2.2.2.2.2.map Prod.fst := beq_iff_eq.1 (pqAllL_spec hcs X hX)
    have hw0 : ((pglData ()).elems0.filter fun w0 => w0 != Code.one && Code.mul w0 w0 == Code.one &&
        Code.mul w0 X.1.1 == Code.mul X.1.1 w0) = (X.2.2.2.2.2.2.2.map Prod.fst).toArray := by
      have hl : (K0.filter fun w0 => w0 != Code.one && Code.mul w0 w0 == Code.one &&
          Code.mul w0 X.1.1 == Code.mul X.1.1 w0) =
          (involL K0).filter fun w0 => mulF w0 X.1.1 == mulF X.1.1 w0 := by
        unfold involL
        rw [List.filter_filter]
        apply List.filter_congr
        intro w0 _
        rw [mul_eq_mulF, mul_eq_mulF, mul_eq_mulF, ← oneF_eq,
          Bool.and_comm (w0 != oneF && mulF w0 w0 == oneF)]
        rfl
      rw [pgl_elems0 h.enum h.enum0, List.filter_toArray, hl, hI0, hcsX]
    rw [hfx, hq, hw0, List.all_toArray, List.all_map]
    unfold pqFix at hB2
    dsimp only at hB2
    simp only [Bool.and_eq_true] at hB2 ⊢
    refine ⟨hB2.1, ?_⟩
    rw [← hB2.2]
    apply all_congr_mem
    intro p hp
    apply any_congr_mem
    intro x hx
    rw [hR.cs p hp _ (by have := hmem x hx; omega)]
  · rw [if_neg hv]

end PglHyp

end CFSG.KC.C690

end
