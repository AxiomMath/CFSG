module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt
public import CFSG.Sporadic.Schreier.PairClasses
public import CFSG.Certificates.Kernel.SporSch.TabSum
import CFSG.Certificates.Kernel.SporSch.TabChainLv
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Certificates.Kernel.SporSch.PairClTDefs

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative

variable {n : Nat}

@[expose] def RepF (n : Nat) (f : Nat → Nat) (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ x (hx : x < n), f x = (g ⟨x, hx⟩ : Nat)

@[expose] def nfArr (nb F : Nat) : Array Nat :=
  Array.ofFn (n := nb) fun i => F / 2 ^ (16 * i.val) % 65536

@[expose] def TabChain (n w kS nb BP NS CH NR NL NT BT NQ BQ : Nat)
    (PS PSI LR Ts LT PT QT : Nat → Nat) (S : Array (Array Nat)) (base : Array Nat)
    (bs : List Nat) : Prop :=
  Binds n w PS kS nb BP S base ∧
    allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true ∧ OrbsOK n w PS PSI LR kS nb BP NS CH ∧ n ≤ NS * CH ∧
    TabsT n w kS nb BP NR NL PS PSI LR Ts LT PT QT NT BT NQ BQ ∧ base.toList = bs

theorem nfPtT_sound {w kS nb BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {bs : List Nat}
    (hT : TabChain n w kS nb BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base bs) {F : Nat}
    (hF : nfValidK nb LR F = true) :
    nfOK (rawLevels n S base) (nfArr nb F) = true ∧
      RepF n (nfPtT w NR NL LT PT nb F) (nfElt n S base (nfArr nb F)) :=
  Tab.nfPtT_spec hT.1 hT.2.1 hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.1 hF

theorem strictB_val (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem RepF.lt {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (h : RepF n f g) {x : Nat} (hx : x < n) :
    f x < n := by
  rw [h x hx]
  exact (g _).2

theorem RepF.one : RepF n (fun x => x) 1 := fun _ _ => rfl

theorem RepF.comp {f f' : Nat → Nat} {g g' : Equiv.Perm (Fin n)} (h : RepF n f g)
    (h' : RepF n f' g') : RepF n (fun x => f (f' x)) (g * g') := by
  intro x hx
  have e : (⟨f' x, h'.lt hx⟩ : Fin n) = g' ⟨x, hx⟩ := Fin.ext (h' x hx)
  change f (f' x) = _
  rw [h (f' x) (h'.lt hx), e, Equiv.Perm.mul_apply]

theorem RepF.congr {f : Nat → Nat} {g g' : Equiv.Perm (Fin n)} (h : RepF n f g) (e : g = g') :
    RepF n f g' :=
  e ▸ h

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  simpa [Nat.blt_eq] using h

theorem blt_false {a b : Nat} (h : ¬a < b) : Nat.blt a b = false := by
  cases h' : Nat.blt a b
  · rfl
  · exact absurd (by simpa [Nat.blt_eq] using h') h

theorem powF_succ (f : Nat → Nat) (e x : Nat) : powF f (e + 1) x = f (powF f e x) :=
  strictN_val _ _

theorem RepF.powF {f : Nat → Nat} {g : Equiv.Perm (Fin n)} (h : RepF n f g) :
    ∀ e, RepF n (CFSG.KS.SporSch.powF f e) (g ^ e)
  | 0 => fun _ _ => rfl
  | e + 1 => fun x hx => by
    rw [powF_succ, pow_succ']
    exact (h.comp (RepF.powF h e)) x hx

theorem RepF.unique {f : Nat → Nat} {g g' : Equiv.Perm (Fin n)} (h : RepF n f g)
    (h' : RepF n f g') : g = g' :=
  Equiv.ext fun x => Fin.ext ((h x x.2).symm.trans (h' x x.2))

theorem eqOnL_iff (bs : List Nat) (f g : Nat → Nat) :
    eqOnL bs f g = true ↔ ∀ b ∈ bs, f b = g b := by
  induction bs with
  | nil => simp [eqOnL]
  | cons b bs ih =>
    change Bool.rec (motive := fun _ => Bool) false (eqOnL bs f g) (Nat.beq (f b) (g b)) = true ↔ _
    rw [bAnd_iff, ih, Nat.beq_eq, List.forall_mem_cons]

theorem bNot_iff (b : Bool) :
    Bool.rec (motive := fun _ => Bool) true false b = true ↔ b ≠ true := by
  cases b <;> simp

variable {H : Subgroup (Equiv.Perm (Fin n))} {bs : List Nat}

theorem eq_of_eqOnL (hH : BaseFaithful H bs) {f g : Nat → Nat} {u v : Equiv.Perm (Fin n)}
    (hf : RepF n f u) (hg : RepF n g v) (hu : u ∈ H) (hv : v ∈ H) (h : eqOnL bs f g = true) :
    u = v := by
  have h1 := hH (v⁻¹ * u) (H.mul_mem (H.inv_mem hv) hu) fun x hx => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    refine Fin.ext ?_
    rw [← hf x x.2, ← hg x x.2]
    exact (eqOnL_iff bs f g).1 h x hx
  exact (inv_mul_eq_one.1 h1).symm

theorem eqOnL_of_eq (hbs : ∀ b ∈ bs, b < n) {f g : Nat → Nat} {u : Equiv.Perm (Fin n)}
    (hf : RepF n f u) (hg : RepF n g u) : eqOnL bs f g = true :=
  (eqOnL_iff bs f g).2 fun b hb => by rw [hf b (hbs b hb), hg b (hbs b hb)]

theorem fixL_iff (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {f : Nat → Nat}
    {u : Equiv.Perm (Fin n)} (hf : RepF n f u) (hu : u ∈ H) :
    eqOnL bs f (fun x => x) = true ↔ u = 1 :=
  ⟨eq_of_eqOnL hH hf RepF.one hu H.one_mem, fun h => eqOnL_of_eq hbs hf (h ▸ RepF.one)⟩

theorem ordPL_iff (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {f : Nat → Nat}
    {u : Equiv.Perm (Fin n)} (hf : RepF n f u) (hu : u ∈ H) {p : Nat} (hp : p.Prime) :
    ordPL bs f p = true ↔ orderOf u = p := by
  have : Fact p.Prime := ⟨hp⟩
  unfold ordPL
  rw [bAnd_iff, fixL_iff hH hbs (hf.powF p) (H.pow_mem hu p), bNot_iff, Ne,
    fixL_iff hH hbs hf hu]
  constructor
  · rintro ⟨h1, h2⟩
    exact orderOf_eq_prime h1 h2
  · intro h
    refine ⟨h ▸ pow_orderOf_eq_one u, fun h1 => ?_⟩
    rw [h1, orderOf_one] at h
    exact hp.one_lt.ne h

theorem ord9L_iff (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {f : Nat → Nat}
    {u : Equiv.Perm (Fin n)} (hf : RepF n f u) (hu : u ∈ H) :
    ord9L bs f = true ↔ orderOf u = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold ord9L
  rw [bAnd_iff, fixL_iff hH hbs (hf.powF 9) (H.pow_mem hu 9), bNot_iff, Ne,
    fixL_iff hH hbs (hf.powF 3) (H.pow_mem hu 3)]
  constructor
  · rintro ⟨h1, h2⟩
    have := orderOf_eq_prime_pow (p := 3) (n := 1) (x := u) (by simpa using h2) (by simpa using h1)
    simpa using this
  · intro h
    exact ⟨h ▸ pow_orderOf_eq_one u, pow_ne_one_of_lt_orderOf (by norm_num) (by omega)⟩

theorem sumN_mul (m B : Nat) (f : Nat → Nat) :
    sumN (m * B) f = sumN m (fun q => sumN B (fun j => f (Nat.add (Nat.mul q B) j))) := by
  induction m with
  | zero => simp [sumN_eq]
  | succ m ih =>
    rw [sumN_eq, sumN_eq] at *
    rw [Nat.succ_mul, List.range_add, List.map_append, List.sum_append, ih, List.range_succ,
      List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, sumN_eq,
      List.map_map]
    congr 2

section Checks

variable {w kS BP NS CH NR NL NT BT NQ BQ : Nat} {PS PSI LR Ts LT PT QT : Nat → Nat}
  {S : Array (Array Nat)} {base : Array Nat}
  (hT : TabChain n w kS 4 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT S base bs)
include hT

noncomputable abbrev eltOf (S : Array (Array Nat)) (base : Array Nat) (F : Nat) :
    Equiv.Perm (Fin n) :=
  nfElt n S base (nfArr 4 F)

theorem nfPtT4 {F : Nat} (hF : nfValidK 4 LR F = true) :
    nfOK (rawLevels n S base) (nfArr 4 F) = true ∧
      RepF n (fun x => nfPtT w NR NL LT PT (nat_lit 4) F x) (eltOf S base F) :=
  nfPtT_sound hT hF

omit hT in
theorem nIf_and (a b : Bool) :
    Bool.rec (motive := fun _ => Nat) 0 1 (Bool.rec (motive := fun _ => Bool) false b a) =
      if a = true ∧ b = true then 1 else 0 := by
  cases a <;> cases b <;> rfl

theorem scanAt_eq (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {X Z : Nat → Nat}
    {z : Equiv.Perm (Fin n)} (hZ : RepF n Z z) (hz : z ∈ H) {c i : Nat}
    (hV : i < c → nfValidK 4 LR (nfX 4 (X i)) = true)
    (hE : i < c → eltOf S base (nfX 4 (X i)) ∈ H) :
    scanAt w NR NL LT PT bs c X Z i = if i < c ∧ orderOf (eltOf S base (nfX 4 (X i)) * z) = 3 ∧
      orderOf (z ^ 2 * eltOf S base (nfX 4 (X i)) * z) = 9 then 1 else 0 := by
  unfold scanAt
  by_cases hi : i < c
  · rw [blt_true hi]
    change strictN (nfX 4 (X i)) _ = _
    rw [strictN_val]
    have hR := (nfPtT4 hT (hV hi)).2
    have hEi := hE hi
    have h1 : RepF n (fun b => nfPtT w NR NL LT PT (nat_lit 4) (nfX 4 (X i)) (Z b))
        (eltOf S base (nfX 4 (X i)) * z) := hR.comp hZ
    have h2 : RepF n (fun b => Z (Z (nfPtT w NR NL LT PT (nat_lit 4) (nfX 4 (X i)) (Z b))))
        (z ^ 2 * eltOf S base (nfX 4 (X i)) * z) :=
      (hZ.comp (hZ.comp h1)).congr (by rw [pow_two]; simp only [mul_assoc])
    have hA := ordPL_iff hH hbs h1 (H.mul_mem hEi hz) Nat.prime_three
    have hB := ord9L_iff hH hbs h2 (H.mul_mem (H.mul_mem (H.pow_mem hz 2) hEi) hz)
    rw [nIf_and]
    simp only [hA, hB, hi, true_and]
  · rw [blt_false hi]
    simp only [hi, false_and, ite_false]

theorem invAt_spec (hH : BaseFaithful H bs) (hbs : ∀ b ∈ bs, b < n) {X : Nat → Nat} {c i : Nat}
    (h : invAt w NR NL LT PT LR bs c X i = true) (hi : i < c)
    (hE : nfOK (rawLevels n S base) (nfArr 4 (nfX 4 (X i))) = true →
      eltOf (n := n) S base (nfX 4 (X i)) ∈ H) :
    nfValidK 4 LR (nfX 4 (X i)) = true ∧ orderOf (eltOf (n := n) S base (nfX 4 (X i))) = 2 := by
  unfold invAt at h
  rw [blt_true hi] at h
  change strictB (nfX 4 (X i)) _ = true at h
  rw [strictB_val, bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hR := nfPtT4 hT h1
  exact ⟨h1, (ordPL_iff hH hbs hR.2 (hE hR.1) Nat.prime_two).1 h2⟩

theorem bind_spec {F P : Nat} (hF : nfValidK 4 LR F = true)
    (h : ∀ x < n, bindAt n w NR NL LT PT F P x = true) :
    RepF n (pg w (mask w) P) (eltOf S base F) := by
  intro x hx
  have h1 := h x hx
  unfold bindAt at h1
  rw [blt_true hx] at h1
  rw [Nat.eq_of_beq_eq_true h1]
  exact (nfPtT4 hT hF).2 x hx

end Checks

end CFSG.KS.SporSch

end
