module

public import Certificates.Data.Kernel.U6.Sec3K
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.U6Sec3

open CFSG.KS CFSG.KS.Raw CFSG.KC.Enum

theorem strictB_eq₀ (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem allBlk_of₀ {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
    rw [h len (Nat.lt_succ_self len), allBlk_of₀ (fun l hl => h l (Nat.lt_succ_of_lt hl))]

theorem rec_blocks_of₀ {f : Nat → Bool} : ∀ {q : Nat},
    (∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true
  | 0, _ => rfl
  | q + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true
    rw [h q (Nat.lt_succ_self q), rec_blocks_of₀ (fun h' hh => h h' (Nat.lt_succ_of_lt hh))]

theorem allN_of_forall₀ {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) :
    allN n f = true := by
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true
  have hd := Nat.div_add_mod n 64
  rw [allBlk_of₀ (fun l hl => h _ (by rw [e6, e64, Nat.add_eq]; rw [er] at hl; omega)),
    rec_blocks_of₀ (fun q hq => allBlk_of₀ (fun l hl => h _ (by
      have hl' : l < 64 := hl
      rw [e6, Nat.add_eq]; rw [e64] at hq; omega)))]

open CFSG.KS.Prim

@[expose] noncomputable def unpackAll (kS : Nat) (PS : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := kS) fun j => unpack 693 10 (PS j.val)

@[expose] noncomputable def wordGA (G : Nat → Nat) (w : List Nat) : Nat :=
  w.foldr (fun k acc => pcomp 693 10 (mask 10) (G k) acc) (pidn 693 10)

@[expose] noncomputable def PermK (p q : Nat) : Bool :=
  bAnd(canonK 693 10 (mask 10) (693 * 10) p, bAnd(canonK 693 10 (mask 10) (693 * 10) q,
    permOK 693 10 (mask 10) (693 * 10) p q))

theorem prodAllK_succ {n w m nw d i acc : Nat} {LR TR : Nat → Nat} {f : Nat → Bool} :
    prodAllK n w m nw LR TR f (d + 1) i acc = allN (rcnt (LR i)) (fun a =>
      prodAllK n w m nw LR TR f d (i + 1) (pcomp n w m acc (TR (roff n nw (LR i) + a)))) := by
  unfold prodAllK
  simp only [strictB_eq₀]
  rfl

theorem prodAllK_zero {n w m nw i acc : Nat} {LR TR : Nat → Nat} {f : Nat → Bool} :
    prodAllK n w m nw LR TR f 0 i acc = f acc := rfl

theorem prodLazyK_succ {n nw d i : Nat} {L : List Nat} {LR TR : Nat → Nat} {f : List Nat → Bool} :
    prodLazyK n nw LR TR f (d + 1) i L = allN (rcnt (LR i)) (fun a =>
      prodLazyK n nw LR TR f d (i + 1) (TR (roff n nw (LR i) + a) :: L)) := by
  unfold prodLazyK
  simp only [strictB_eq₀]
  rfl

theorem prodLazyK_zero {n nw i : Nat} {L : List Nat} {LR TR : Nat → Nat} {f : List Nat → Bool} :
    prodLazyK n nw LR TR f 0 i L = f L := rfl

theorem allN_blocks {g : Nat → Bool} {B N : Nat} (h : ∀ s < N, allN B (fun j => g (s * B + j)) = true) :
    allN (N * B) g = true := by
  refine allN_of_forall₀ fun a ha => ?_
  have hB : 0 < B := Nat.pos_of_ne_zero fun h0 => by simp [h0] at ha
  have hs : a / B < N := (Nat.div_lt_iff_lt_mul hB).2 ha
  have := allN_spec (h (a / B) hs) (a % B) (Nat.mod_lt a hB)
  rwa [Nat.div_add_mod'] at this

end CFSG.KC.U6Sec3

end
