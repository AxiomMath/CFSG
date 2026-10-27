module

public import CFSG.Certificates.Kernel.GMS78RuP.Basic
public import Certificates.Data.GMS78RuSPrimeCheck

public section

namespace CFSG.KC.GMS.P117

open CFSG.GMS78Ru CFSG.GMS78RuS CFSG.GMS78RuSP

@[expose] def pCode (x : Pt) : Nat := x.1 ||| (x.2.1.val <<< 8) ||| (x.2.2.val <<< 11)

@[expose] def pDec (x : Nat) : Pt :=
  (Nat.land x 255, fin8Of (Nat.shiftRight x 8), fin8Of (Nat.shiftRight x 11))

theorem fin8_xor_val (a b : Fin 8) : (a ^^^ b).val = a.val ^^^ b.val := by
  change (a.val ^^^ b.val) % 8 = _
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 3) a.isLt b.isLt)

theorem land255 (x : Nat) : Nat.land x 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

theorem land7 (x : Nat) : Nat.land x 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3

theorem shr3 (x : Nat) : Nat.shiftRight x 3 = x / 8 := Nat.shiftRight_eq_div_pow x 3

theorem shr6 (x : Nat) : Nat.shiftRight x 6 = x / 64 := Nat.shiftRight_eq_div_pow x 6

theorem shr8 (x : Nat) : Nat.shiftRight x 8 = x / 256 := Nat.shiftRight_eq_div_pow x 8

theorem shr11 (x : Nat) : Nat.shiftRight x 11 = x / 2048 := Nat.shiftRight_eq_div_pow x 11

theorem pCode_eq {p : Pt} (hp : p.1 < 256) :
    pCode p = p.1 + 256 * p.2.1.val + 2048 * p.2.2.val := by
  obtain ⟨c, t, d⟩ := p
  have ht := t.isLt
  have hd := d.isLt
  dsimp only at hp ⊢
  have h1 : t.val <<< 8 ||| c = t.val <<< 8 + c :=
    (Nat.shiftLeft_add_eq_or_of_lt (by omega : c < 2 ^ 8) t.val).symm
  have h2 : (d.val <<< 11) ||| (t.val <<< 8 ||| c) = d.val <<< 11 + (t.val <<< 8 ||| c) :=
    (Nat.shiftLeft_add_eq_or_of_lt (Nat.or_lt_two_pow (by rw [Nat.shiftLeft_eq]; omega)
      (by omega : c < 2 ^ 11)) d.val).symm
  change c ||| t.val <<< 8 ||| d.val <<< 11 = _
  rw [Nat.or_comm c, Nat.or_comm _ (d.val <<< 11), h2, h1, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  omega

theorem pCode_c {c : Nat} (hc : c < 256) (t d : Fin 8) : Nat.land (pCode (c, t, d)) 255 = c := by
  have ht := t.isLt
  have hd := d.isLt
  rw [land255, pCode_eq hc]
  dsimp only
  omega

theorem pCode_t {c : Nat} (hc : c < 256) (t d : Fin 8) :
    Nat.land (Nat.shiftRight (pCode (c, t, d)) 8) 7 = t.val := by
  have ht := t.isLt
  have hd := d.isLt
  rw [land7, shr8, pCode_eq hc]
  dsimp only
  omega

theorem pCode_d {c : Nat} (hc : c < 256) (t d : Fin 8) :
    Nat.land (Nat.shiftRight (pCode (c, t, d)) 11) 7 = d.val := by
  have ht := t.isLt
  have hd := d.isLt
  rw [land7, shr11, pCode_eq hc]
  dsimp only
  omega

theorem pDec_code {p : Pt} (hp : p.1 < 256) : pDec (pCode p) = p := by
  obtain ⟨c, t, d⟩ := p
  refine Prod.ext (pCode_c hp t d) (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · change (Nat.shiftRight (pCode (c, t, d)) 8) % 8 = t.val
    rw [← land7]
    exact pCode_t hp t d
  · change (Nat.shiftRight (pCode (c, t, d)) 11) % 8 = d.val
    rw [← land7]
    exact pCode_d hp t d

theorem pCode_pDec {x : Nat} (hx : x < 16384) : pCode (pDec x) = x ∧ (pDec x).1 < 256 := by
  have h1 : (pDec x).1 < 256 := by
    change Nat.land x 255 < 256
    rw [land255]; omega
  refine ⟨?_, h1⟩
  rw [pCode_eq h1]
  change Nat.land x 255 + 256 * (Nat.shiftRight x 8 % 8) + 2048 * (Nat.shiftRight x 11 % 8) = x
  rw [land255, shr8, shr11]
  omega

theorem pCode_inj {p q : Pt} (hp : p.1 < 256) (hq : q.1 < 256) (h : pCode p = pCode q) :
    p = q := by
  rw [← pDec_code hp, ← pDec_code hq, h]

theorem beq_code {p q : Pt} (hp : p.1 < 256) (hq : q.1 < 256) :
    Nat.beq (pCode p) (pCode q) = (p == q) := by
  rw [beq_eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨pCode_inj hp hq, fun h => h ▸ rfl⟩

theorem pIdxOf_code {p : Pt} (hp : p.1 < 256) : pIdxOf (pCode p) = encPt p := by
  obtain ⟨c, t, d⟩ := p
  have ht := t.isLt
  have hd := d.isLt
  change Nat.add (Nat.mul 64 (Nat.land (pCode (c, t, d)) 255))
    (Nat.add (Nat.mul 8 (Nat.land (Nat.shiftRight (pCode (c, t, d)) 8) 7))
      (Nat.land (Nat.shiftRight (pCode (c, t, d)) 11) 7)) = 64 * c + 8 * t.val + d.val
  rw [pCode_c hp, pCode_t hp, pCode_d hp]
  change 64 * c + (8 * t.val + d.val) = 64 * c + 8 * t.val + d.val
  omega

theorem pCodeOf_encPt {p : Pt} (hp : p.1 < 256) : pCodeOf (encPt p) = pCode p := by
  obtain ⟨c, t, d⟩ := p
  have ht := t.isLt
  have hd := d.isLt
  have e1 : Nat.shiftRight (encPt (c, t, d)) 6 = c := by
    rw [shr6]; change (64 * c + 8 * t.val + d.val) / 64 = c; omega
  have e2 : Nat.land (Nat.shiftRight (encPt (c, t, d)) 3) 7 = t.val := by
    rw [land7, shr3]; change ((64 * c + 8 * t.val + d.val) / 8) % 8 = t.val; omega
  have e3 : Nat.land (encPt (c, t, d)) 7 = d.val := by
    rw [land7]; change (64 * c + 8 * t.val + d.val) % 8 = d.val; omega
  change Nat.lor (Nat.shiftRight (encPt (c, t, d)) 6) (Nat.lor
    (Nat.shiftLeft (Nat.land (Nat.shiftRight (encPt (c, t, d)) 3) 7) 8)
    (Nat.shiftLeft (Nat.land (encPt (c, t, d)) 7) 11)) = c ||| t.val <<< 8 ||| d.val <<< 11
  rw [e1, e2, e3, Nat.or_assoc]
  rfl

theorem decPt_encPt {p : Pt} (hp : p.1 < 256) : decPt (encPt p) = p := by
  obtain ⟨c, t, d⟩ := p
  have ht := t.isLt
  have hd := d.isLt
  refine Prod.ext ?_ (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · change (64 * c + 8 * t.val + d.val) / 64 = c; omega
  · change ((64 * c + 8 * t.val + d.val) / 8) % 8 = t.val; omega
  · change (64 * c + 8 * t.val + d.val) % 8 = d.val; omega

theorem encPt_lt {p : Pt} (hp : p.1 < 256) : encPt p < 16384 := by
  have ht := p.2.1.isLt
  have hd := p.2.2.isLt
  change 64 * p.1 + 8 * p.2.1.val + p.2.2.val < 16384
  omega

theorem pCode_decPt (i : Nat) : pCode (decPt i) = pCodeOf i := by
  change i / 64 ||| (i / 8 % 8) <<< 8 ||| (i % 8) <<< 11 =
    Nat.lor (Nat.shiftRight i 6) (Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight i 3) 7) 8)
      (Nat.shiftLeft (Nat.land i 7) 11))
  rw [land7, land7, shr6, shr3, Nat.or_assoc]
  rfl

theorem range_mul_map {α : Type} (f : Nat → α) (b : Nat) : ∀ a : Nat,
    (List.range (b * a)).map f =
      (List.range a).flatMap fun i => (List.range b).map fun j => f (b * i + j)
  | 0 => by simp
  | a + 1 => by
    rw [Nat.mul_succ, List.range_add, List.map_append, List.range_succ, List.flatMap_append,
      range_mul_map f b a, List.map_map, List.flatMap_singleton]
    rfl

theorem all8_eq : all8 = (List.range 8).map fin8Of := by decide +kernel

theorem allPt_block (c : Nat) :
    (all8.flatMap fun t => all8.map fun d => (c, t, d)) =
      (List.range 64).map fun j => decPt (64 * c + j) := by
  have h := range_mul_map (fun j => decPt (64 * c + j)) 8 8
  rw [show (64 : Nat) = 8 * 8 from rfl, h, all8_eq, List.flatMap_map]
  refine List.flatMap_congr fun t ht => ?_
  rw [List.map_map]
  refine List.map_congr_left fun d hd => ?_
  have ht' := List.mem_range.1 ht
  have hd' := List.mem_range.1 hd
  refine Prod.ext ?_ (Prod.ext (Fin.ext ?_) (Fin.ext ?_))
  · change c = (8 * 8 * c + (8 * t + d)) / 64; omega
  · change t % 8 = ((8 * 8 * c + (8 * t + d)) / 8) % 8; omega
  · change d % 8 = (8 * 8 * c + (8 * t + d)) % 8; omega

theorem allPt_eq : allPt = (List.range 16384).map decPt := by
  have h := range_mul_map decPt 64 256
  rw [show (16384 : Nat) = 64 * 256 from rfl, h]
  exact List.flatMap_congr fun c _ => allPt_block c

theorem mem_allPt {p : Pt} : p ∈ allPt ↔ p.1 < 256 := by
  obtain ⟨c, t, d⟩ := p
  simp [allPt, all8]

theorem pAll_eq : pAll = allPt.map pCode := by
  unfold pAll
  rw [pMap_eq, sFilter_eq, List.filter_true, allPt_eq, List.map_map]
  exact List.map_congr_left fun i _ => (pCode_decPt i).symm

theorem pBit_evenD : ∀ d : Fin 8, pBit 51 d.val = evenD d := by decide +kernel

theorem pEvenD_code {p : Pt} (hp : p.1 < 256) : pEvenD (pCode p) = evenD p.2.2 := by
  obtain ⟨c, t, d⟩ := p
  have e : Nat.shiftRight (pCode (c, t, d)) 11 = d.val := by
    rw [shr11, pCode_eq hp]
    have ht := t.isLt
    have hd := d.isLt
    dsimp only
    omega
  change pBit 51 (Nat.shiftRight (pCode (c, t, d)) 11) = evenD d
  rw [e]
  exact pBit_evenD d

theorem pCode_one : pCode onePt = 0 := by decide +kernel

theorem pCode_f : pCode fPt = 256 := by decide +kernel

theorem pCode_a : pCode aPt = 102 := by decide +kernel

theorem pCode_c0 : pCode cPt = 9216 := by decide +kernel

end CFSG.KC.GMS.P117

end
