module

public import Certificates.Data.Kernel.LyI301.Defs
public import CFSG.Sporadic.LyI301.Inputs
public import CFSG.Certificates.Kernel.PermCent.CVSound
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.Certificates.Kernel.LyI301

open Equiv CFSG.Sporadic.LyI301 CFSG.KC.LyI301 CFSG.KC.Enum CFSG.KS CFSG.KS.PF
  CFSG.Certificates.Kernel.PkCV

instance small11 : Small 11 := ⟨by decide⟩

@[expose] noncomputable def ixOf (i : Nat) : Nat := fld(lyIX, Nat.mul (nat_lit 4) i, nat_lit 15)

theorem pt_ix : ∀ y < 11, 3 ≤ y → ixOf y < 8 ∧ lyPt (ixOf y) = y := by decide +kernel

theorem ix_pt : ∀ m < 8, 3 ≤ lyPt m ∧ lyPt m < 11 ∧ ixOf (lyPt m) = m := by decide +kernel

theorem ix_small : ∀ y < 3, ixOf y = 0 := by decide +kernel

theorem s3_complete' : ∀ x0 x1 x2 : Fin 3, x0 ≠ x1 → x0 ≠ x2 → x1 ≠ x2 →
    ∃ a : Fin 6, fld(lyS3 a.val, Nat.mul (nat_lit 4) 0, nat_lit 15) = x0.val ∧
      fld(lyS3 a.val, Nat.mul (nat_lit 4) 1, nat_lit 15) = x1.val ∧
      fld(lyS3 a.val, Nat.mul (nat_lit 4) 2, nat_lit 15) = x2.val := by decide +kernel

theorem s3_complete (x0 : Nat) (h0 : x0 < 3) (x1 : Nat) (h1 : x1 < 3) (x2 : Nat) (h2 : x2 < 3)
    (d01 : x0 ≠ x1) (d02 : x0 ≠ x2) (d12 : x1 ≠ x2) :
    ∃ a < 6, fld(lyS3 a, Nat.mul (nat_lit 4) 0, nat_lit 15) = x0 ∧
      fld(lyS3 a, Nat.mul (nat_lit 4) 1, nat_lit 15) = x1 ∧
      fld(lyS3 a, Nat.mul (nat_lit 4) 2, nat_lit 15) = x2 := by
  obtain ⟨a, ha⟩ := s3_complete' ⟨x0, h0⟩ ⟨x1, h1⟩ ⟨x2, h2⟩ (fun h => d01 (congrArg Fin.val h))
    (fun h => d02 (congrArg Fin.val h)) (fun h => d12 (congrArg Fin.val h))
  exact ⟨a.val, a.2, ha⟩

theorem s4_complete' : ∀ y0 y1 y2 y3 : Fin 4,
    y0 ≠ y1 → y0 ≠ y2 → y0 ≠ y3 → y1 ≠ y2 → y1 ≠ y3 → y2 ≠ y3 →
    ∃ k : Fin 24, fld(lyS4 k.val, Nat.mul (nat_lit 4) 0, nat_lit 15) = y0.val ∧
      fld(lyS4 k.val, Nat.mul (nat_lit 4) 1, nat_lit 15) = y1.val ∧
      fld(lyS4 k.val, Nat.mul (nat_lit 4) 2, nat_lit 15) = y2.val ∧
      fld(lyS4 k.val, Nat.mul (nat_lit 4) 3, nat_lit 15) = y3.val := by decide +kernel

theorem s4_complete (y0 : Nat) (h0 : y0 < 4) (y1 : Nat) (h1 : y1 < 4) (y2 : Nat) (h2 : y2 < 4)
    (y3 : Nat) (h3 : y3 < 4) (d01 : y0 ≠ y1) (d02 : y0 ≠ y2) (d03 : y0 ≠ y3) (d12 : y1 ≠ y2)
    (d13 : y1 ≠ y3) (d23 : y2 ≠ y3) :
    ∃ k < 24, fld(lyS4 k, Nat.mul (nat_lit 4) 0, nat_lit 15) = y0 ∧
      fld(lyS4 k, Nat.mul (nat_lit 4) 1, nat_lit 15) = y1 ∧
      fld(lyS4 k, Nat.mul (nat_lit 4) 2, nat_lit 15) = y2 ∧
      fld(lyS4 k, Nat.mul (nat_lit 4) 3, nat_lit 15) = y3 := by
  obtain ⟨k, hk⟩ := s4_complete' ⟨y0, h0⟩ ⟨y1, h1⟩ ⟨y2, h2⟩ ⟨y3, h3⟩
    (fun h => d01 (congrArg Fin.val h)) (fun h => d02 (congrArg Fin.val h))
    (fun h => d03 (congrArg Fin.val h)) (fun h => d12 (congrArg Fin.val h))
    (fun h => d13 (congrArg Fin.val h)) (fun h => d23 (congrArg Fin.val h))
  exact ⟨k.val, k.2, hk⟩

theorem blt_t {a b : Nat} (h : a < b) : Nat.blt a b = true := cast Nat.blt_eq.symm h

theorem blt_f {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hc : Nat.blt a b
  · rfl
  · exact absurd (cast Nat.blt_eq hc) h

theorem lyImg_lt3 {s e α β i : Nat} (h : i < 3) :
    lyImg s e α β i = fld(s, Nat.mul (nat_lit 4) i, nat_lit 15) := by
  unfold lyImg
  rw [blt_t h]

theorem lyImg_A {s e α β i : Nat} (h : 3 ≤ i) (ht : ixOf i < 4) :
    lyImg s e α β i = lyPt (Nat.add (Nat.mul (nat_lit 4) e)
      fld(α, Nat.mul (nat_lit 4) (ixOf i), nat_lit 15)) := by
  unfold lyImg
  rw [blt_f (by omega : ¬ i < 3), strictN_eqP]
  change Bool.rec (motive := fun _ => Nat) _ _ (Nat.blt (ixOf i) 4) = _
  rw [blt_t ht]
  rfl

theorem lyImg_B {s e α β i : Nat} (h : 3 ≤ i) (ht : ¬ ixOf i < 4) :
    lyImg s e α β i = lyPt (Nat.sub (Nat.add (nat_lit 4)
      fld(β, Nat.mul (nat_lit 4) (Nat.sub (ixOf i) (nat_lit 4)), nat_lit 15))
      (Nat.mul (nat_lit 4) e)) := by
  unfold lyImg
  rw [blt_f (by omega : ¬ i < 3), strictN_eqP]
  change Bool.rec (motive := fun _ => Nat) _ _ (Nat.blt (ixOf i) 4) = _
  rw [blt_f ht]
  rfl

theorem codes_exist (f : Nat → Nat) (hf3 : ∀ i < 3, f i < 3)
    (hf8 : ∀ i < 11, 3 ≤ i → 3 ≤ f i ∧ f i < 11)
    (hinj : ∀ i < 11, ∀ j < 11, f i = f j → i = j) (e : Nat) (he : e < 2)
    (hblk : ∀ i < 11, 3 ≤ i → ixOf (f i) / 4 = (ixOf i / 4 + e) % 2) :
    ∃ a < 6, ∃ ka < 24, ∃ kb < 24, ∀ i < 11, lyImg (lyS3 a) e (lyS4 ka) (lyS4 kb) i = f i := by
  obtain ⟨a, ha, h0, h1, h2⟩ := s3_complete (f 0) (hf3 0 (by omega)) (f 1) (hf3 1 (by omega))
    (f 2) (hf3 2 (by omega)) (fun h => absurd (hinj 0 (by omega) 1 (by omega) h) (by omega))
    (fun h => absurd (hinj 0 (by omega) 2 (by omega) h) (by omega))
    (fun h => absurd (hinj 1 (by omega) 2 (by omega) h) (by omega))
  have hpos : ∀ m < 8, ixOf (f (lyPt m)) = 4 * ((m / 4 + e) % 2) + ixOf (f (lyPt m)) % 4 := by
    intro m hm
    obtain ⟨p3, p11, pix⟩ := ix_pt m hm
    have hb := hblk (lyPt m) p11 p3
    rw [pix] at hb
    omega
  have hinjP : ∀ m < 8, ∀ m' < 8, m / 4 = m' / 4 →
      ixOf (f (lyPt m)) % 4 = ixOf (f (lyPt m')) % 4 → m = m' := by
    intro m hm m' hm' hq hr
    have e1 := hpos m hm
    have e2 := hpos m' hm'
    have hix : ixOf (f (lyPt m)) = ixOf (f (lyPt m')) := by rw [e1, e2, hq, hr]
    obtain ⟨p3, p11, pix⟩ := ix_pt m hm
    obtain ⟨q3, q11, qix⟩ := ix_pt m' hm'
    obtain ⟨-, a1⟩ := pt_ix _ (hf8 _ p11 p3).2 (hf8 _ p11 p3).1
    obtain ⟨-, a2⟩ := pt_ix _ (hf8 _ q11 q3).2 (hf8 _ q11 q3).1
    have hfe : f (lyPt m) = f (lyPt m') := by rw [← a1, ← a2, hix]
    have := hinj _ p11 _ q11 hfe
    rw [← pix, ← qix, this]
  have md : ∀ m, ixOf (f (lyPt m)) % 4 < 4 := fun m => Nat.mod_lt _ (by omega)
  obtain ⟨ka, hka, a0, a1, a2, a3⟩ := s4_complete _ (md 0) _ (md 1) _ (md 2) _ (md 3)
    (fun h => absurd (hinjP 0 (by omega) 1 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 0 (by omega) 2 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 0 (by omega) 3 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 1 (by omega) 2 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 1 (by omega) 3 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 2 (by omega) 3 (by omega) rfl h) (by omega))
  obtain ⟨kb, hkb, b0, b1, b2, b3⟩ := s4_complete _ (md 4) _ (md 5) _ (md 6) _ (md 7)
    (fun h => absurd (hinjP 4 (by omega) 5 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 4 (by omega) 6 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 4 (by omega) 7 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 5 (by omega) 6 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 5 (by omega) 7 (by omega) rfl h) (by omega))
    (fun h => absurd (hinjP 6 (by omega) 7 (by omega) rfl h) (by omega))
  have hA : ∀ t < 4, fld(lyS4 ka, Nat.mul (nat_lit 4) t, nat_lit 15) =
      ixOf (f (lyPt t)) % 4 := by
    intro t ht
    interval_cases t
    · exact a0
    · exact a1
    · exact a2
    · exact a3
  have hB : ∀ t < 4, fld(lyS4 kb, Nat.mul (nat_lit 4) t, nat_lit 15) =
      ixOf (f (lyPt (t + 4))) % 4 := by
    intro t ht
    interval_cases t
    · exact b0
    · exact b1
    · exact b2
    · exact b3
  refine ⟨a, ha, ka, hka, kb, hkb, fun i hi => ?_⟩
  by_cases h3 : i < 3
  · rw [lyImg_lt3 h3]
    interval_cases i
    · exact h0
    · exact h1
    · exact h2
  · have h3' : 3 ≤ i := by omega
    obtain ⟨i8, ipt⟩ := pt_ix i hi h3'
    obtain ⟨f3, f11⟩ := hf8 i hi h3'
    obtain ⟨-, fpt⟩ := pt_ix (f i) f11 f3
    have hp := hpos (ixOf i) i8
    rw [ipt] at hp
    by_cases ht : ixOf i < 4
    · rw [lyImg_A h3' ht]
      change lyPt (4 * e + fld(lyS4 ka, Nat.mul (nat_lit 4) (ixOf i), nat_lit 15)) = f i
      rw [hA _ ht, ipt]
      have : (ixOf i / 4 + e) % 2 = e := by
        have : ixOf i / 4 = 0 := by omega
        omega
      rw [this] at hp
      rw [← hp, fpt]
    · rw [lyImg_B h3' ht]
      change lyPt (4 + fld(lyS4 kb, Nat.mul (nat_lit 4) (ixOf i - 4), nat_lit 15) - 4 * e) = f i
      rw [hB _ (by omega), Nat.sub_add_cancel (by omega), ipt]
      have : (ixOf i / 4 + e) % 2 = 1 - e := by
        have : ixOf i / 4 = 1 := by omega
        omega
      rw [this] at hp
      have hx : 4 + ixOf (f i) % 4 - 4 * e = ixOf (f i) := by omega
      rw [hx, fpt]

@[expose] def vEl (k : Fin 16) : Perm (Fin 11) :=
  lyU 0 ^ (k.val % 2) * lyU 1 ^ (k.val / 2 % 2) * lyU 2 ^ (k.val / 4 % 2) * lyU 3 ^ (k.val / 8)

theorem mem_lyV_iff {w : Perm (Fin 11)} : w ∈ lyV ↔ ∃ k, vEl k = w := by
  simp only [lyV, List.mem_map, List.mem_finRange, true_and]
  rfl

theorem vEl_fix : ∀ k : Fin 16, ∀ x : Fin 11,
    (3 ≤ x.val → ixOf (vEl k x).val / 4 = ixOf x.val / 4) := by decide +kernel

theorem lyU_edges : lyU 0 3 = 4 ∧ lyU 1 3 = 5 ∧ lyU 0 5 = 9 ∧ lyU 0 6 = 7 ∧ lyU 2 6 = 8 ∧
    lyU 0 8 = 10 := by decide +kernel

theorem ix_blk : ∀ y : Fin 11, 3 ≤ y.val → ixOf y.val / 4 < 2 := by decide +kernel

theorem ixA : ixOf 3 / 4 = 0 ∧ ixOf 4 / 4 = 0 ∧ ixOf 5 / 4 = 0 ∧ ixOf 9 / 4 = 0 := by decide +kernel

theorem ixB : ixOf 6 / 4 = 1 ∧ ixOf 7 / 4 = 1 ∧ ixOf 8 / 4 = 1 ∧ ixOf 10 / 4 = 1 := by
  decide +kernel

theorem cases8 {P : Fin 11 → Prop} (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7)
    (h8 : P 8) (h9 : P 9) (h10 : P 10) : ∀ x : Fin 11, 3 ≤ x.val → P x := by
  intro x hx
  fin_cases x
  · exact absurd hx (by decide)
  · exact absurd hx (by decide)
  · exact absurd hx (by decide)
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10

theorem block (g : Perm (Fin 11)) (hS : ∀ x, ((g x).val < 3 ↔ x.val < 3))
    (hN : ∀ i, g * lyU i * g⁻¹ ∈ lyV) : ∀ x : Fin 11, 3 ≤ x.val →
      ixOf (g x).val / 4 = (ixOf x.val / 4 + ixOf (g 3).val / 4) % 2 := by
  have hge : ∀ x : Fin 11, 3 ≤ x.val → 3 ≤ (g x).val := fun x hx => by
    have := hS x
    omega
  have hstep : ∀ i x, 3 ≤ x.val → ixOf (g (lyU i x)).val / 4 = ixOf (g x).val / 4 := by
    intro i x hx
    obtain ⟨k, hk⟩ := mem_lyV_iff.1 (hN i)
    have e : g (lyU i x) = (g * lyU i * g⁻¹) (g x) := by simp
    rw [e, ← hk]
    exact vEl_fix k (g x) (hge x hx)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := lyU_edges
  have h4 : ixOf (g 4).val / 4 = ixOf (g 3).val / 4 := by
    rw [← e1]
    exact hstep 0 3 (by decide)
  have h5 : ixOf (g 5).val / 4 = ixOf (g 3).val / 4 := by
    rw [← e2]
    exact hstep 1 3 (by decide)
  have h9 : ixOf (g 9).val / 4 = ixOf (g 3).val / 4 := by
    rw [← e3, hstep 0 5 (by decide), h5]
  have h7 : ixOf (g 7).val / 4 = ixOf (g 6).val / 4 := by
    rw [← e4]
    exact hstep 0 6 (by decide)
  have h8 : ixOf (g 8).val / 4 = ixOf (g 6).val / 4 := by
    rw [← e5]
    exact hstep 2 6 (by decide)
  have h10 : ixOf (g 10).val / 4 = ixOf (g 6).val / 4 := by
    rw [← e6, hstep 0 8 (by decide), h8]
  have b3 := ix_blk (g 3) (hge 3 (by decide))
  have b6 := ix_blk (g 6) (hge 6 (by decide))
  have hne : ixOf (g 6).val / 4 ≠ ixOf (g 3).val / 4 := by
    intro heq
    have hall : ∀ x : Fin 11, 3 ≤ x.val → ixOf (g x).val / 4 = ixOf (g 3).val / 4 :=
      cases8 rfl h4 h5 heq (h7.trans heq) (h8.trans heq) h9 (h10.trans heq)
    obtain ⟨a3, -, -, -⟩ := ixA
    obtain ⟨a6, -, -, -⟩ := ixB
    have hq : ∃ q : Fin 11, 3 ≤ q.val ∧ ixOf q.val / 4 ≠ ixOf (g 3).val / 4 := by
      rcases Nat.lt_or_ge (ixOf (g 3).val / 4) 1 with h | h
      · exact ⟨6, by decide, by change ixOf 6 / 4 ≠ _; omega⟩
      · exact ⟨3, by decide, by change ixOf 3 / 4 ≠ _; omega⟩
    obtain ⟨q, hq3, hqb⟩ := hq
    have hgq : g (g⁻¹ q) = q := by simp
    have hy : 3 ≤ (g⁻¹ q).val := by
      have := hS (g⁻¹ q)
      rw [hgq] at this
      omega
    have := hall (g⁻¹ q) hy
    rw [hgq] at this
    exact hqb this
  obtain ⟨a3, a4, a5, a9⟩ := ixA
  obtain ⟨c6, c7, c8, c10⟩ := ixB
  refine cases8 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · change _ = (ixOf 3 / 4 + _) % 2
    omega
  · change _ = (ixOf 4 / 4 + _) % 2
    omega
  · change _ = (ixOf 5 / 4 + _) % 2
    omega
  · change _ = (ixOf 6 / 4 + _) % 2
    omega
  · change _ = (ixOf 7 / 4 + _) % 2
    omega
  · change _ = (ixOf 8 / 4 + _) % 2
    omega
  · change _ = (ixOf 9 / 4 + _) % 2
    omega
  · change _ = (ixOf 10 / 4 + _) % 2
    omega

theorem lySplit_small (σ₃ : Perm {i : Fin 11 // i.val < 3}) (σ₈ : Perm {i : Fin 11 // ¬ i.val < 3})
    (x : Fin 11) : (lySplit σ₃ σ₈ x).val < 3 ↔ x.val < 3 := by
  unfold lySplit
  rw [Perm.subtypeCongr.apply]
  split_ifs with h
  · exact iff_of_true (σ₃ ⟨x, h⟩).2 h
  · exact iff_of_false (σ₈ ⟨x, h⟩).2 h

@[expose] noncomputable def cls (x : Fin 11) : Finset (Fin 11) :=
  Finset.univ.filter fun y => (y.val < 3 ↔ x.val < 3) ∧ ixOf y.val / 4 = ixOf x.val / 4

theorem cls_card : ∀ x : Fin 11, (cls x).card ≤ 4 := by decide +kernel

theorem pow_24 (g : Perm (Fin 11)) (hS : ∀ x, ((g x).val < 3 ↔ x.val < 3))
    (hN : ∀ i, g * lyU i * g⁻¹ ∈ lyV) : g ^ 24 = 1 := by
  have hb := block g hS hN
  set h := g * g with hh
  have hcl : ∀ x y, y ∈ cls x → h y ∈ cls x := by
    intro x y hy
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨hy1, hy2⟩ := hy
    have s1 : (h y).val < 3 ↔ y.val < 3 := by
      rw [hh, Perm.mul_apply, hS, hS]
    refine ⟨s1.trans hy1, ?_⟩
    rw [← hy2]
    by_cases y3 : y.val < 3
    · rw [ix_small _ (s1.2 y3), ix_small _ y3]
    · have y3' : 3 ≤ y.val := by omega
      have gy : 3 ≤ (g y).val := by
        have := hS y
        omega
      rw [hh, Perm.mul_apply, hb (g y) gy, hb y y3']
      have := ix_blk y y3'
      have := ix_blk (g 3) (by have := hS 3; change 3 ≤ (g 3).val; simp at this; omega)
      omega
  have hpow : ∀ x k, (h ^ k) x ∈ cls x := by
    intro x k
    induction k with
    | zero => simp [cls]
    | succ k ih =>
      rw [pow_succ', Perm.mul_apply]
      exact hcl x _ ih
  have h12 : ∀ x, (h ^ 12) x = x := by
    intro x
    obtain ⟨i, hi, j, hj, hij, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range 5) (t := cls x) (f := fun k => (h ^ k) x)
      (by rw [Finset.card_range]; have := cls_card x; omega)
      (fun k _ => hpow x k)
    simp only [Finset.mem_range] at hi hj
    have key : ∀ i j, i < j → j < 5 → (h ^ i) x = (h ^ j) x → (h ^ 12) x = x := by
      intro i j hlt hj5 hij
      have hd : (h ^ (j - i)) x = x := by
        apply (h ^ i).injective
        rw [← Perm.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le, hij]
      have hdx : ∀ m, ((h ^ (j - i)) ^ m) x = x := fun m =>
        Perm.pow_apply_eq_self_of_apply_eq_self hd m
      obtain ⟨m, hm⟩ : ∃ m, 12 = (j - i) * m := by
        have : j - i = 1 ∨ j - i = 2 ∨ j - i = 3 ∨ j - i = 4 := by omega
        rcases this with hd1 | hd1 | hd1 | hd1
        · exact ⟨12, by rw [hd1]⟩
        · exact ⟨6, by rw [hd1]⟩
        · exact ⟨4, by rw [hd1]⟩
        · exact ⟨3, by rw [hd1]⟩
      rw [hm, pow_mul]
      exact hdx m
    rcases Nat.lt_or_gt_of_ne hij with hl | hl
    · exact key i j hl hj he
    · exact key j i hl hi he.symm
  have : g ^ 24 = h ^ 12 := by
    rw [hh, ← sq, ← pow_mul]
  rw [this]
  exact Equiv.ext h12

theorem wC11 : wC 11 = 4 := by decide

theorem mul_val (a b : CV 11) : (a * b).1 = lyMul a.1 b.1 := by
  change pcomp 11 (wC 11) (mask (wC 11)) a.1 b.1 = _
  rw [wC11]
  rfl

theorem inv_val (a : CV 11) : (a⁻¹).1 = pinvS (nat_lit 11) (nat_lit 4) (nat_lit 15) a.1 := by
  change pinvS 11 (wC 11) (mask (wC 11)) a.1 = _
  rw [wC11]
  rfl

theorem cOf_mul (a b : Perm (Fin 11)) : cOf (a * b) = cOf a * cOf b :=
  ev_injective (by rw [ev_mul, ev_cOf, ev_cOf, ev_cOf])

theorem cOf_inv (a : Perm (Fin 11)) : cOf a⁻¹ = (cOf a)⁻¹ :=
  ev_injective (by rw [ev_inv, ev_cOf, ev_cOf])

theorem vt_to : ∀ k : Fin 16, ∃ j : Fin 16, (cOf (vEl k)).1 = lyVk j.val := by decide +kernel

theorem vt_of : ∀ j : Fin 16, ∃ k : Fin 16, (cOf (vEl k)).1 = lyVk j.val := by decide +kernel

theorem conj_eq : (cOf lyX3).1 = lyB0 ∧ (cOf lyX3⁻¹).1 = lyB0I ∧ (cOf (lyX1 * lyX2)).1 = lyB1 ∧
    (cOf (lyX1 * lyX2)⁻¹).1 = lyB1I := by decide +kernel

theorem mem_lyV (w : Perm (Fin 11)) : w ∈ lyV ↔ ∃ k < 16, (cOf w).1 = lyVk k := by
  rw [mem_lyV_iff]
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨j, hj⟩ := vt_to k
    exact ⟨j.val, j.2, hj⟩
  · rintro ⟨j, hj, he⟩
    obtain ⟨k, hk⟩ := vt_of ⟨j, hj⟩
    refine ⟨k, ?_⟩
    have : cOf (vEl k) = cOf w := Subtype.ext (hk.trans he.symm)
    rw [← ev_cOf (vEl _), this, ev_cOf]

theorem notV_true {w : Perm (Fin 11)} (h : lyNotV (cOf w).1 = true) : w ∉ lyV := by
  rw [mem_lyV]
  rintro ⟨k, hk, he⟩
  have := allN_spec h k hk
  rw [he, Nat.beq_refl] at this
  exact Bool.noConfusion this

theorem notV_of {w : Perm (Fin 11)} (h : w ∉ lyV) : lyNotV (cOf w).1 = true := by
  apply CFSG.KS.PackFld.allN_of_forall
  intro k hk
  cases hb : Nat.beq (cOf w).1 (lyVk k)
  · rfl
  · exact absurd ((mem_lyV w).2 ⟨k, hk, Nat.eq_of_beq_eq_true hb⟩) h

theorem lyMk_eq {s e α β : Nat} (g : Perm (Fin 11))
    (h : ∀ i (hi : i < 11), lyImg s e α β i = (g ⟨i, hi⟩).val) : lyMk s e α β = (cOf g).1 := by
  have hf : ∀ x < 11, lyImg s e α β x < 2 ^ 4 := fun x hx => by
    rw [h x hx]
    have := (g ⟨x, hx⟩).2
    omega
  have hev : ∀ i (hi : i < 11), pg 4 (mask 4) (cOf g).1 i = (g ⟨i, hi⟩).val := by
    intro i hi
    have := ev_apply (cOf g) ⟨i, hi⟩
    rw [ev_cOf] at this
    rw [this]
    change pg 4 (mask 4) (cOf g).1 i = pg (wC 11) (mask (wC 11)) (cOf g).1 i
    rw [wC11]
  refine eq_of_fields (n := 11) (w := 4) (by decide) (pmk_shr (by decide) (by decide) hf) ?_ ?_
  · have := (cOf g).2.1
    rw [wC11] at this
    exact this
  · intro i hi
    rw [hev i hi]
    change pg 4 (mask 4) (pmk 11 4 (lyImg s e α β)) i = _
    rw [pg_pmk (by decide) hf hi, h i hi]

theorem inv_facts (hrow : ∀ r < 12, lyRow r = true) (g : Perm (Fin 11))
    (hS : ∀ x, ((g x).val < 3 ↔ x.val < 3)) (hN : ∀ i, g * lyU i * g⁻¹ ∈ lyV) (hg : g ∉ lyV)
    (hsq : g * g ∈ lyV) : ∃ b ∈ lyConj, g * (b * g * b⁻¹) * g⁻¹ * (b * g * b⁻¹)⁻¹ ∉ lyV := by
  have hb := block g hS hN
  set e := ixOf (g 3).val / 4 with he
  have he2 : e < 2 := ix_blk (g 3) (by have := hS 3; change 3 ≤ (g 3).val; simp at this; omega)
  set f : Nat → Nat := fun i => if hi : i < 11 then (g ⟨i, hi⟩).val else 0 with hf
  have fv : ∀ i (hi : i < 11), f i = (g ⟨i, hi⟩).val := fun i hi => by rw [hf]; simp [hi]
  obtain ⟨a, ha, ka, hka, kb, hkb, hcode⟩ := codes_exist f
    (fun i hi => by rw [fv i (by omega)]; exact (hS _).2 hi)
    (fun i hi h3 => by
      rw [fv i hi]
      have := hS ⟨i, hi⟩
      exact ⟨by simp at this; omega, (g _).2⟩)
    (fun i hi j hj hij => by
      rw [fv i hi, fv j hj] at hij
      exact congrArg Fin.val (g.injective (Fin.ext hij)))
    e he2 (fun i hi h3 => by rw [fv i hi]; exact hb ⟨i, hi⟩ h3)
  have hx : lyMk (lyS3 a) e (lyS4 ka) (lyS4 kb) = (cOf g).1 :=
    lyMk_eq g (fun i hi => (hcode i hi).trans (fv i hi))
  have hr := hrow (2 * a + e) (by omega)
  have r1 : Nat.shiftRight (2 * a + e) (nat_lit 1) = a := by
    change (2 * a + e) >>> 1 = a
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have r2 : Nat.land (2 * a + e) (nat_lit 1) = e := by
    change (2 * a + e) &&& 1 = e
    rw [Nat.and_one_is_mod]
    omega
  unfold lyRow at hr
  rw [r1, strictB_eqP, r2, strictB_eqP] at hr
  have h1 := allN_spec hr ka hka
  rw [strictB_eqP] at h1
  have hel := allN_spec h1 kb hkb
  rw [hx] at hel
  have hsqF : lyNotV (lyMul (cOf g).1 (cOf g).1) = false := by
    rw [← mul_val, ← cOf_mul]
    cases hc : lyNotV (cOf (g * g)).1
    · rfl
    · exact absurd hsq (notV_true hc)
  have hgT := notV_of hg
  unfold lyEl at hel
  rw [hsqF, hgT, strictB_eqP, ← inv_val] at hel
  obtain ⟨c0, c0i, c1, c1i⟩ := conj_eq
  have hcomm : ∀ b : Perm (Fin 11), lyComm (cOf g).1 ((cOf g)⁻¹).1 (cOf b).1 (cOf b⁻¹).1 = true →
      g * (b * g * b⁻¹) * g⁻¹ * (b * g * b⁻¹)⁻¹ ∉ lyV := by
    intro b hc
    unfold lyComm at hc
    rw [strictB_eqP, strictB_eqP] at hc
    apply notV_true
    have e1 : g * (b * g * b⁻¹) * g⁻¹ * (b * g * b⁻¹)⁻¹ =
        g * (b * g * b⁻¹) * g⁻¹ * (b * g⁻¹ * b⁻¹) := by group
    rw [e1, cOf_mul, cOf_mul, cOf_mul, cOf_mul, cOf_mul, cOf_mul, cOf_mul, cOf_inv g]
    simp only [mul_val]
    exact hc
  cases h0 : lyComm (cOf g).1 ((cOf g)⁻¹).1 lyB0 lyB0I
  · rw [h0] at hel
    refine ⟨lyX1 * lyX2, by simp [lyConj], hcomm _ ?_⟩
    rw [c1, c1i]
    exact hel
  · refine ⟨lyX3, by simp [lyConj], hcomm _ ?_⟩
    rw [c0, c0i]
    exact h0

end CFSG.Certificates.Kernel.LyI301

end
