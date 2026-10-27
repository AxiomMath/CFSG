module

public import Certificates.Data.Kernel.OrbRow.Defs
public import Mathlib.Data.Finset.Card
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.OrbRow

open CFSG.KC.Enum

inductive OrbReach (f : ℕ → ℕ → ℕ) (ok : ℕ → Prop) (b : ℕ) : ℕ → Prop
  | root : OrbReach f ok b b
  | step {q j : ℕ} : OrbReach f ok b q → ok j → OrbReach f ok b (f j q)

def lvOk (k lv : ℕ) (j : ℕ) : Prop := j < k ∧ lv.testBit j = true

theorem lvOk_iff {k lv j : ℕ} : lvOk k lv j ↔ j < k ∧ lv.testBit j = true := Iff.rfl

private theorem orbRow_strictB (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem orbRow_bAnd (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem orbRow_bIf (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (if c = true then t else e) := by
  cases c <;> rfl

private theorem orbRow_nIf (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = (if c = true then t else e) := by
  cases c <;> rfl

private theorem orbRow_beq (a b : ℕ) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

private theorem orbRow_blt (a b : ℕ) : Nat.blt a b = true ↔ a < b := by
  rw [Nat.blt_eq]

theorem lvBit_iff (lv j : ℕ) :
    Nat.beq (Nat.land (Nat.shiftRight lv j) 1) 1 = true ↔ lv.testBit j = true := by
  rw [orbRow_beq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]
  change (lv >>> j) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

private theorem orbRow_depD_lt (D p : ℕ) : depD D p < 256 := by
  change Nat.land (Nat.shiftRight D (Nat.mul 8 p)) 255 < 256
  exact Nat.and_lt_two_pow (n := 8) _ (by decide)

private theorem orbRow_rowK {n w m : ℕ} {S : List ℕ} {k lv D b p d r : ℕ}
    (h : rowK n w m S k lv D b p d r = true) :
    d = 255 ∨ (d = 0 ∧ p = b) ∨
      ∃ q j, q < n ∧ lvOk k lv j ∧ depD D q + 1 = d ∧ pg w m (getS S j) q = p := by
  unfold rowK at h
  rw [orbRow_bIf] at h
  by_cases h1 : Nat.beq d 255 = true
  · exact Or.inl ((orbRow_beq _ _).1 h1)
  rw [if_neg h1, orbRow_bIf] at h
  by_cases h2 : Nat.beq d 0 = true
  · rw [if_pos h2] at h
    exact Or.inr (Or.inl ⟨(orbRow_beq _ _).1 h2, (orbRow_beq _ _).1 h⟩)
  rw [if_neg h2, orbRow_strictB, orbRow_strictB] at h
  simp only [orbRow_bAnd, Bool.and_eq_true] at h
  obtain ⟨hq, hj, hb, hd, hp⟩ := h
  exact Or.inr (Or.inr ⟨_, _, (orbRow_blt _ _).1 hq,
    ⟨(orbRow_blt _ _).1 hj, (lvBit_iff _ _).1 hb⟩, (orbRow_beq _ _).1 hd, (orbRow_beq _ _).1 hp⟩)

private theorem orbRow_rowsFrom {n w m : ℕ} {S : List ℕ} {k lv D b cnt : ℕ} :
    ∀ {R : List ℕ} {p c : ℕ}, rowsFrom n w m S k lv D b cnt R p c = true →
      p ≤ n ∧ (∀ p', p ≤ p' → p' < n → ∃ r, rowK n w m S k lv D b p' (depD D p') r = true) ∧
        c + ((Finset.range n).filter (fun x => p ≤ x ∧ depD D x ≠ 255)).card = cnt
  | [], p, c, h => by
    have h' : (Nat.beq p n && Nat.beq c cnt) = true := by
      rw [← orbRow_bAnd]
      exact h
    rw [Bool.and_eq_true, orbRow_beq, orbRow_beq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    refine ⟨le_rfl, fun p' h1 h2 => absurd h2 (by omega), ?_⟩
    have h0 : ((Finset.range p).filter (fun x => p ≤ x ∧ depD D x ≠ 255)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx hx'
      rw [Finset.mem_range] at hx
      exact absurd hx'.1 (by omega)
    rw [h0, Nat.add_zero]
  | r :: R, p, c, h => by
    have h' : strictB (depD D p) (fun d => Bool.rec (motive := fun _ => Bool) false
        (strictB (Nat.succ p) fun p' =>
          strictB (Bool.rec (motive := fun _ => ℕ) (Nat.succ c) c (Nat.beq d 255)) fun c' =>
            rowsFrom n w m S k lv D b cnt R p' c')
        (rowK n w m S k lv D b p d r)) = true := h
    rw [orbRow_strictB, orbRow_bAnd, orbRow_strictB, orbRow_strictB, orbRow_nIf,
      Bool.and_eq_true] at h'
    obtain ⟨hrow, hrest⟩ := h'
    obtain ⟨hpn, hall, hcnt⟩ := orbRow_rowsFrom hrest
    have hp : p < n := by omega
    refine ⟨by omega, fun p' h1 h2 => ?_, ?_⟩
    · rcases Nat.lt_or_ge p p' with hlt | hge
      · exact hall p' hlt h2
      · exact ⟨r, (Nat.le_antisymm hge h1) ▸ hrow⟩
    · rw [← hcnt]
      by_cases hd : depD D p = 255
      · have hb : Nat.beq (depD D p) 255 = true := (orbRow_beq _ _).2 hd
        rw [if_pos hb]
        have hA : (Finset.range n).filter (fun x => p ≤ x ∧ depD D x ≠ 255) =
            (Finset.range n).filter (fun x => Nat.succ p ≤ x ∧ depD D x ≠ 255) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro ⟨h1, h2, h3⟩
            refine ⟨h1, ?_, h3⟩
            rcases Nat.eq_or_lt_of_le h2 with rfl | h2
            · exact absurd hd h3
            · exact h2
          · rintro ⟨h1, h2, h3⟩
            exact ⟨h1, by omega, h3⟩
        rw [hA]
      · have hb : ¬ Nat.beq (depD D p) 255 = true := fun hb => hd ((orbRow_beq _ _).1 hb)
        rw [if_neg hb]
        have hA : (Finset.range n).filter (fun x => p ≤ x ∧ depD D x ≠ 255) =
            insert p ((Finset.range n).filter (fun x => Nat.succ p ≤ x ∧ depD D x ≠ 255)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
          constructor
          · rintro ⟨h1, h2, h3⟩
            rcases Nat.eq_or_lt_of_le h2 with rfl | h2
            · exact Or.inl rfl
            · exact Or.inr ⟨h1, h2, h3⟩
          · rintro (rfl | ⟨h1, h2, h3⟩)
            · exact ⟨hp, le_rfl, hd⟩
            · exact ⟨h1, by omega, h3⟩
        have hnot : p ∉ (Finset.range n).filter (fun x => Nat.succ p ≤ x ∧ depD D x ≠ 255) := by
          intro hx
          rw [Finset.mem_filter] at hx
          exact absurd hx.2.1 (by omega)
        rw [hA, Finset.card_insert_of_notMem hnot]
        omega

theorem rowsK_depth {n w m : ℕ} {S : List ℕ} {k lv D b cnt : ℕ} {R : List ℕ}
    (h : rowsK n w m S k lv D b cnt R = true) :
    ((Finset.range n).filter fun x => depD D x ≠ 255).card = cnt ∧
      ∀ x < n, depD D x ≠ 255 → OrbReach (fun j y => pg w m (getS S j) y) (lvOk k lv) b x := by
  obtain ⟨-, hall, hcnt⟩ := orbRow_rowsFrom h
  refine ⟨?_, fun x hx hd => ?_⟩
  · rw [Nat.zero_add] at hcnt
    have he : ((Finset.range n).filter fun x => depD D x ≠ 255) =
        (Finset.range n).filter (fun x => 0 ≤ x ∧ depD D x ≠ 255) :=
      Finset.filter_congr fun x _ => ⟨fun h => ⟨Nat.zero_le x, h⟩, fun h => h.2⟩
    rw [← hcnt, he]
  have key : ∀ d x, x < n → depD D x = d → d ≠ 255 →
      OrbReach (fun j y => pg w m (getS S j) y) (lvOk k lv) b x := by
    intro d
    induction d with
    | zero =>
      intro x hx hd _
      obtain ⟨r, hr⟩ := hall x (Nat.zero_le x) hx
      rcases orbRow_rowK hr with h1 | ⟨-, rfl⟩ | ⟨q, j, -, -, hq, -⟩
      · omega
      · exact OrbReach.root
      · omega
    | succ d ih =>
      intro x hx hd hne
      obtain ⟨r, hr⟩ := hall x (Nat.zero_le x) hx
      rcases orbRow_rowK hr with h1 | ⟨h0, -⟩ | ⟨q, j, hqn, hj, hq, hp⟩
      · omega
      · omega
      · have hlt := orbRow_depD_lt D x
        rw [← hp]
        exact OrbReach.step (ih q hqn (by omega) (by omega)) hj
  exact key _ x hx rfl hd

theorem rowsK_sound {n w m : ℕ} {S : List ℕ} {k lv D b cnt : ℕ} {R : List ℕ}
    (h : rowsK n w m S k lv D b cnt R = true) :
    ∃ s : Finset ℕ, s.card = cnt ∧
      ∀ x ∈ s, x < n ∧ OrbReach (fun j y => pg w m (getS S j) y) (lvOk k lv) b x := by
  obtain ⟨hc, hr⟩ := rowsK_depth h
  refine ⟨_, hc, fun x hx => ?_⟩
  rw [Finset.mem_filter, Finset.mem_range] at hx
  exact ⟨hx.1, hr x hx.1 hx.2⟩

theorem fixLvK_sound {w m : ℕ} {S : List ℕ} {k lv : ℕ} {B : List ℕ} {i : ℕ}
    (h : fixLvK w m S k lv B i = true) {j : ℕ} (hj : lvOk k lv j) {t : ℕ} (ht : t < i) :
    pg w m (getS S j) (getS B t) = getS B t := by
  have h1 := CFSG.KS.allN_spec h j hj.1
  rw [orbRow_bIf, if_pos ((lvBit_iff _ _).2 hj.2)] at h1
  have h2 := CFSG.KS.allN_spec h1 t ht
  rw [orbRow_strictB] at h2
  exact (orbRow_beq _ _).1 h2

end CFSG.KC.OrbRow

end
