module

public import Certificates.Data.Kernel.YoshQ.UEF
public import CFSG.Certificates.Kernel.YoshQ.FastSound
import CFSG.Certificates.Kernel.Spor.DistinctSound

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS

theorem strictB_eqU (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem eqN_trans {x y z : Nat} (h1 : eqN 16 5 x y = true) (h2 : eqN 16 5 y z = true) :
    eqN 16 5 x z = true := by
  unfold eqN at *
  rw [Nat.beq_eq] at *
  exact h1.trans h2

theorem eqN_symm {x y : Nat} (h : eqN 16 5 x y = true) : eqN 16 5 y x = true := by
  unfold eqN at *
  rw [Nat.beq_eq] at *
  exact h.symm

theorem hN_of_eqN {P x y : Nat} (h : eqN 16 5 x y = true) : hN P x = hN P y := by
  unfold eqN at h
  unfold hN
  rw [Nat.beq_eq.mp h]

theorem memT_eq {P M : Nat} {T : Nat → Nat} {lE : List Nat} (hT : ueT P M T lE = true) (t : Nat) :
    memT P M T t = memN 16 5 lE t := by
  unfold ueT at hT
  rw [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hT
  obtain ⟨hM, hE⟩ := hT
  unfold memT memN
  rw [strictB_eqU, Co2Shape.hasBit_eq, hM, hmask, testBit_hmaskF]
  simp only [Nat.zero_testBit, Bool.false_or]
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨e, he, hh⟩, hq⟩
    have h1 := hE e he
    rw [hh] at h1
    exact ⟨e, he, eqN_trans (eqN_symm h1) hq⟩
  · rintro ⟨e, he, hq⟩
    have hh : hN P e = hN P t := hN_of_eqN hq
    have h1 := hE e he
    rw [hh] at h1
    exact ⟨⟨e, he, hh⟩, eqN_trans h1 hq⟩

theorem cInI_eq (c a b : Nat) :
    cInI (pidn 16 5) c a (invN 16 5 a) b (invN 16 5 b) = commInN 16 5 c a b := by
  unfold cInI commInN comN
  rw [strictB_eqU]

theorem zip_map_selfU {α β : Type} (l : List α) (f : α → β) :
    l.zip (l.map f) = l.map fun a => (a, f a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem zip_map_self2 {α β γ : Type} (l : List α) (f : α → β) (g : α → γ) :
    l.zip ((l.map f).zip (l.map g)) = l.map fun a => (a, f a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem popN_succ (x n : Nat) : popN x (n + 1) = Nat.land x 1 + popN (Nat.shiftRight x 1) n := rfl

theorem bitsN_cons (b : Bool) (l : List Bool) : bitsN (b :: l) = 2 * bitsN l + cond b 1 0 := rfl

theorem popN_bitsN (l : List Bool) : popN (bitsN l) l.length = (l.filter id).length := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have e1 : Nat.land (2 * bitsN l + cond b 1 0) 1 = cond b 1 0 := by
      change (2 * bitsN l + cond b 1 0) &&& 1 = _
      rw [Nat.and_one_is_mod]
      cases b <;> simp [Nat.add_mod]
    have e2 : Nat.shiftRight (2 * bitsN l + cond b 1 0) 1 = bitsN l := by
      change (2 * bitsN l + cond b 1 0) >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow]
      cases b <;> simp <;> omega
    rw [List.length_cons, popN_succ, bitsN_cons, e1, e2, ih]
    cases b <;> simp [List.filter_cons] <;> omega

theorem bitsN_inj : ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length → bitsN l₁ = bitsN l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hl, h => by
    rw [bitsN_cons, bitsN_cons] at h
    have hb : b₁ = b₂ := by cases b₁ <;> cases b₂ <;> simp at h <;> first | rfl | omega
    subst hb
    have h' : bitsN l₁ = bitsN l₂ := by cases b₁ <;> simp at h <;> omega
    rw [bitsN_inj (by simpa using hl) h']

theorem bne_eq_bitsN {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length) :
    (l₁ != l₂) = !Nat.beq (bitsN l₁) (bitsN l₂) := by
  by_cases h : l₁ = l₂
  · subst h
    simp
  · have h' : bitsN l₁ ≠ bitsN l₂ := fun e => h (bitsN_inj hl e)
    have hb : Nat.beq (bitsN l₁) (bitsN l₂) = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact h' (Nat.eq_of_beq_eq_true e)
    rw [hb]
    simpa using h

theorem ueN_of_F {GE GS lE lS LI YL YI MK : List Nat} {c P M : Nat} {T : Nat → Nat}
    (hT : ueT P M T lE = true) (hI : ueI lE LI YL YI = true) (hY : ueY P M T c lS YL = true)
    (h2 : ue2 P M T GE lS = true) (h5 : ue5 c lE LI = true) (hV : ueV c lE LI YL YI MK = true)
    (h8 : ue8 P M T YL YI MK = true) (hR : ueR GE GS c lE lS = true) :
    ueN GE GS c lE lS = true := by
  have hm := memT_eq hT
  unfold ueI at hI
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hI
  obtain ⟨hLI, hYI⟩ := hI
  subst hLI hYI
  unfold ueY at hY
  simp only [strictB_eqU, hm, beq_iff_eq] at hY
  unfold ueV at hV
  simp only [strictB_eqU, Bool.and_eq_true, beq_iff_eq, zip_map_selfU, List.map_map,
    Function.comp_def, cInI_eq] at hV
  obtain ⟨hMK, hpop⟩ := hV
  subst hMK
  unfold ueR at hR
  simp only [strictB_eqU, Bool.and_eq_true] at hR
  obtain ⟨⟨⟨r1, r3⟩, r4⟩, r6⟩ := hR
  unfold ueN
  rw [hY]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨r1, ?_⟩, r3⟩, r4⟩, ?_⟩, r6⟩, ?_⟩, ?_⟩
  · unfold ue2 at h2
    simp only [strictB_eqU, hm] at h2
    exact h2
  · unfold ue5 at h5
    simp only [strictB_eqU, zip_map_selfU, List.all_map, Function.comp_def, cInI_eq] at h5
    exact h5
  · rw [List.all_eq_true]
    intro y hy
    rw [List.all_map, List.all_eq_true] at hpop
    have h := hpop y hy
    simp only [Function.comp_def, Nat.ble_eq] at h
    have hl : lE.length = (lE.map fun x => commInN 16 5 c x y).length := by simp
    rw [hl, popN_bitsN, List.filter_map, List.length_map] at h
    simpa [Function.comp_def] using h
  · unfold ue8 at h8
    simp only [zip_map_self2, zip_map_selfU, List.all_map, Function.comp_def, hm] at h8
    simp only [List.all_map, Function.comp_def]
    rw [List.all_eq_true] at h8 ⊢
    intro y hy
    have h := h8 y hy
    rw [List.all_eq_true] at h ⊢
    intro y' hy'
    rw [bne_eq_bitsN (by simp)]
    exact h y' hy'

end CFSG.KC.YoshQ

end
