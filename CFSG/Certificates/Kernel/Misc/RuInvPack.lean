module

public import Certificates.Data.Kernel.Misc.RuInv
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.SporSch.LyLoop
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneInputs
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.KC.Misc.RuInv.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.RuSchreier

abbrev G := Equiv.Perm (Fin 4060)

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem mask12 : mask 12 = 4095 := rfl

theorem prep_idP : PRep 4060 12 idP (1 : G) :=
  prep_pidn (by norm_num) (by norm_num)

theorem prep_mulP {p q : Nat} {g h : G} (hp : PRep 4060 12 p g) (hq : PRep 4060 12 q h) :
    PRep 4060 12 (mulP p q) (g * h) :=
  prep_pcomp (by norm_num) hp hq

theorem prep_powP {p : Nat} {g : G} (hp : PRep 4060 12 p g) : ∀ e, PRep 4060 12 (powP p e) (g ^ e)
  | 0 => by rw [pow_zero]; exact prep_idP
  | e + 1 => by
    change PRep 4060 12 (strictN (powP p e) (fun a => mulP p a)) _
    rw [strictN_eq, pow_succ']
    exact prep_mulP hp (prep_powP hp e)

theorem prep_conjP {g gi x : Nat} {a b : G} (hg : PRep 4060 12 g a) (hgi : PRep 4060 12 gi a⁻¹)
    (hx : PRep 4060 12 x b) : PRep 4060 12 (conjP g gi x) (a * b * a⁻¹) :=
  prep_mulP (prep_mulP hg hx) hgi

theorem testBit_foldr_shift (f s : Nat → Nat) (b : Nat) : ∀ l : List Nat,
    (l.foldr (fun i acc => acc ||| (f i <<< s i)) 0).testBit b = true ↔
      ∃ i ∈ l, s i ≤ b ∧ (f i).testBit (b - s i) = true
  | [] => by simp
  | i :: l => by
    rw [List.foldr_cons]
    rw [Nat.testBit_or, Bool.or_eq_true, testBit_foldr_shift f s b l, Nat.testBit_shiftLeft]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (⟨j, hj, h⟩ | ⟨h1, h2⟩)
      · exact ⟨j, Or.inr hj, h⟩
      · exact ⟨i, Or.inl rfl, h1, h2⟩
    · rintro ⟨j, rfl | hj, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨j, hj, h⟩

theorem testBit_lt_4096 {x b : Nat} (hx : x < 4096) (hb : 12 ≤ b) : x.testBit b = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (by
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb))

theorem testBit_fld12 (X o b : Nat) : (fld(X, o, nat_lit 4095)).testBit b = (decide (b < 12) && X.testBit (o + b)) := by
  change ((X >>> o) &&& (2 ^ 12 - 1)).testBit b = _
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Bool.and_comm]

theorem prep_invP {p : Nat} {g : G} (hp : PRep 4060 12 p g) : PRep 4060 12 (invP p) g⁻¹ := by
  intro x
  have hf : invP p = (List.range 4060).foldr
      (fun i acc => acc ||| (i <<< (Nat.mul 12 (apP p i)))) 0 :=
    CFSG.KS.SporSch.LyLoop.foldN_eqP _ _ _
  have hap : ∀ i (hi : i < 4060), apP p i = (g ⟨i, hi⟩ : Nat) := fun i hi => hp ⟨i, hi⟩
  change fld(invP p, Nat.mul 12 x, CFSG.KS.mask 12) = _
  rw [mask12]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fld12]
  by_cases hb : b < 12
  · rw [decide_eq_true hb, Bool.true_and, hf]
    apply Bool.eq_iff_iff.2
    rw [testBit_foldr_shift (fun i => i) (fun i => Nat.mul 12 (apP p i))]
    constructor
    · rintro ⟨i, hi, h1, h2⟩
      rw [List.mem_range] at hi
      rw [hap i hi] at h1 h2
      have hix : (g ⟨i, hi⟩ : Nat) = x := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
        · have : (i : Nat).testBit (12 * x + b - 12 * (g ⟨i, hi⟩ : Nat)) = false :=
            testBit_lt_4096 (by omega) (by
              change 12 * (g ⟨i, hi⟩ : Nat) ≤ 12 * x + b at h1
              omega)
          change (i : Nat).testBit (12 * x + b - 12 * (g ⟨i, hi⟩ : Nat)) = true at h2
          rw [this] at h2
          exact Bool.false_ne_true h2
        · change 12 * (g ⟨i, hi⟩ : Nat) ≤ 12 * x + b at h1
          omega
      have hgi : g⁻¹ x = ⟨i, hi⟩ := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact Fin.ext hix.symm
      rw [hgi]
      change (i : Nat).testBit (12 * x + b - 12 * (g ⟨i, hi⟩ : Nat)) = true at h2
      rw [hix, Nat.add_sub_cancel_left] at h2
      exact h2
    · intro h
      refine ⟨(g⁻¹ x : Nat), List.mem_range.2 (g⁻¹ x).2, ?_, ?_⟩
      · rw [hap _ (g⁻¹ x).2]
        change 12 * (g ⟨(g⁻¹ x : Nat), (g⁻¹ x).2⟩ : Nat) ≤ 12 * x + b
        have : g ⟨(g⁻¹ x : Nat), (g⁻¹ x).2⟩ = x := by simp
        rw [this]
        omega
      · rw [hap _ (g⁻¹ x).2]
        have : g ⟨(g⁻¹ x : Nat), (g⁻¹ x).2⟩ = x := by simp
        change ((g⁻¹ x : Nat)).testBit (12 * x + b - 12 * (g ⟨(g⁻¹ x : Nat), (g⁻¹ x).2⟩ : Nat)) = true
        rw [this, Nat.add_sub_cancel_left]
        exact h
  · rw [decide_eq_false hb, Bool.false_and]
    exact (testBit_lt_4096 (by have := (g⁻¹ x).2; omega) (by omega)).symm

theorem prep_of_permOK {p q : Nat} (h : permOK 4060 12 (mask 12) (4060 * 12) p q = true) :
    ∃ g : G, PRep 4060 12 p g ∧ PRep 4060 12 q g⁻¹ := by
  have hi := isInvA_unpack h
  obtain ⟨h1, h2⟩ := rep_permOfArr hi
  exact ⟨_, prep_of_rep h1, prep_of_rep h2⟩

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem prep_unique {p : Nat} {g h : G} (hg : PRep 4060 12 p g) (hh : PRep 4060 12 p h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

@[expose] def toRow (r : Nat × Nat × Nat × Nat) : SlotRow :=
  if r.1 = 0 then .mu r.2.1 r.2.2.1 r.2.2.2
  else if r.1 = 1 then .iv r.2.1 r.2.2.1 else .pwr r.2.1 r.2.2.1 r.2.2.2

theorem cprogK_rows : cprogK.map toRow = ruCProg := rfl

@[expose] def SlotP (a : List (Nat × Nat)) (s : List (Nat × G)) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ PRep 4060 12 p.2 q.2) a s

theorem slotP_read {a : List (Nat × Nat)} {s : List (Nat × G)} (h : SlotP a s) (k : Nat) :
    PRep 4060 12 (readS a k) (slotRead s k) := by
  induction h with
  | nil => exact prep_idP
  | @cons p q a s hpq _ ih =>
    obtain ⟨k1, x⟩ := p
    obtain ⟨k2, g⟩ := q
    obtain ⟨e, hx⟩ := hpq
    simp only at e hx
    subst e
    change PRep 4060 12 (Bool.rec (motive := fun _ => Nat) (readS a k) x (Nat.beq k1 k)) _
    by_cases hk : k = k1
    · subst hk
      rw [Nat.beq_refl]
      simpa [slotRead, lookup_cons_self] using hx
    · rw [show Nat.beq k1 k = false from beq_false_of_ne (Ne.symm hk)]
      simpa [slotRead, lookup_cons_ne hk] using ih

theorem slotP_step {a : List (Nat × Nat)} {s : List (Nat × G)} (h : SlotP a s)
    (r : Nat × Nat × Nat × Nat) : SlotP (stepS a r) (slotStep s (toRow r)) := by
  obtain ⟨c, i, j, k⟩ := r
  unfold stepS toRow
  simp only
  by_cases h0 : c = 0
  · subst h0
    exact List.Forall₂.cons ⟨rfl, prep_mulP (slotP_read h i) (slotP_read h j)⟩ h
  · rw [show Nat.beq c 0 = false from beq_false_of_ne h0, if_neg h0]
    by_cases h1 : c = 1
    · subst h1
      exact List.Forall₂.cons ⟨rfl, prep_invP (slotP_read h i)⟩ h
    · rw [show Nat.beq c 1 = false from beq_false_of_ne h1, if_neg h1]
      exact List.Forall₂.cons ⟨rfl, prep_powP (slotP_read h j) i⟩ h

theorem prep_slotK (rows : List (Nat × Nat × Nat × Nat)) {t₁ t₂ : Nat} {g₁ g₂ : G}
    (h₁ : PRep 4060 12 t₁ g₁) (h₂ : PRep 4060 12 t₂ g₂) :
    PRep 4060 12 (slotK rows t₁ t₂).1 (slotRun (rows.map toRow) g₁ g₂).1 ∧
      PRep 4060 12 (slotK rows t₁ t₂).2 (slotRun (rows.map toRow) g₁ g₂).2 := by
  have key : ∀ (rows : List (Nat × Nat × Nat × Nat)) (a : List (Nat × Nat)) (s : List (Nat × G)),
      SlotP a s → SlotP (List.rec (motive := fun _ => List (Nat × Nat) → List (Nat × Nat))
        (fun s => s) (fun r _ ih s => ih (stepS s r)) rows a)
        ((rows.map toRow).foldl slotStep s) := by
    intro rows
    induction rows with
    | nil => intro a s h; exact h
    | cons r rows ih =>
      intro a s h
      exact ih _ _ (slotP_step h r)
  have h0 : SlotP [(1, t₁), (2, t₂)] [(1, g₁), (2, g₂)] :=
    List.Forall₂.cons ⟨rfl, h₁⟩ (List.Forall₂.cons ⟨rfl, h₂⟩ List.Forall₂.nil)
  have hS := key rows _ _ h0
  exact ⟨slotP_read hS 1, slotP_read hS 2⟩

@[expose] def letG (γ : Nat → G) (z : Int) : G :=
  if 0 < z then γ (z.toNat - 1) else (γ ((-z).toNat - 1))⁻¹

@[expose] def Letters2 (w : List Int) : Prop := ∀ z ∈ w, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2

theorem prep_wordP {C0 C1 CI0 CI1 : Nat} {x0 x1 : G} (h0 : PRep 4060 12 C0 x0)
    (h1 : PRep 4060 12 C1 x1) (hi0 : PRep 4060 12 CI0 x0⁻¹) (hi1 : PRep 4060 12 CI1 x1⁻¹) :
    ∀ w : List Int, Letters2 w → PRep 4060 12 (wordP (gen2 C0 C1) (gen2 CI0 CI1) w)
      (CFSG.Sporadic.Th.wordG (letG fun l => if l = 0 then x0 else x1) w)
  | [], _ => by
    have e : CFSG.Sporadic.Th.wordG (letG fun l => if l = 0 then x0 else x1) [] = 1 := by
      simp [CFSG.Sporadic.Th.wordG]
    rw [e]
    exact prep_idP
  | z :: w, hw => by
    have ih := prep_wordP h0 h1 hi0 hi1 w (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    change PRep 4060 12 (strictN (wordP (gen2 C0 C1) (gen2 CI0 CI1) w) (fun a => mulP
      (Int.rec (motive := fun _ => Nat) (fun k => gen2 C0 C1 (Nat.sub k 1)) (fun k => gen2 CI0 CI1 k)
        z) a)) _
    rw [strictN_eq]
    have hw' : CFSG.Sporadic.Th.wordG (letG fun l => if l = 0 then x0 else x1) (z :: w) =
        letG (fun l => if l = 0 then x0 else x1) z *
          CFSG.Sporadic.Th.wordG (letG fun l => if l = 0 then x0 else x1) w := by
      simp [CFSG.Sporadic.Th.wordG]
    rw [hw']
    refine prep_mulP ?_ ih
    rcases hw z List.mem_cons_self with rfl | rfl | rfl | rfl
    · exact h0
    · exact hi0
    · exact h1
    · exact hi1

theorem invCand_eq_foldl (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl]
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e]
  exact hi _ (g⁻¹ x).2

theorem isInvA_invCand {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    isInvA n t (invCand n t) = true := by
  unfold isInvA
  rw [allLt_iff]
  intro i hi
  have hr := rep_invCand ht
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ht.apply hi]
  refine ⟨(g ⟨i, hi⟩).2, ?_⟩
  rw [hr.apply (g ⟨i, hi⟩).2]
  simp

theorem slotRunA_rep {n : ℕ} (rows : List SlotRow) {t₁ t₂ : Array ℕ}
    {g₁ g₂ : Equiv.Perm (Fin n)} (h₁ : Rep n t₁ g₁) (h₂ : Rep n t₂ g₂) :
    (slotRunA n rows t₁ t₂).2.2 = true ∧
      Rep n (slotRunA n rows t₁ t₂).1 (slotRun rows g₁ g₂).1 ∧
      Rep n (slotRunA n rows t₁ t₂).2.1 (slotRun rows g₁ g₂).2 := by
  have key : ∀ (rows : List SlotRow) (a : List (ℕ × Array ℕ) × Bool)
      (s : List (ℕ × Equiv.Perm (Fin n))), SlotRep n a.1 s → a.2 = true →
      (rows.foldl (slotStepA n) a).2 = true := by
    intro rows
    induction rows with
    | nil => intro a s _ hf; exact hf
    | cons r rows ih =>
      intro a s h hf
      rw [List.foldl_cons]
      cases r with
      | mu i j k =>
        exact ih _ ((k, slotRead s i * slotRead s j) :: s)
          (List.Forall₂.cons ⟨rfl, rep_compA (slotRep_read h i) (slotRep_read h j)⟩ h) hf
      | iv i j =>
        refine ih _ ((j, (slotRead s i)⁻¹) :: s)
          (List.Forall₂.cons ⟨rfl, rep_invCand (slotRep_read h i)⟩ h) ?_
        simp only [slotStepA, Bool.and_eq_true]
        exact ⟨hf, isInvA_invCand (slotRep_read h i)⟩
      | pwr e i j =>
        exact ih _ ((j, slotRead s i ^ e) :: s)
          (List.Forall₂.cons ⟨rfl, rep_powA (slotRep_read h i) e⟩ h) hf
  have h0 : SlotRep n ([(1, t₁), (2, t₂)] : List (ℕ × Array ℕ)) [(1, g₁), (2, g₂)] :=
    List.Forall₂.cons ⟨rfl, h₁⟩ (List.Forall₂.cons ⟨rfl, h₂⟩ List.Forall₂.nil)
  have hflag : (slotRunA n rows t₁ t₂).2.2 = true := key rows _ _ h0 rfl
  exact ⟨hflag, rep_slotRunA rows h₁ h₂ hflag⟩

theorem rep_tblOfArr {n : ℕ} (hn : n < 2 ^ 32) {t : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ht : Rep n t g) : CFSG.Sporadic.Th.Rep n (CFSG.EvenSporadicStandard.TwoRu.HypOne.tblOfArr t) g := by
  intro i hi
  unfold CFSG.Sporadic.Th.Native.ap CFSG.EvenSporadicStandard.TwoRu.HypOne.tblOfArr
  have hti : t[i]! = (g ⟨i, hi⟩ : Nat) := ht.apply hi
  have hlt : t[i]! < 2 ^ 32 := by rw [hti]; exact lt_trans (g ⟨i, hi⟩).2 hn
  by_cases hs : i < t.size
  · rw [getElem!_pos (t.map UInt32.ofNat) i (by simpa using hs), Array.getElem_map,
      ← getElem!_pos t i hs, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hlt, hti,
      CFSG.Sporadic.Th.idx_of_lt _ hi]
    rfl
  · rw [getElem!_neg (t.map UInt32.ofNat) i (by simpa using hs)]
    have h0 : t[i]! = 0 := getElem!_neg t i hs
    rw [h0] at hti
    rw [CFSG.Sporadic.Th.idx_of_lt _ hi]
    exact hti

end CFSG.KC.Misc.RuInv.P

end
