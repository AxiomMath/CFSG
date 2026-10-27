module

public import CFSG.Certificates.Kernel.SporSch.ChainKElem
public import Certificates.Data.Kernel.SporSch.ChainCls
import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Monster.B.Mathieu CFSG.KS.SporSch.ChainCls

theorem cntRK_eq (lo : Nat) (p : Nat → Bool) (len : Nat) :
    cntRK lo len p = (List.range' lo len).countP p := by
  unfold cntRK
  induction len with
  | zero => rfl
  | succ len ih =>
    simp only [Orb.strictN_eq, nIf_eq] at ih ⊢
    rw [ih, List.range'_concat, List.countP_append]
    simp only [Nat.add_eq, List.countP_singleton]
    split <;> simp_all

theorem sum_cntRK (L : Nat) (p : Nat → Bool) (CS : List Nat)
    (hc : ∀ s < CS.length, cntRK (s * L) L p = CS.getD s 0) :
    CS.sum = (List.range' 0 (CS.length * L)).countP p := by
  induction CS using List.reverseRecOn with
  | nil => simp
  | append_singleton CS a ih =>
    have h1 : ∀ s < CS.length, cntRK (s * L) L p = CS.getD s 0 := fun s hs => by
      have := hc s (by simp; omega)
      rwa [List.getD_append _ _ _ _ hs] at this
    have h2 := hc CS.length (by simp)
    rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self] at h2
    simp only [List.getD_cons_zero] at h2
    rw [List.sum_append, ih h1, List.length_append, List.length_singleton, Nat.add_mul,
      Nat.one_mul, ← List.range'_append_1, List.countP_append, Nat.zero_add, ← h2, cntRK_eq]
    simp

theorem countP_range'_of (p : Nat → Bool) {N M : Nat} (hNM : N ≤ M)
    (hp : ∀ j, N ≤ j → p j = false) : (List.range' 0 M).countP p = (List.range N).countP p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  rw [← List.range'_append_1, List.countP_append, List.range_eq_range']
  have : (List.range' (0 + N) d).countP p = 0 := by
    rw [List.countP_eq_zero]
    intro j hj
    have := (List.mem_range'_1.1 hj).1
    simp [hp j (by omega)]
  rw [this, Nat.add_zero]

theorem countP_forall₂ {α β : Type*} {R : α → β → Prop} {f : α → Bool} {q : β → Bool}
    (hf : ∀ a b, R a b → f a = q b) :
    ∀ {l : List α} {m : List β}, List.Forall₂ R l m → l.countP f = m.countP q
  | _, _, .nil => rfl
  | _, _, .cons hab h => by
    rw [List.countP_cons, List.countP_cons, hf _ _ hab, countP_forall₂ hf h]

theorem prep_unique {n w P : Nat} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g)
    (hh : PRep n w P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem prep_of_imageList {n w P : Nat} {g : Equiv.Perm (Fin n)}
    (h : imageList g = (unpack n w P).toList) : PRep n w P g :=
  prep_of_rep (rep_of_imageList h)

theorem beq_pcomp_iff {n w P Q R S : Nat} {a b c d : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hw : 0 < w) (hP : PRep n w P a) (hQ : PRep n w Q b) (hR : PRep n w R c)
    (hS : PRep n w S d) :
    Nat.beq (pcomp n w (mask w) P Q) (pcomp n w (mask w) R S) = decide (a * b = c * d) := by
  have h1 := prep_pcomp hn hP hQ
  have h2 := prep_pcomp hn hR hS
  by_cases e : a * b = c * d
  · rw [decide_eq_true e]
    have : pcomp n w (mask w) P Q = pcomp n w (mask w) R S :=
      PF.eq_of_fields hw (PF.pcomp_shr _ _ hn hw) (PF.pcomp_shr _ _ hn hw) fun i hi => by
        rw [h1 ⟨i, hi⟩, h2 ⟨i, hi⟩, e]
    rw [this]
    exact Nat.beq_refl _
  · rw [decide_eq_false e]
    cases hb : Nat.beq (pcomp n w (mask w) P Q) (pcomp n w (mask w) R S)
    · rfl
    · rw [Nat.eq_of_beq_eq_true hb] at h1
      exact absurd (prep_unique h1 h2) e

theorem commT_eq {n : Nat} {X Y : Table} {x y : Equiv.Perm (Fin n)} (hX : Rep n X x)
    (hY : Rep n Y y) : commT n X Y = decide (x * y = y * x) := by
  rw [commT]
  have := CFSG.Sporadic.SmallOddCore.tblEq_iff_eq (Rep.compT hX hY) (Rep.compT hY hX)
  by_cases e : x * y = y * x
  · rw [decide_eq_true e]
    exact this.2 e
  · rw [decide_eq_false e]
    cases h : tblEq n (compT n X Y) (compT n Y X)
    · rfl
    · exact absurd (this.1 h) e

variable {n w : Nat} {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
include hQ

theorem chainK_h32 : n < 2 ^ 32 := by
  have := hQ.2.2.1
  omega

theorem commGK_eq {gs : List (Equiv.Perm (Fin n))} {G : Nat → Nat}
    (hG : ∀ i < gs.length, PRep n w (G i) (gs.getD i 1)) (j : Nat) :
    commGK n w (mask w) G gs.length (elemK n w (mask w) (n * w) (pidn n w) LR TR k j) =
      gs.all fun g => decide (elemP n w LR TR k j * g = g * elemP n w LR TR k j) := by
  rw [commGK, allN_eq, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  have hw := PF.w_pos hQ.2.1
  have hx := prep_elemK hQ j
  constructor
  · intro h g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have := h i (List.mem_range.2 hi)
    rw [beq_pcomp_iff (chainK_h32 hQ) hw hx (hG i hi) (hG i hi) hx] at this
    rwa [List.getD_eq_getElem _ _ hi] at this
  · intro h i hi
    rw [beq_pcomp_iff (chainK_h32 hQ) hw hx (hG i (List.mem_range.1 hi)) (hG i (List.mem_range.1 hi))
      hx]
    exact h _ (by rw [List.getD_eq_getElem _ _ (List.mem_range.1 hi)]; exact List.getElem_mem _)

variable (hn : 1 ≤ n) (hbs : bv.toList.Nodup)
include hn hbs

theorem countP_allTables {f : Table → Bool} {q : Equiv.Perm (Fin n) → Bool}
    (hf : ∀ X x, Rep n X x → f X = q x) :
    (allTables (certificate hn gens words bv hbs)).countP f =
      (List.range (ordK LR k)).countP fun j => q (elemP n w LR TR k j) := by
  rw [countP_forall₂ hf (forall₂_allTables_elem hQ hn hbs), List.countP_reverse,
    List.countP_map]
  rfl

theorem chainK_commAllCount' {gs : List (Equiv.Perm (Fin n))} {G : Nat → Nat}
    (hG : ∀ i < gs.length, imageList (gs.getD i 1) = (unpack n w (G i)).toList ∧
      CFSG.KS.Prim.canonK n w (mask w) (n * w) (G i) = true)
    {L : Nat} {CS : List Nat} (hL : ordK LR k ≤ CS.length * L)
    (hc : ∀ s < CS.length, commCntK n w (mask w) (n * w) (pidn n w) LR TR k G gs.length
      (ordK LR k) (s * L) L = CS.getD s 0) :
    (allTables (certificate hn gens words bv hbs)).countP (commAll n (gs.map toTable)) =
      CS.sum := by
  have hG' : ∀ i < gs.length, PRep n w (G i) (gs.getD i 1) := fun i hi =>
    prep_of_imageList (hG i hi).1
  set q : Equiv.Perm (Fin n) → Bool := fun x => gs.all fun g => decide (x * g = g * x)
  rw [countP_allTables hQ hn hbs (q := q) fun X x hX => ?_]
  · rw [sum_cntRK L _ CS hc, countP_range'_of _ hL fun j hj => ?_]
    · apply List.countP_congr
      intro j hj
      have hjN := List.mem_range.1 hj
      simp only [bIf_eq, Orb.strictB_eq, Nat.blt_eq, hjN, ↓reduceIte]
      rw [commGK_eq hQ hG' j]
    · simp only [bIf_eq, Nat.blt_eq]
      simp [Nat.not_lt.2 hj]
  · simp only [commAll, List.all_map, q]
    apply List.all_congr rfl
    intro g
    exact commT_eq hX (rep_toTable (chainK_h32 hQ) g)

end Chain

end CFSG.KS.SporSch.MOC

end
