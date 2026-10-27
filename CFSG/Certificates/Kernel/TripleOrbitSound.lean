module

public import Certificates.Data.Kernel.TripleOrbit
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.KC.Triple

open CFSG.KLie.CT Equiv

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

private theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

private theorem bRec_eq (b t e : Bool) :
    (Bool.rec (motive := fun _ => Bool) e t b : Bool) = if b then t else e := by cases b <;> rfl

private theorem nRec_eq (b : Bool) (t e : Nat) :
    (Bool.rec (motive := fun _ => Nat) e t b : Nat) = if b then t else e := by cases b <;> rfl

private theorem fget_eq (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem fget0 (c : Nat) : fget c 0 5 = c % 32 := by
  rw [fget_eq]
  simp

private theorem fget1 (c : Nat) : fget c 1 5 = c / 32 % 32 := by
  rw [fget_eq]
  simp

private theorem fget2 (c : Nat) : fget c 2 5 = c / 1024 % 32 := by
  rw [fget_eq]
  simp

private theorem code_lt (r : Nat) : code r < 32768 := by
  have h : r &&& 32767 ≤ 32767 := Nat.and_le_right
  change r &&& 32767 < 32768
  omega

private theorem imgC_eq (G c : Nat) : imgC G c =
    fget G (fget c 0 5) 5 + (32 * fget G (fget c 1 5) 5 + 1024 * fget G (fget c 2 5) 5) := rfl

private theorem recAnd_spec (g : Nat → Bool) : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (g i)) n : Bool) = true →
    ∀ i < n, g i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    change (Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun i ih => Bool.rec (motive := fun _ => Bool) false ih (g i)) n) (g n) : Bool) = true at h
    cases hgn : g n with
    | false =>
      rw [hgn] at h
      exact absurd h Bool.false_ne_true
    | true =>
      rw [hgn] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact recAnd_spec g n h i hlt
      · exact hgn

private theorem allBelow_spec {m hi : Nat} {f : Nat → Bool}
    (h : CFSG.KC.Loop.allBelow m hi f = true) (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := recAnd_spec (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      Bool.rec (motive := fun _ => Bool) false ih2
        ((fun i => Bool.rec (motive := fun _ => Bool) true (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l))) 64) hi h (i / 64) (by omega)
  have h2 := recAnd_spec (fun l => (fun i => Bool.rec (motive := fun _ => Bool) true (f i)
      (Nat.blt i m)) (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64)
    (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  dsimp only at h2
  rw [e, Nat.blt_eq.mpr him] at h2
  exact h2

private theorem injC_spec {c : Nat} (h : injC c = true) :
    fget c 0 5 < 22 ∧ fget c 1 5 < 22 ∧ fget c 2 5 < 22 ∧ fget c 0 5 ≠ fget c 1 5 ∧
      fget c 0 5 ≠ fget c 2 5 ∧ fget c 1 5 ≠ fget c 2 5 := by
  simp only [injC, andB_eq, notB_eq, Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at h
  obtain ⟨⟨h0, h1, h2⟩, h01, h02, h12⟩ := h
  exact ⟨h0, h1, h2, Nat.ne_of_beq_eq_false h01, Nat.ne_of_beq_eq_false h02,
    Nat.ne_of_beq_eq_false h12⟩

private theorem nodeOK_spec {G0 G1 : Nat} {T : Nat → Nat} {N i : Nat}
    (h : nodeOK G0 G1 T N i = true) :
    injC (code (rec T i)) = true ∧
      (i + 1 < N → code (rec T i) < code (rec T (i + 1))) ∧
      (rec T i >>> 30 = 0 → code (rec T i) = 2080) ∧
      (rec T i >>> 30 ≠ 0 → fget (rec T i >>> 15) 0 14 < N ∧
        rec T (fget (rec T i >>> 15) 0 14) >>> 30 = rec T i >>> 30 - 1 ∧
        imgC (if Nat.beq (fget (rec T i) 29 1) 0 = true then G0 else G1)
          (code (rec T (fget (rec T i >>> 15) 0 14))) = code (rec T i)) := by
  simp only [nodeOK, andB_eq, bRec_eq, nRec_eq, Bool.and_eq_true] at h
  obtain ⟨hinj, hnext, hpar⟩ := h
  refine ⟨hinj, fun hi => ?_, fun hd => ?_, fun hd => ?_⟩
  · split at hnext
    · exact Nat.blt_eq.mp hnext
    · exact absurd (Nat.blt_eq.mpr hi) ‹_›
  · split at hpar
    · exact Nat.beq_eq.mp hpar
    · exact absurd (Nat.beq_eq.mpr hd) ‹_›
  · split at hpar
    · exact absurd (Nat.beq_eq.mp ‹_›) hd
    · simp only [Bool.and_eq_true] at hpar
      exact ⟨Nat.blt_eq.mp hpar.1, Nat.beq_eq.mp hpar.2.1, Nat.beq_eq.mp hpar.2.2⟩

private theorem exists_emb {x y z : Nat} (hx : x < 22) (hy : y < 22) (hz : z < 22)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ f : Fin 3 ↪ Fin 22, (f 0).val = x ∧ (f 1).val = y ∧ (f 2).val = z := by
  refine ⟨⟨![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩], fun u v huv => ?_⟩, rfl, rfl, rfl⟩
  have hv := congrArg Fin.val huv
  fin_cases u <;> fin_cases v <;> simp_all

theorem tripleOrbit_sound {G0 G1 : Nat} {T : Nat → Nat} {a b : Perm (Fin 22)}
    (ha : ∀ x : Fin 22, (a x).val = fget G0 x.val 5) (hb : ∀ x : Fin 22, (b x).val = fget G1 x.val 5)
    (hk : treeOK G0 G1 T 9240 145 = true) :
    ∀ e : Fin 3 ↪ Fin 22, ∃ g ∈ Subgroup.closure ({a, b} : Set (Perm (Fin 22))),
      ∀ i, g (![0, 1, 2] i) = e i := by
  classical
  have hall : CFSG.KC.Loop.allBelow 9240 145 (nodeOK G0 G1 T 9240) = true := by
    have e : treeOK G0 G1 T 9240 145 = (Nat.ble 9240 (Nat.mul 64 145) &&
        CFSG.KC.Loop.allBelow 9240 145 (nodeOK G0 G1 T 9240)) := andB_eq _ _
    rw [e, Bool.and_eq_true] at hk
    exact hk.2
  have hnode : ∀ i < 9240, nodeOK G0 G1 T 9240 i = true := allBelow_spec hall (by omega)
  have hmono : ∀ j, j < 9240 → ∀ i < j, code (rec T i) < code (rec T j) := by
    intro j
    induction j with
    | zero => exact fun _ i hi => absurd hi (Nat.not_lt_zero i)
    | succ j ih =>
      intro hj i hi
      have hstep := (nodeOK_spec (hnode j (by omega))).2.1 hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact (ih (by omega) i hlt).trans hstep
      · exact hstep
  have horb : ∀ n, ∀ i < 9240, rec T i >>> 30 = n →
      ∃ g ∈ Subgroup.closure ({a, b} : Set (Perm (Fin 22))),
        (g 0).val = fget (code (rec T i)) 0 5 ∧ (g 1).val = fget (code (rec T i)) 1 5 ∧
          (g 2).val = fget (code (rec T i)) 2 5 := by
    intro n
    induction n with
    | zero =>
      intro i hi hd
      have h2080 := (nodeOK_spec (hnode i hi)).2.2.1 hd
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [h2080, fget0, fget1, fget2]
      exact ⟨rfl, rfl, rfl⟩
    | succ n ih =>
      intro i hi hd
      obtain ⟨hp, hdp, himg⟩ := (nodeOK_spec (hnode i hi)).2.2.2 (by omega)
      obtain ⟨g, hg, hg0, hg1, hg2⟩ := ih _ hp (by omega)
      have step : ∀ (x : Perm (Fin 22)) (G : Nat),
          x ∈ Subgroup.closure ({a, b} : Set (Perm (Fin 22))) →
          (∀ y : Fin 22, (x y).val = fget G y.val 5) →
          imgC G (code (rec T (fget (rec T i >>> 15) 0 14))) = code (rec T i) →
          ∃ g ∈ Subgroup.closure ({a, b} : Set (Perm (Fin 22))),
            (g 0).val = fget (code (rec T i)) 0 5 ∧ (g 1).val = fget (code (rec T i)) 1 5 ∧
              (g 2).val = fget (code (rec T i)) 2 5 := by
        intro x G hx hxG himg'
        refine ⟨x * g, Subgroup.mul_mem _ hx hg, ?_⟩
        have hci : code (rec T i) =
            (x (g 0)).val + 32 * (x (g 1)).val + 1024 * (x (g 2)).val := by
          rw [← himg', imgC_eq, hxG, hxG, hxG, hg0, hg1, hg2]
          omega
        have h0 := (x (g 0)).isLt
        have h1 := (x (g 1)).isLt
        have h2 := (x (g 2)).isLt
        simp only [Perm.mul_apply, fget0, fget1, fget2]
        omega
      by_cases hgen : Nat.beq (fget (rec T i) 29 1) 0 = true
      · rw [if_pos hgen] at himg
        exact step a G0 (Subgroup.subset_closure (Set.mem_insert a {b})) ha himg
      · rw [if_neg hgen] at himg
        exact step b G1 (Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)) hb himg
  have hcard : ((Finset.range 9240).image fun i => code (rec T i)).card = 9240 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (hmono j hj i h).ne
    · exact h
    · exact absurd hij (hmono i hi j h).ne'
  have hsub : ((Finset.range 9240).image fun i => code (rec T i)) ⊆
      (Finset.univ : Finset (Fin 3 ↪ Fin 22)).image
        (fun f => (f 0).val + 32 * (f 1).val + 1024 * (f 2).val) := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h0, h1, h2, h01, h02, h12⟩ :=
      injC_spec (nodeOK_spec (hnode i (Finset.mem_range.mp hi))).1
    obtain ⟨f, hf0, hf1, hf2⟩ := exists_emb h0 h1 h2 h01 h02 h12
    refine Finset.mem_image.mpr ⟨f, Finset.mem_univ f, ?_⟩
    have hlt := code_lt (rec T i)
    rw [hf0, hf1, hf2, fget0, fget1, fget2]
    omega
  have hle : ((Finset.univ : Finset (Fin 3 ↪ Fin 22)).image
      (fun f => (f 0).val + 32 * (f 1).val + 1024 * (f 2).val)).card ≤ 9240 := by
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
    decide
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  intro e
  have hmem : (e 0).val + 32 * (e 1).val + 1024 * (e 2).val ∈
      (Finset.range 9240).image fun i => code (rec T i) := by
    rw [heq]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ e)
  obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp hmem
  obtain ⟨g, hg, hg0, hg1, hg2⟩ := horb _ i (Finset.mem_range.mp hi) rfl
  rw [fget0, hci] at hg0
  rw [fget1, hci] at hg1
  rw [fget2, hci] at hg2
  have he0 := (e 0).isLt
  have he1 := (e 1).isLt
  have he2 := (e 2).isLt
  have key : g 0 = e 0 ∧ g 1 = e 1 ∧ g 2 = e 2 :=
    ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega)⟩
  refine ⟨g, hg, fun j => ?_⟩
  fin_cases j
  · exact key.1
  · exact key.2.1
  · exact key.2.2

end CFSG.KC.Triple

end
