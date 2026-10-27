module

public import Certificates.Data.Kernel.Misc.PairCount
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic

public section

namespace CFSG.KC.Misc.PairCount

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

private theorem bit_eq (a i : Nat) :
    Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq a i) =
      if a = i then 1 else 0 := by
  by_cases h : a = i
  · subst h
    rw [Nat.beq_refl, ite_eq_left_iff.2 (fun h => absurd rfl h)]
  · have : Nat.beq a i = false := by
      cases e : Nat.beq a i
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [this, ite_eq_right_iff.2 (fun h' => absurd h' h)]

private theorem pair_spec {N w K1 K2 : Nat} (hp : pairK N w K1 K2 = true) :
    ∀ x < N, pg w (mask w) K1 x < pg w (mask w) K2 x := by
  unfold pairK at hp
  induction N with
  | zero => intro x hx; omega
  | succ n ih =>
    have e : CFSG.KC.LQT.P.allN (n + 1)
        (fun x => Nat.blt (pg w (mask w) K1 x) (pg w (mask w) K2 x)) =
        CFSG.KC.Ord.andB (Nat.blt (pg w (mask w) K1 n) (pg w (mask w) K2 n))
          (CFSG.KC.LQT.P.allN n
            (fun x => Nat.blt (pg w (mask w) K1 x) (pg w (mask w) K2 x))) := rfl
    rw [e] at hp
    cases h1 : Nat.blt (pg w (mask w) K1 n) (pg w (mask w) K2 n) <;>
      rw [h1] at hp
    · exact absurd hp Bool.false_ne_true
    · intro x hx
      rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
      · exact ih hp x hx
      · exact Nat.le_of_ble_eq_true h1

theorem cntAt_sound {N w K1 K2 i : Nat} (hp : pairK N w K1 K2 = true) :
    ((Finset.univ : Finset (Fin N)).filter fun x : Fin N =>
      i = pg w (mask w) K1 (x : ℕ) ∨ i = pg w (mask w) K2 (x : ℕ)).card = cntAt N w K1 K2 i := by
  have hl := pair_spec hp
  clear hp
  rw [← Finset.card_map Fin.valEmbedding]
  have hm : ((Finset.univ : Finset (Fin N)).filter fun x : Fin N =>
      i = pg w (mask w) K1 (x : ℕ) ∨ i = pg w (mask w) K2 (x : ℕ)).map Fin.valEmbedding =
      (Finset.range N).filter fun x =>
        i = pg w (mask w) K1 x ∨ i = pg w (mask w) K2 x := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨ha, hx⟩
      exact ⟨⟨a, ha⟩, hx, rfl⟩
  rw [hm]
  clear hm
  induction N with
  | zero => rfl
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    change _ = cntAt n w K1 K2 i +
      Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (pg w (mask w) K1 n) i) +
      Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (Nat.beq (pg w (mask w) K2 n) i)
    rw [bit_eq, bit_eq, ← ih (fun x hx => hl x (Nat.lt_succ_of_lt hx))]
    have := hl n (Nat.lt_succ_self n)
    have hn : n ∉ (Finset.range n).filter fun x =>
        i = pg w (mask w) K1 x ∨ i = pg w (mask w) K2 x := by
      simp
    have hc := Finset.card_insert_of_notMem hn
    split_ifs <;> omega

theorem unpack_get {n w P x : Nat} (hx : x < n) : (unpack n w P)[x]! = pg w (mask w) P x := by
  unfold unpack
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

end CFSG.KC.Misc.PairCount

end
