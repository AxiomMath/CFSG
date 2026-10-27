module

public import Certificates.Data.Kernel.He7222.Fix
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.SporSch.LyLoop

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KS.PF

variable {n w : ℕ}

theorem fixCnt_eq (n w m x : ℕ) :
    fixCnt n w m x = ((List.range n).filter (fun p => Nat.beq (pg w m x p) p)).length := by
  unfold fixCnt
  rw [CFSG.KS.SporSch.LyLoop.foldN_eqP]
  induction (List.range n) with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, List.filter_cons]
    rcases Bool.eq_false_or_eq_true (Nat.beq (pg w m x a) a) with hb | hb
    · rw [if_pos hb, List.length_cons]
      change Nat.add _ (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (pg w m x a) a)) = _
      rw [hb]
      rfl
    · rw [if_neg (by rw [hb]; simp)]
      change Nat.add _ (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (pg w m x a) a)) = _
      rw [hb]
      rfl

theorem fixNeK_sound {n w m x y : ℕ} (h : fixNeK n w m x y = true) :
    fixCnt n w m x ≠ fixCnt n w m y := by
  intro he
  have h' : bIf(Nat.beq (fixCnt n w m x) (fixCnt n w m y), false, true) = true := h
  rw [he, Nat.beq_refl] at h'
  exact absurd h' (by simp)

theorem count_range_eq (q : ℕ → Bool) :
    ((List.range n).filter q).length = (Finset.univ.filter (fun p : Fin n => q p = true)).card := by
  have h1 : (Finset.univ.filter (fun p : Fin n => q p = true)).map Fin.valEmbedding =
      (Finset.range n).filter (fun p => q p = true) := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp⟩
    · rintro ⟨ha, hq⟩
      exact ⟨⟨a, ha⟩, hq, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, h1]
  change ((List.range n).filter q).length =
    Multiset.card (Multiset.filter (fun p => q p = true) (↑(List.range n) : Multiset ℕ))
  rw [Multiset.filter_coe, Multiset.coe_card]
  simp

theorem fixCnt_rep {x : ℕ} {g : Equiv.Perm (Fin n)} (hx : PRep n w x g) :
    fixCnt n w (mask w) x = (Finset.univ.filter (fun p : Fin n => g p = p)).card := by
  rw [fixCnt_eq, count_range_eq]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.beq_eq_true_eq, hx p]
  exact ⟨fun h => Fin.ext (Nat.eq_of_beq_eq_true h), fun h => by rw [h]; exact Nat.beq_refl _⟩

theorem fixCnt_conj {x y : ℕ} {g h c : Equiv.Perm (Fin n)} (hx : PRep n w x g)
    (hy : PRep n w y h) (hc : g = c * h * c⁻¹) : fixCnt n w (mask w) x = fixCnt n w (mask w) y := by
  rw [fixCnt_rep hx, fixCnt_rep hy]
  have e : (Finset.univ.filter (fun p : Fin n => h p = p)).map c.toEmbedding =
      Finset.univ.filter (fun p : Fin n => g p = p) := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply, hc, Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨q, hq, rfl⟩
      change c (h (c.symm (c q))) = c q
      rw [c.symm_apply_apply, hq]
    · intro hp
      refine ⟨c.symm p, ?_, c.apply_symm_apply p⟩
      have := congrArg c.symm hp
      change c.symm (c (h (c.symm p))) = c.symm p at this
      rwa [c.symm_apply_apply] at this
  rw [← e, Finset.card_map]

theorem not_conj_of_fixNeK {x y : ℕ} {g h : Equiv.Perm (Fin n)}
    (hne : fixNeK n w (mask w) x y = true) (hx : PRep n w x g) (hy : PRep n w y h) :
    ∀ c : Equiv.Perm (Fin n), g ≠ c * h * c⁻¹ := fun c hc =>
  fixNeK_sound hne (fixCnt_conj hx hy hc)

end CFSG.KC.HeChain

end
