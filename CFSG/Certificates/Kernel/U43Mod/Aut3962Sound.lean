module

public import Certificates.Data.Kernel.U43Mod.Aut3962
public import CFSG.Certificates.Kernel.U43Mod.WordSound

public section

namespace CFSG.KS.U43Aut3962

open CFSG.KC.Enum CFSG.KC.U43Aut3962 CFSG.KS.U43Mod

variable {n : ℕ}

@[expose] def letV {G : Type*} [Group G] (x y : G) (c : ℕ) : G :=
  if c = 0 then x else if c = 1 then y else if c = 2 then x⁻¹ else y⁻¹

theorem lt_eq_of {w m X Y Xi Yi : ℕ} {x y : Equiv.Perm (Fin n)}
    (hX : ∀ q (hq : q < n), pg w m X q = (x ⟨q, hq⟩ : ℕ))
    (hY : ∀ q (hq : q < n), pg w m Y q = (y ⟨q, hq⟩ : ℕ))
    (hXi : ∀ q (hq : q < n), pg w m Xi q = (x⁻¹ ⟨q, hq⟩ : ℕ))
    (hYi : ∀ q (hq : q < n), pg w m Yi q = (y⁻¹ ⟨q, hq⟩ : ℕ)) (c q : ℕ) (hq : q < n) :
    CFSG.KC.Enum.lt w m X Y Xi Yi c q = (letV x y c ⟨q, hq⟩ : ℕ) := by
  rcases c with _ | _ | _ | c
  · exact hX q hq
  · exact hY q hq
  · exact hXi q hq
  · have h0 : Nat.beq (c + 1 + 1 + 1) 0 = false := rfl
    have h1 : Nat.beq (c + 1 + 1 + 1) 1 = false := by
      cases h : Nat.beq (c + 1 + 1 + 1) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
    have h2 : Nat.beq (c + 1 + 1 + 1) 2 = false := by
      cases h : Nat.beq (c + 1 + 1 + 1) 2
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) (by omega)
    unfold CFSG.KC.Enum.lt letV
    rw [h0, h1, h2, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hYi q hq

theorem mwv_eq {w m X Y Xi Yi : ℕ} {L : ℕ → Equiv.Perm (Fin n)}
    (hL : ∀ c q (hq : q < n), CFSG.KC.Enum.lt w m X Y Xi Yi c q = (L c ⟨q, hq⟩ : ℕ)) :
    ∀ (ws : List ℕ) q (hq : q < n), mwv w m X Y Xi Yi ws q = ((ws.map L).prod ⟨q, hq⟩ : ℕ)
  | [], q, hq => rfl
  | c :: ws, q, hq => by
    change strictN (mwv w m X Y Xi Yi ws q) (CFSG.KC.Enum.lt w m X Y Xi Yi c) = _
    rw [strictN_eq, mwv_eq hL ws q hq, hL c _ (Fin.is_lt _), List.map_cons, List.prod_cons,
      Equiv.Perm.mul_apply]

theorem mwvI_eq {w m X Y Xi Yi : ℕ} {L : ℕ → Equiv.Perm (Fin n)}
    (hL : ∀ c q (hq : q < n), CFSG.KC.Enum.lt w m Xi Yi X Y c q = ((L c)⁻¹ ⟨q, hq⟩ : ℕ)) :
    ∀ (ws : List ℕ) q (hq : q < n), mwvI w m X Y Xi Yi ws q = (((ws.map L).prod)⁻¹ ⟨q, hq⟩ : ℕ)
  | [], q, hq => rfl
  | c :: ws, q, hq => by
    change strictN (CFSG.KC.Enum.lt w m Xi Yi X Y c q) (mwvI w m X Y Xi Yi ws) = _
    rw [strictN_eq, hL c q hq, mwvI_eq hL ws _ (Fin.is_lt _), List.map_cons, List.prod_cons,
      mul_inv_rev, Equiv.Perm.mul_apply]

theorem allIdx_spec {α : Type} {f : α → ℕ → Bool} :
    ∀ (L : List α) (k : ℕ), allIdx f L k = true → ∀ i (hi : i < L.length), f L[i] (k + i) = true
  | [], _, _, i, hi => absurd hi (by simp)
  | x :: L, k, h, i, hi => by
    change Bool.rec (motive := fun _ => Bool) false (allIdx f L (Nat.succ k)) (f x k) = true at h
    rw [bAnd_iff] at h
    rcases i with _ | i
    · simpa using h.1
    · rw [List.getElem_cons_succ]
      have h' := allIdx_spec L (k + 1) h.2 i (by simpa using hi)
      have e : k + 1 + i = k + (i + 1) := by omega
      rwa [e] at h'

theorem lSel_eq {α : Type} (d : α) : ∀ (L : List α) (i : ℕ), lSel d L i = L.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => lSel_eq d L i

end CFSG.KS.U43Aut3962

end
