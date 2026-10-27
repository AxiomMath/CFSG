
module

public import CFSG.Certificates.Kernel.M24L2.CtxSound
public import Certificates.Data.Kernel.M24L2.R3
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R CFSG.CGT.L5R.R3 CFSG.KC.Enum

theorem wTab_beq (w w' : List (Fin 10 × Bool)) : (wTab w == wTab w') = Nat.beq (cwK w) (cwK w') := by
  rw [wTab_tabC, wTab_tabC, beq_tabC (cwK_lt w) (cwK_lt w')]

theorem identCheck_eq : identCheck = identCheckK := by
  have h : tEq = tEqK := funext fun w => funext fun w' => wTab_beq w w'
  unfold identCheck identCheckK
  rw [h]

theorem mulC_div16 (a b : Nat) : mulC a b / 16 = mulC (16 * (a / 16)) (16 * (b / 16)) / 16 := by
  rw [mulC_eq, mulC_eq]
  have h1 := aff_lt a (b % 16)
  have h2 := aff_lt (16 * (a / 16)) (16 * (b / 16) % 16)
  have e1 : (16 * (a / 16)) / 16 = a / 16 := by omega
  have e2 : (16 * (b / 16)) / 16 = b / 16 := by omega
  rw [e1, e2]
  omega

theorem mulC_mod16_lin (a b : Nat) : mulC (16 * a) (16 * b) % 16 = 0 := by
  rw [mulC_mod16, show 16 * b % 16 = 0 by omega]
  exact aff_zero_lin (by omega)

theorem commK_lin {c y : Nat} (h : commK c y = true) :
    commK (16 * (c / 16)) (16 * (y / 16)) = true := by
  unfold commK at *
  rw [Nat.beq_eq] at *
  have e1 := mulC_div16 c y
  have e2 := mulC_div16 y c
  rw [h] at e1
  have h3 := mulC_mod16_lin (c / 16) (y / 16)
  have h4 := mulC_mod16_lin (y / 16) (c / 16)
  omega

theorem commT_tabC (a b : Nat) : commT (tabC a) (tabC b) = commK a b := by
  unfold commT commK
  rw [compT_tabC, compT_tabC, beq_tabC (mulC_lt _ _) (mulC_lt _ _)]

theorem centM_spec {y1 y2 m : Nat} (h : centM y1 y2 m = true) :
    ∀ v < 16, centBody y1 y2 (v + 16 * m) = true := by
  intro v hv
  unfold centM at h
  rcases hl : centLin y1 y2 m with _ | _
  · unfold centBody
    have : (commK (v + 16 * m) y1 && commK (v + 16 * m) y2) = false := by
      unfold centLin at hl
      rcases h1 : commK (v + 16 * m) y1 with _ | _
      · rfl
      rcases h2 : commK (v + 16 * m) y2 with _ | _
      · rfl
      have k1 := commK_lin h1
      have k2 := commK_lin h2
      rw [show (v + 16 * m) / 16 = m by omega] at k1 k2
      change (commK (16 * m) (16 * (y1 >>> 4)) && commK (16 * m) (16 * (y2 >>> 4))) = false at hl
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, k1, k2] at hl
      simp at hl
    rw [this]
  · rw [hl] at h
    change allN 16 _ = true at h
    rw [CFSG.KS.Raw.Orb.allN_iff] at h
    have := h v hv
    rw [letN_eq] at this
    exact this

theorem centCheck_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536)
    (h : ∀ m ∈ L, centM (cwK (yW 0)) (cwK (yW 1)) m = true) : centCheck (mkCtx ()) = true := by
  unfold centCheck
  simp only [List.all_eq_true]
  intro c hc
  rw [tab_of_mem hR hc, wTab_tabC, wTab_tabC, commT_tabC, commT_tabC, idT_tabC,
    beq_tabC ((mem_codes_iff hR).1 hc).1 (by decide)]
  have hb := forall_codes hR hL (P := fun c => centBody (cwK (yW 0)) (cwK (yW 1)) c = true)
    (fun m hm v hv => centM_spec (h m hm) v hv) c hc
  unfold centBody at hb
  revert hb
  cases commK c (cwK (yW 0)) && commK c (cwK (yW 1)) <;> simp

end CFSG.KC.M24L2
