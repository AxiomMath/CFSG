module

public import CFSG.CGT.T75O.Norm
public import CFSG.CGT.T75O.AptSyl

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseH

variable {G : Type} [Group G] {T T₁ : Subgroup G}

namespace Cfg56

variable (c : Cfg56 T T₁)
include c

theorem false_of_coords {R : Set (Subgroup G)} {A₀ P P' : Subgroup G}
    (S : Setup R (secA T T₁) A₀ P P') {F E : Type} [Field F] [Field E] [CharP E 2] [CharP F 2]
    [Finite F] (cc : Coords S F E) (e : F →+* E)
    (he : ∀ s u, cc.c5 s u = cc.c5 (e u * s) 1)
    (hfix : ∀ (u : F) (w r : E) (v : F),
      (∀ s : E, S.ad (cc.x1_mem_normalizer s) (cc.vc u w r v) = cc.vc u w r v) →
        u = 0 ∧ w = 0 ∧ r = 0)
    {n m k o : ℕ} (hq : Nat.card (secA T T₁) = 2 ^ n)
    (hL : (linesThrough R (secA T T₁)).ncard = 2 ^ m + 1) (hE : Nat.card E = 2 ^ m)
    (hodd : Odd o) (hG : Nat.card G = 2 ^ k * o) (hk : k ≤ 3 * n + 3 * m) : False := by
  have := S.hyp.finite
  apply c.false_of_le_secA
  refine Apt.le_A cc e he hfix secA_le_left c.isPGroup_T (fun x hx => c.normalizer_secA_le hx)
    (fun v hv => ?_) hodd hG ?_
  · by_contra hv0
    have hyA := c.mem_secA_of_mem_member S.hyp.root S.hA S.hP'.2.1 (cc.x2_mem v) hv
    have h := (S.proj_P' (cc.x2_mem v)).symm.trans (S.proj_A hyA)
    have h2 := congrArg (fun p => (p.2.2.2 : G)) h
    exact hv0 (cc.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1) (h2.trans cc.x2_zero.symm))
  · rw [Apt.card_M_mul_card_E S hq hL hE]
    exact Nat.pow_le_pow_right (by norm_num) hk

end Cfg56

end CFSG.CGT.T75O
