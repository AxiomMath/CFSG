module

public import Certificates.Data.Kernel.SporSch.MatSch
public import CFSG.Certificates.Kernel.Spor.RawTreeDefs
public import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.MatSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] def SchMOK (n w nw d md L I PV : Nat) (PS PSI SM SMI LK LR OF TM TIM ST : Nat → Nat)
    (kS BP nb : Nat) : Prop :=
  ∀ i < nb, ∀ h < rcnt (LR i),
    schMK n w nw d md L I PV PS PSI SM SMI LK LR OF TM TIM kS BP nb i (ST i) h 1 = true

theorem schMK_one {n w nw d md L I PV : Nat} {PS PSI SM SMI LK LR OF TM TIM : Nat → Nat}
    {kS BP nb i T h₀ cnt : Nat}
    (hs : schMK n w nw d md L I PV PS PSI SM SMI LK LR OF TM TIM kS BP nb i T h₀ cnt = true)
    {e : Nat} (he : e < cnt) :
    schMK n w nw d md L I PV PS PSI SM SMI LK LR OF TM TIM kS BP nb i T (Nat.add h₀ e) 1 =
      true := by
  unfold schMK at hs ⊢
  simp only [CFSG.KS.Raw.Orb.strictB_eq] at hs ⊢
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 hs e he
  refine CFSG.KS.Raw.Orb.allN_iff.2 fun e' he' => ?_
  have e0 : e' = 0 := by omega
  subst e0
  exact h1

theorem sch_of_sl (n w nw d md L I PV : Nat) (PS PSI SM SMI LK LR OF TM TIM : Nat → Nat)
    (kS BP nb i T NS CH : Nat) (hN : rcnt (LR i) ≤ NS * CH)
    (hs : ∀ s < NS,
      schMK n w nw d md L I PV PS PSI SM SMI LK LR OF TM TIM kS BP nb i T (s * CH) CH = true) :
    ∀ h < rcnt (LR i),
      schMK n w nw d md L I PV PS PSI SM SMI LK LR OF TM TIM kS BP nb i T h 1 = true := by
  intro h hh
  obtain ⟨hCH, hsk, e⟩ := slice_cover hN hh
  have := schMK_one (hs (h / CH) hsk) (Nat.mod_lt h hCH)
  rwa [e] at this

end CFSG.KS.MatSch

end
