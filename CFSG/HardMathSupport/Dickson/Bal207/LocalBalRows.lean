module

public import CFSG.HardMathSupport.Dickson.Bal207.Restate
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalTits
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalTitsFive
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalG2Eight

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux
  CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def Bal207LocalBalRow (P : ℕ → TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ) (d : TauCeti.ValidLieTypeIndex), P p d.1 →
    IsLocallyBalancedAbs p 1 (TauCeti.CFSGIndex.lie d).Group

theorem bal207LocalBalAbs_of_rows (hSp : Bal207LocalBalRow FamSp)
    (hUni : Bal207LocalBalRow FamUni) (hOrth : Bal207LocalBalRow FamOrth)
    (hU62 : Bal207LocalBalRow fun p d => p = 3 ∧ IsExcU62 d)
    (h3D4 : Bal207LocalBalRow fun p d => p = 3 ∧ IsExc3D42 d)
    (hRee : Bal207LocalBalRow fun p d => p = 5 ∧ IsExcRee32 d) : Bal207LocalBalAbs := by
  rintro p ⟨d, hv⟩ hd
  by_cases hs : IsSpIdx d
  · exact hSp p ⟨d, hv⟩ ⟨hd, hs⟩
  by_cases hu : IsUniIdx d
  · exact hUni p ⟨d, hv⟩ ⟨hd, hu⟩
  by_cases ho : IsOrthIdx d
  · exact hOrth p ⟨d, hv⟩ ⟨hd, ho⟩
  by_cases hg : IsG2EightIndex d
  · have hp : p = 3 := bal207Index_g2 hd hg
    subst hp
    cases d with
    | G2 q => exact isLocallyBalancedAbs_three_one_G2_eight hg hv
    | _ => exact False.elim hg
  rcases famExcNoG2_cases ⟨⟨hd, hs, hu, ho⟩, hg⟩ with h | h | h | h | h | h | h
  · exact hU62 p ⟨d, hv⟩ h
  · exact h3D4 p ⟨d, hv⟩ h
  · obtain ⟨rfl, h⟩ := h
    cases d with
    | F4 q => exact isLocallyBalancedAbs_three_one_F4_two h hv
    | _ => exact False.elim h
  · obtain ⟨rfl, h⟩ := h
    cases d with
    | tits => exact isLocallyBalancedAbs_three_one_tits hv
    | _ => exact False.elim h
  · obtain ⟨rfl, h⟩ := h
    cases d with
    | tits => exact isLocallyBalancedAbs_five_one_tits hv
    | _ => exact False.elim h
  · exact hRee p ⟨d, hv⟩ h
  · obtain ⟨rfl, h⟩ := h
    cases d with
    | suzuki m =>
      change m = 2 at h
      subst h
      exact isLocallyBalancedAbs_five_one_sz32 hv
    | _ => exact False.elim h

theorem bal207LocalBal_of_rows (hSp : Bal207LocalBalRow FamSp)
    (hUni : Bal207LocalBalRow FamUni) (hOrth : Bal207LocalBalRow FamOrth)
    (hU62 : Bal207LocalBalRow fun p d => p = 3 ∧ IsExcU62 d)
    (h3D4 : Bal207LocalBalRow fun p d => p = 3 ∧ IsExc3D42 d)
    (hRee : Bal207LocalBalRow fun p d => p = 5 ∧ IsExcRee32 d) : Bal207LocalBal :=
  bal207LocalBal_of_abs (bal207LocalBalAbs_of_rows hSp hUni hOrth hU62 h3D4 hRee)

theorem bal207PlusLocalBalD4Eight_of_row
    (h : Bal207LocalBalRow fun p d => p = 3 ∧ IsD4EightIdx d) : Bal207PlusLocalBalD4Eight := by
  intro X _ _ _ K A hK hLie _ _
  obtain ⟨d, hd, e⟩ := hLie
  exact isCompLocallyBalanced_of_abs (P := fun p d => p = 3 ∧ IsD4EightIdx d) h Nat.prime_three A
    hK.2.2 ⟨d, ⟨rfl, hd⟩, e⟩

end CFSG.HardMathSupport.Dickson.Bal207
