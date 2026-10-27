module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2B
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2W
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AET
public import CFSG.ClassicalInvolution.Q3.TL4SecIdRed

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

namespace SecIdE2

variable {Y : Type} [Group Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem core_eq_top_of_subsingleton (hc : TightCls Y R S t)
    (h : ∀ L ∈ CoreAssembly.conjClass (tightCore R),
      ∀ L' ∈ CoreAssembly.conjClass (tightCore R), L = L') :
    tightCore R = ⊤ := by
  rw [eq_top_iff, ← AlphaFr.E2D.pSpan_eq_top hc]
  exact iSup₂_le fun L hL => (h L hL _ (CoreAssembly.mem_conjClass_self _)).le

end SecIdE2

theorem secIdE2EdgelessBelow_of {n : ℕ} (hD : TC.Thin.ThmDAbsBelow 3 n) :
    SecIdE2EdgelessBelow n := by
  intro Y _ _ hn R S t hd hc hO2 hE ⟨W, hW, hZ⟩
  rcases SecIdE2.thmDConcl_of_below hD hn hd hc hO2 with
    h1 | ⟨W', hW'⟩ | ⟨E, hE8⟩ | I | ⟨m, hm, ⟨I⟩⟩ | I
  · exact SecIdE2.core_eq_top_of_subsingleton hc h1
  · have hWW : W = W' := by
      rw [hW'] at hW
      exact hW
    subst hWW
    exact SecIdE2.core_eq_top_of_subsingleton hc (SecIdE2.subsingleton_of_wSet hd hc hO2 hW' hZ)
  · exact (SecIdE2.false_of_e8 hd hc hO2 hE hW hZ hE8).elim
  · obtain ⟨I⟩ := I
    exact absurd hE (SecIdE2.not_edgeless_of_aeIdentOn hd hc hO2 (by norm_num) I
      SecIdE2.mem_e64Sets (by decide))
  · exact absurd hE (SecIdE2.not_edgeless_of_aeIdent hd hc hO2 hm I)
  · obtain ⟨I⟩ := I
    exact absurd hE (SecIdE2.not_edgeless_of_aeIdentOn hd hc hO2 (by norm_num) I
      SecIdE2.mem_e29Sets (by decide))

theorem secIdE2DStarBelow_of {n : ℕ} (hD : TC.Thin.ThmDAbsBelow 3 n) :
    SecIdE2DStarBelow n := by
  intro Y _ _ hn R S t hd hc hO2 he hds
  rcases SecIdE2.thmDConcl_of_below hD hn hd hc hO2 with
    h1 | ⟨W, hW⟩ | ⟨E, hE8⟩ | I | ⟨m, hm, ⟨I⟩⟩ | I
  · exfalso
    apply he
    intro K hK J hJ hadj
    rcases hadj with h | h
    · exact h.2.1 (h1 J hJ K hK)
    · exact h.2.1 (h1 K hK J hJ)
  · exact absurd (SecIdE2.dstarConnected_of_wSet hd hc hO2 hW) hds
  · exact absurd (SecIdE2.dstarConnected_of_e8 hd hc hO2 hE8) hds
  · obtain ⟨I⟩ := I
    exact absurd (SecIdE2.dstarConnected_of_e64 hd hc hO2 I) hds
  · rcases Nat.lt_or_ge m 6 with h6 | h6
    · obtain rfl : m = 5 := by omega
      exact ⟨I⟩
    · exact absurd (SecIdE2.dstarConnected_of_aeIdent hd hc hO2 h6 I) hds
  · obtain ⟨I⟩ := I
    exact absurd (SecIdE2.dstarConnected_of_e29 hd hc hO2 I) hds

end CFSG.ClassicalInvolution.Q3.TL4
