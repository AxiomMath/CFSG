module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56.BridgeGN
public import CFSG.Alternating.Multipliers.OddKernel

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56

open CFSG.HardMathSupport.Cooperstein.Coordinator (GF2EightFive)
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

theorem altOddCentreTrivial : AltOddCentreTrivial := by
  intro Q _ _ hQ hodd n hn ⟨e⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have : Group.IsPerfect Q := ⟨hQ.1⟩
  let η : Q →* alternatingGroup (Fin (m + 2)) := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center Q := by
    ext x
    simp only [MonoidHom.mem_ker, η, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hodd' : Odd (Nat.card η.ker) := by
    rw [hker]; exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd)
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (by omega) η hη hker.le hodd'
  rw [hker] at h1
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem agl81I56_of_gf2EightFive' (hGF : GF2EightFive) : AGL81I56 :=
  agl81I56_of_gf2EightFive hGF altOddCentreTrivial

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
