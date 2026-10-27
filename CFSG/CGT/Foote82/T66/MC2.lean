module

public import CFSG.CGT.Foote82.T66.Steps
public import CFSG.CGT.Foote82.T66.CitedMC2
import CFSG.CGT.Foote82.T66.MC2Quot
import CFSG.CGT.Foote82.T66.MC2Spor
import CFSG.CGT.Foote82.T66.MC2Case24
import CFSG.CGT.Foote82.T66.MC2F2
import CFSG.CGT.Foote82.OddCover

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

theorem caseMC2 (hF : FrontierRankTwoF) (h5 : SporadicNoFComponent) (h24 : FooteLemma24)
    (h13 : A11DoubleThreeCycle) (h6 : A6NoSixDimIrr) : CaseMC2 := by
  intro V _ _ _ G L s h hrank
  have hLG : L ≤ G := MC2.stdForm_L_le h
  obtain ⟨⟨hqE, hqG⟩, hodd, hsimple, hnonab, hK, hstd, hrankbar⟩ := MC2.quotData h hrank
  rcases hF (MC2.Gbar G) hnonab hK (MC2.Lbar G L) hstd hrankbar with ⟨m, hm, ⟨e⟩⟩ | hspor
  ·
    let η : ↥G →* alternatingGroup (Fin m) :=
      (e : MC2.Gbar G →* alternatingGroup (Fin m)).comp (QuotientGroup.mk' (Subgroup.center ↥G))
    have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : η.ker = Subgroup.center ↥G := by
      rw [MonoidHom.ker_mulEquiv_comp, QuotientGroup.ker_mk']
    have hperf : commutator ↥G = ⊤ := hqG.1.commutator_eq_top
    have hbot := ker_eq_bot_of_odd_alt hperf (by omega : 8 ≤ m) η hη hker.le (hker ▸ hodd)
    let ψ : ↥G ≃* alternatingGroup (Fin m) :=
      MulEquiv.ofBijective η ⟨(MonoidHom.ker_eq_bot_iff η).1 hbot, hη⟩
    have h4 : 4 ∣ Nat.card ↥(G ⊓ Subgroup.centralizer (L : Set (GLV V))) := by
      have := MC2.sq_dvd_card_of_two_le_pRank (p := 2) (by norm_num) hrank
      simpa using this
    obtain ⟨F, hd⟩ := MC2.altSetup h h4 ψ
    rcases h.extremal.fmod with ⟨n, hn, hA⟩ | hA | hA | hA | hA | hA
    · exact MC2.case_alt h24 h hqE hd hn hA
    · exact MC2.case_a7four h13 h hd hA
    · exact MC2.case_alt h24 h hqE hd (by norm_num) (MC2.isAltNaturalModule_of_omegaPlus_three hA)
    · exact MC2.case_omegaMinus hd (Or.inl rfl) hA
    · exact MC2.case_omegaMinus hd (Or.inr rfl) hA
    · exact MC2.case_a6z3 h6 h hd hA
  ·
    refine MC2.sporadic_false h5 hspor hstd (MC2.fSurj_map _ ?_
      (MC2.fSurj_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG)
        (MC2.IsFPrimeModule.fSurj h.extremal.fmod)))
    rw [QuotientGroup.ker_mk']

end CFSG.CGT.Foote82
