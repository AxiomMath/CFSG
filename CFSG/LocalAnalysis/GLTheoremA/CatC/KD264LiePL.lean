module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.Assembly.InCatalogConverse
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerComponentDvd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator

theorem kd264PL_holds
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KD264PL p := by
  intro d _ hpq β hβ hβ1 P hPX hP hPdvd
  obtain ⟨-, hsimp⟩ := CFSG.Assembly.lie_finite_simple d
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := hsimp
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie d).Group, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have hbot : ⁅P, P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact h y x
    have hPbot : P = ⊥ := by rw [← hP, hbot]
    exact hp.not_dvd_one (by simpa [hPbot] using hPdvd)
  have hPL := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
    (TauCeti.CFSGIndex.lie d).Group hsimp hnc d ⟨MulEquiv.refl _⟩ p hp hp2 hpq β hβ hβ1
  exact CFSG.exists_glaPComponent_dvd_card_of_dvd_card_glaLayer hp
    (hPdvd.trans (Subgroup.card_dvd_of_le (hPL P hPX hP)))

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
