module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAEng
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAGen
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesCplx

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fj_mul_self_eq_one_of_odd (hQ : Q.Nondegenerate)
    (hodd : ¬ Even (Module.finrank (ZMod 3) V)) {A : OGroup Q}
    (h : toProj Q A * toProj Q A = 1) : A * A = 1 := by
  have hAAmem : A * A ∈ piGroup Q :=
    (QuotientGroup.eq_one_iff (A * A)).mp (by
      show toProj Q (A * A) = 1
      rw [map_mul]
      exact h)
  rcases mem_piGroup_iff.mp hAAmem with h1 | h1
  · exact h1
  · exact absurd ((exists_mul_self_eq_piOrth_iff hQ).mp ⟨A, h1⟩).1 hodd

@[expose] def FJIsomInv (hQ : Q.Nondegenerate) : Prop :=
  ∀ α : MulAut (omegaProj hQ), α * α = 1 → ∃ s : OGroup Q, s * s = 1 ∧ α = projAut hQ s

theorem fjKGAAt_of_isomInv (hQ : Q.Nondegenerate) (hn : Module.finrank (ZMod 3) V ≤ 7)
    (h : FJIsomInv hQ) : FJKGAAt ↥(omegaProj hQ) := by
  intro y B hy hB α hαα hα1 hfix hαy
  obtain ⟨s, hs, rfl⟩ := h α hαα
  obtain ⟨J, hJ, hJF, hBJ⟩ := fj_kga_engine_le7 hQ hn hs hα1 hy hB hfix hαy
  exact ⟨J, by rw [l34g_fix_eq_fixSub]; exact hJ, hJF, hBJ⟩

end CFSG.OddStandard.SmallF3.Omega
