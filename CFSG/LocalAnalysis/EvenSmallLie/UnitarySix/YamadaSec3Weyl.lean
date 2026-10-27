module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Model
import all CFSG.Fischer.F4

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer

theorem sujExt {A B : SUJ}
    (h : ((A : Matrix.SpecialLinearGroup (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) =
      ((B : Matrix.SpecialLinearGroup (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :
    A = B :=
  Subtype.ext (Subtype.ext h)

theorem w₁_sq : yamGen 15 * yamGen 15 = 1 := sujExt (by decide)

theorem w₂_sq : yamGen 16 * yamGen 16 = 1 := sujExt (by decide)

theorem w₃_sq : yamGen 17 * yamGen 17 = 1 := sujExt (by decide)

theorem braid₁₂ : yamGen 15 * yamGen 16 * yamGen 15 = yamGen 16 * yamGen 15 * yamGen 16 :=
  sujExt (by decide +kernel)

@[expose] def yw₀ : SUJ := (yamGen 15 * yamGen 16 * yamGen 17) ^ 3

theorem word_a : yamGen 17 * yamGen 16 * yamGen 17 * yamGen 15 * yamGen 16 * yamGen 17 *
    yamGen 15 * yamGen 16 = yw₀ * yamGen 15 := sujExt (by decide +kernel)

theorem word_b : yamGen 17 * yamGen 16 * yamGen 17 * yamGen 15 * yamGen 16 * yamGen 17 *
    yamGen 16 * yamGen 15 = yw₀ * yamGen 16 := sujExt (by decide +kernel)

theorem word_b' : yamGen 15 * yamGen 16 * yamGen 17 * yamGen 16 * yamGen 15 * yamGen 17 *
    yamGen 16 * yamGen 17 = yw₀ * yamGen 16 := sujExt (by decide +kernel)

theorem word_c : yamGen 15 * yamGen 16 * yamGen 17 * yamGen 16 * yamGen 15 * yamGen 16 *
    yamGen 17 * yamGen 16 = yw₀ * yamGen 17 := sujExt (by decide +kernel)

theorem word_c' : yamGen 15 * yamGen 16 * yamGen 15 * yamGen 17 * yamGen 16 * yamGen 17 *
    yamGen 15 * yamGen 16 = yw₀ * yamGen 17 := sujExt (by decide +kernel)

theorem w₁_gen : yamGen 15 = yamGen 0 * (yamGen 15 * yamGen 0 * yamGen 15) * yamGen 0 :=
  sujExt (by decide +kernel)

theorem w₂_gen : yamGen 16 = yamGen 2 * (yamGen 16 * yamGen 2 * yamGen 16) * yamGen 2 :=
  sujExt (by decide +kernel)

theorem w₃_gen : yamGen 17 = yamGen 4 * (yamGen 17 * yamGen 4 * yamGen 17) * yamGen 4 :=
  sujExt (by decide +kernel)

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
