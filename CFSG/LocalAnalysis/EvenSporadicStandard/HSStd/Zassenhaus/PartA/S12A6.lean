module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Types
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Invol
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Sylow3

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Types

namespace S12A6

theorem cube_check : Core.autL.all (fun c =>
    Core.cmul c (Core.cmul c c) != Core.cid || Core.pslLit.contains c) = true := by
  decide +kernel

end S12A6

theorem mulAut_cube_inner (α : MulAut (alternatingGroup (Fin 6))) (h : α * α * α = 1) :
    α ∈ (MulAut.conj : alternatingGroup (Fin 6) →*
      MulAut (alternatingGroup (Fin 6))).range := by
  rw [mem_inner_iff]
  set y : AutA6 := thetaEquiv.symm α with hy
  have hy3 : y * (y * y) = 1 := by
    apply thetaEquiv.injective
    rw [map_mul, map_mul, map_one, hy, MulEquiv.apply_symm_apply, ← mul_assoc, h]
  have h1 := List.all_eq_true.mp S12A6.cube_check _ (cd_mem_autL y)
  have h2 : Core.cmul (cd y) (Core.cmul (cd y) (cd y)) = Core.cid := by
    rw [← cd_mul, ← cd_mul, hy3, cd_one]
  rw [h2] at h1
  simp only [bne_self_eq_false, Bool.false_or] at h1
  exact (mem_PslSub_iff_contains y).2 h1

theorem mulAut_eq_one_of_fix_centralizer {x : alternatingGroup (Fin 6)} (hx : orderOf x = 3)
    (α : MulAut (alternatingGroup (Fin 6))) (h2 : α * α = 1)
    (hα : ∀ a ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6))), α a = a) :
    α = 1 := by
  obtain ⟨b, hb, rfl⟩ := mem_inner_of_fix_centralizer hx α hα
  have hbb : b * b = 1 := by
    apply CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
    rw [map_mul, map_one]
    exact h2
  have h3 := pow_three_of_mem_centralizer hx b hb
  have : b = 1 := by
    calc b = b ^ 3 * (b * b)⁻¹ := by group
      _ = 1 := by rw [h3, hbb]; simp
  rw [this, map_one]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
