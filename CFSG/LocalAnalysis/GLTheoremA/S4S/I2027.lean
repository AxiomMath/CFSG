module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

theorem i2027At_of (h : KD2027) : I2027At := by
  intro K _ _ hK hcat A S hA hS hN hAS
  have : Group.IsPerfect K := ⟨hK.1⟩
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  set φ := CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K with hφ
  have hinj : Function.Injective φ :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K
  have hA' : IsPGroup 3 (A.map φ) := hA.map φ
  have hS' : IsPGroup 2 (S.map φ) := hS.map φ
  have hN' : A.map φ ≤ Subgroup.normalizer
      ((S.map φ : Subgroup (MulAut (K ⧸ Subgroup.center K))) : Set (MulAut (K ⧸ Subgroup.center K))) :=
    (Subgroup.map_mono (f := φ) hN).trans (Subgroup.le_normalizer_map φ)
  have hAS' : (⁅A.map φ, S.map φ⁆ : Subgroup (MulAut (K ⧸ Subgroup.center K))) = S.map φ := by
    rw [← Subgroup.map_commutator, hAS]
  have key := h (K ⧸ Subgroup.center K) hsimple hcat (A.map φ) (S.map φ) hA' hS' hN' hAS'
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator] at key
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp key

end CFSG.LocalAnalysis.GLTheoremA
