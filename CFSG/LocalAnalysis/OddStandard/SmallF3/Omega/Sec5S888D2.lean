module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888D1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B514Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5_conj_K34 (h37 : Asc82Lemma37) (h52a : Asc82Lemma52a) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {y : G} (hyt : y ∈ centralizer ({t} : Set G))
    (hyz : y ∈ centralizer ({z} : Set G)) :
    CFSG.conjugate (CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) y =
      CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := by
  have hz : h⁻¹ * z * h = z := by
    have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
    calc h⁻¹ * z * h = h⁻¹ * (h * z) := by rw [hhz]; group
      _ = z := by group
  have hh : h⁻¹ * h * h = h := by group
  have hctx : Sec5HCtx G (h⁻¹ * t * h) (CFSG.conjugate L h) (CFSG.conjugate S h) z
      (h⁻¹ * r * h) (CFSG.conjugate B h) (CFSG.conjugate A h) (CFSG.conjugate K₁ h)
      (CFSG.conjugate K₂ h) h := by
    have hc := sec5HCtx_conj c h
    rwa [hz, hh] at hc
  have hmem : y⁻¹ * (h⁻¹ * t * h) * y ∈
      DeltaT5 z (CFSG.conjugate (CFSG.conjugate K₁ h) h)
        (CFSG.conjugate (CFSG.conjugate K₂ h) h) := by
    refine ⟨?_, ?_, ?_⟩
    · have he : y⁻¹ * (h⁻¹ * t * h) * y = (h * y)⁻¹ * t * (h * y) := by group
      rw [he, orderOf_conjugate_eq, c.involution]
    · intro hd
      have he : y⁻¹ * (h⁻¹ * t * h) * y = (h * y)⁻¹ * t * (h * y) := by group
      have htz : (h * y)⁻¹ * t * (h * y) = z := by rw [← he]; exact hd
      exact sec5_t_not_conj_z h37 c.toSec5Ctx ((h * y)⁻¹)
        (calc ((h * y)⁻¹)⁻¹ * z * (h * y)⁻¹
            = (h * y) * z * (h * y)⁻¹ := by rw [inv_inv]
          _ = (h * y) * ((h * y)⁻¹ * t * (h * y)) * (h * y)⁻¹ := by rw [htz]
          _ = t := by group)
    · rw [sec5b517_conjugate_conjugate, sec5b517_conjugate_conjugate, ← sec5b_conjugate_sup,
        sec5_conj_K12 h52a c c.h_sq (mul_mem c.h_z c.h_z)]
      exact sec5b_mem_of_conjugate_eq' (sec5_conj_K12 h52a c hyt hyz) c.h_t
  exact (h513 G (h⁻¹ * t * h) (CFSG.conjugate L h) (CFSG.conjugate S h) z (h⁻¹ * r * h)
    (CFSG.conjugate B h) (CFSG.conjugate A h) (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h)
    h hctx y hyz hmem).2

end CFSG.OddStandard.SmallF3.Omega
