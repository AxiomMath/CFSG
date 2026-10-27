module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Lay
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Layer
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5_conj_L (h52a : Asc82Lemma52a) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {y : G}
    (hyt : y ∈ centralizer ({t} : Set G)) : CFSG.conjugate L y = L := by
  have hL : layerC5 t = L := layerC5_eq_of_setting h52a c.toSec5Setting
  have hconj := sec5b517_layerC5_conj t y
  have hyt' : y⁻¹ * t * y = t := by
    have hcomm : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyt
    calc y⁻¹ * t * y = y⁻¹ * (t * y) := by rw [mul_assoc]
      _ = y⁻¹ * (y * t) := by rw [← hcomm]
      _ = t := by rw [inv_mul_cancel_left]
  rw [← hL, ← hconj, hyt']

theorem sec5_conj_K12 (h52a : Asc82Lemma52a) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {y : G}
    (hyt : y ∈ centralizer ({t} : Set G)) (hyz : y ∈ centralizer ({z} : Set G)) :
    CFSG.conjugate (K₁ ⊔ K₂) y = K₁ ⊔ K₂ := by
  have hL : CFSG.conjugate L y = L := sec5_conj_L h52a c hyt
  calc CFSG.conjugate (K₁ ⊔ K₂) y
      = CFSG.conjugate (twoRes (L ⊓ centralizer ({z} : Set G))) y := by rw [c.prod]
    _ = twoRes (CFSG.conjugate (L ⊓ centralizer ({z} : Set G)) y) := by
          rw [← sec5b513_twoRes_conjugate]
    _ = twoRes (CFSG.conjugate L y ⊓ centralizer ({z} : Set G)) := by
          rw [sec5b513_conjugate_inf_centralizer L hyz]
    _ = twoRes (L ⊓ centralizer ({z} : Set G)) := by rw [hL]
    _ = K₁ ⊔ K₂ := by rw [← c.prod]

end CFSG.OddStandard.SmallF3.Omega
