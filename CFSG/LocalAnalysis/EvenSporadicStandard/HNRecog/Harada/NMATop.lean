module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.NMASetting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6} {R0 F : Subgroup G}

private theorem qm_tv : qm tv = 1 := by
  decide +kernel

theorem Setting25.not_isConj_t_z [Finite G] (h : Setting25 G t z z₁ ι zv R0 F)
    (hX : ∀ v, IsConj t (coordElt ι v) ↔ qm v = 1) : ¬ IsConj t z := by
  rw [← h.coord_z, hX zv, h.hD2.qm_zv]
  decide

theorem Setting25.isConj_t_mul_z [Finite G] (h : Setting25 G t z z₁ ι zv R0 F)
    (hX : ∀ v, IsConj t (coordElt ι v) ↔ qm v = 1) : IsConj t (t * z) := by
  have hbil : bil tv zv = 0 := by
    rw [bil_comm, ← lam_eq_bil, h.hD2.lam_zv]
  have hq : qm (tv + zv) = 1 := by
    rw [qm_add, qm_tv, h.hD2.qm_zv, hbil]
    decide
  have htz : t * z = coordElt ι (tv + zv) := by
    rw [coordElt_add, h.ι_tv, h.coord_z]
  rw [htz]
  exact (hX (tv + zv)).2 hq

end CFSG.EvenSporadicStandard.HNRecog.Harada
