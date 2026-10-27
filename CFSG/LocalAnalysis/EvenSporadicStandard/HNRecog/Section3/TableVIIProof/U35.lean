module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CentEquiv
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.ShapeCongr
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

theorem tableVII_shape_U35 (hS : SuborbitFacts) (h : IsF5Type a z) {c t : G}
    (htc : t ∈ Gxy a c) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hsimp : IsSimpleGroup ↥(Gxy a c))
    (hY : IsNonsplitDoubleCoverOfS5 ↥(Gxyz a t c)) : IsShapeU35 ↥(Gxy a c) := by
  obtain ⟨E, hE⟩ := h.cent_a
  have hle : Gxy a c ≤ Gx a := fun x hx => (mem_Gxy.mp hx).1
  let S : Subgroup ↥(Gx a) := (Gxy a c).subgroupOf (Gx a)
  let φ : ↥S ≃* ↥(Gxy a c) := Subgroup.subgroupOfEquivOfLe hle
  have hsimpS : IsSimpleGroup ↥S := by
    haveI := hsimp
    exact φ.isSimpleGroup
  let t'' : ↥S := φ.symm ⟨t, htc⟩
  have hphi : φ t'' = ⟨t, htc⟩ := MulEquiv.apply_symm_apply φ ⟨t, htc⟩
  have ht''2 : t'' ^ 2 = 1 := by
    apply φ.injective
    rw [map_pow, map_one, hphi]
    exact Subtype.ext (by simpa using ht2)
  have ht''1 : t'' ≠ 1 := by
    intro hh
    apply ht1
    have hc := congrArg φ hh
    rw [hphi, map_one] at hc
    exact congrArg Subtype.val hc
  have hYc : IsNonsplitDoubleCoverOfS5
      ↥(Subgroup.centralizer ({t''} : Set ↥S)) := by
    obtain ⟨e1⟩ := tableVII_centralizer_mulEquiv φ t''
    obtain ⟨e2, -⟩ := tableVII_cent_equiv htc
    have hmid : IsNonsplitDoubleCoverOfS5
        ↥(Subgroup.centralizer ({φ t''} : Set ↥(Gxy a c))) := by
      rw [hphi]
      exact hY.of_mulEquiv e2.symm
    exact hmid.of_mulEquiv e1.symm
  have hU : IsShapeU35 ↥S :=
    hS.simple_2S5 ↥(Gx a) E hE S hsimpS t'' ht''2 ht''1 hYc
  exact hU.of_mulEquiv φ

end CFSG.EvenSporadicStandard.HNRecog.Section3
