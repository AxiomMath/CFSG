module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA (InnerOn)
open CFSG.LocalAnalysis.GLTheoremA.S10

theorem inducesInnerMod_of_innerOn {G : Type} [Group G] {p : ℕ} {J : Subgroup G} {b : G}
    (h : InnerOn J b) : InducesInnerMod p J b := by
  obtain ⟨a, ha, hconj⟩ := h
  refine ⟨a, ha, fun y hy => ?_⟩
  have h1 := hconj (a⁻¹ * y * a) (J.mul_mem (J.mul_mem (J.inv_mem ha) hy) ha)
  have h2 : b * (a⁻¹ * y * a) * b⁻¹ = y := by rw [h1]; group
  have h3 : b⁻¹ * y * b = a⁻¹ * y * a := by
    calc b⁻¹ * y * b = b⁻¹ * (b * (a⁻¹ * y * a) * b⁻¹) * b := by rw [h2]
      _ = a⁻¹ * y * a := by group
  rw [h3]
  group
  exact Subgroup.one_mem _

section Certificates

theorem innDiagOn_of_innerOn {G : Type} [Group G] [Finite G] {p : ℕ} {X J : Subgroup G} {b : G}
    (hp : p.Prime) (hcomp : GLAPComponent p X J) (hchev : IsChevSimple 2 (PSimple p J))
    (hb : b ∈ Subgroup.normalizer (J : Set G)) (h : InnerOn J b) :
    InnDiagOn p (Subgroup.zpowers b) J :=
  CFSG.LocalAnalysis.GLTheoremA.MI.inner_innDiag_holds hp hcomp hchev hb
    (inducesInnerMod_of_innerOn h)

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
