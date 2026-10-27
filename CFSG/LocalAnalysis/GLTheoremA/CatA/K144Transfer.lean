module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind)

theorem inner_of_innDiagKind {K : Type} [Group K] (hq : CFSG.Open.IsQuasisimple K) {α : MulAut K}
    {labK : GLALabel} (h : InnDiagKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α)) :
    I144Inner K α := by
  have hcen := center_centerQuot_eq_bot hq
  obtain ⟨-, lab, hlam, hraw⟩ := h
  refine ⟨hq.1, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, -, u, hu, hind⟩
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).symm.trans θ, u, hu, ?_⟩
  intro k k' hkk'
  subst hkk'
  have h1 := hind (QuotientGroup.mk k) (QuotientGroup.mk (α k)) (centerQuotAut_mk K α k).symm
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  have e1 : (CanonInn.quotCenterEquivOfBot hcen).symm (QuotientGroup.mk k) =
      QuotientGroup.mk (QuotientGroup.mk k) := by
    rw [MulEquiv.symm_apply_eq, CanonInn.quotCenterEquivOfBot_mk]
  have e2 : (CanonInn.quotCenterEquivOfBot hcen).symm (QuotientGroup.mk (α k)) =
      QuotientGroup.mk (QuotientGroup.mk (α k)) := by
    rw [MulEquiv.symm_apply_eq, CanonInn.quotCenterEquivOfBot_mk]
  rw [e1, e2]
  exact h1

theorem centerQuot_component {K : Type} [Group K] [Finite K] {α : MulAut K} (hα : α ^ 3 = 1)
    {J : Subgroup K} (hJ : GLAPComponent 3 (fixSubgroup α) J) :
    centerQuotAut K α ^ 3 = 1 ∧
      GLAPComponent 3 (fixSubgroup (centerQuotAut K α))
        (J.map (QuotientGroup.mk' (Subgroup.center K))) ∧
      Nonempty (PSimple 3 J ≃* PSimple 3 (J.map (QuotientGroup.mk' (Subgroup.center K)))) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hJb : GLAPComponent 3 (fixSubgroup (centerQuotAut K α))
      (J.map (QuotientGroup.mk' (Subgroup.center K))) :=
    glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center K))
      (by rw [QuotientGroup.ker_mk']) α (centerQuotAut K α)
      (fun k => (centerQuotAut_mk K α k).symm) (QuotientGroup.mk'_surjective _) hp hJ
  exact ⟨by rw [← map_pow, hα, map_one], hJb,
    nonempty_pSimple_equiv_map hp (QuotientGroup.mk' (Subgroup.center K)) hJ hJb⟩

end CFSG.LocalAnalysis.GLTheoremA.K144
