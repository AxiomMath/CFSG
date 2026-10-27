module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11d2_a_facts [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} {a x : G} (hax : Sec11Ax G t L S z K1 K2 T R a x) :
    a ∈ R ∧ a * a = 1 ∧ a ∈ normalizer (secQ K1 K2 : Set G) ∧ a * z = z * a ∧
      ∀ y ∈ secD K1 K2 R, a * y * a⁻¹ ∈ secD K1 K2 R := by
  have hctx : Sec11Ctx G t L S z K1 K2 T R := hax.toSec11Ctx
  obtain ⟨hAS, -, hAe⟩ := sec126_isElemAb2_secA hp hctx.toSec10Z
  have haR : a ∈ R := hctx.T_le (hctx.S_le (hAS hax.a_mem))
  have haa : a * a = 1 := by
    have h := hAe.1.2 a hax.a_mem
    simpa [pow_two] using h
  have haN : a ∈ normalizer (secQ K1 K2 : Set G) := hctx.sylowR.1 haR
  have haz : a * z = z * a :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (sec11_normalizer_Q_le_centralizer_z hp hctx.toSec10Ctx haN)
  refine ⟨haR, haa, haN, haz, fun y hy => ?_⟩
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr fun w hw => ?_,
    R.mul_mem (R.mul_mem haR (Subgroup.mem_inf.mp hy).2) (R.inv_mem haR)⟩
  have hw' : a⁻¹ * w * a ∈ secQ K1 K2 := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) w).mp hw
    simpa using h
  have hyc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).1 _ hw'
  calc w * (a * y * a⁻¹) = a * ((a⁻¹ * w * a) * y) * a⁻¹ := by group
    _ = a * (y * (a⁻¹ * w * a)) * a⁻¹ := by rw [hyc]
    _ = (a * y * a⁻¹) * w := by group

end CFSG.OddStandard.SmallF3.Omega
