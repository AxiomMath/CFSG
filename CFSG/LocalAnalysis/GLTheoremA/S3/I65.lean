module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KData
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.HardMathSupport.Solomon.LocalBalance.BarAut
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner centerQuotient_conj)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom centerQuotientHom_injective)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)

private theorem i65_inducesInnerMod_of_inner {G : Type} [Group G] {p : ℕ} {J : Subgroup G}
    [Group.IsPerfect (PQuot p J)] {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (h : centerQuotientHom (PQuot p J) (barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩) ∈
      inner (PSimple p J)) : InducesInnerMod p J g := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot p J)) m
  have hu : barAut p J ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ = MulAut.conj u :=
    (centerQuotientHom_injective (PQuot p J)) (hm.symm.trans (centerQuotient_conj u).symm)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective u
  set γ : ↥(Subgroup.normalizer (J : Set G)) := ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ with hγ
  refine ⟨((w : ↥J) : G)⁻¹, J.inv_mem w.2, fun y hy => ?_⟩
  have hs : ∀ y : ↥J, ((J.normalizerMonoidHom γ y : ↥J) : G) = g⁻¹ * y * g := fun y => by
    change (g⁻¹ : G) * y * (g⁻¹)⁻¹ = _
    rw [inv_inv]
  have h1 : barAut p J γ (QuotientGroup.mk ⟨y, hy⟩) =
      QuotientGroup.mk (w * ⟨y, hy⟩ * w⁻¹) := by
    rw [hu, MulAut.conj_apply]
    rfl
  rw [barAut_mk] at h1
  have h2 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) ∈
      GLAPPrimeCoreOf p J :=
    Subgroup.mem_map_of_mem J.subtype (QuotientGroup.eq.1 h1.symm)
  have h3 : (((w * ⟨y, hy⟩ * w⁻¹)⁻¹ * J.normalizerMonoidHom γ ⟨y, hy⟩ : ↥J) : G) =
      (((w : G)⁻¹)⁻¹ * y * (w : G)⁻¹)⁻¹ * (g⁻¹ * y * g) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hs, inv_inv]
  rwa [h3] at h2

theorem i65At_of {G : Type} [Group G] [Finite G] {p : ℕ} (h : KD65 p) : I65At G p := by
  unfold I65At
  intro hp _hp2 X K _hX hK hchev hex
  obtain ⟨a, ha, hap, _, hni⟩ := hex
  have hq : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  haveI : Group.IsPerfect (PQuot p K) := ⟨hq.1⟩
  have hsimple : IsSimpleGroup (PSimple p K) := hq.2
  have hnonab : ∃ x y : PSimple p K, x * y ≠ y * x :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  have hcenter : IsPGroup p (Subgroup.center (PQuot p K)) := I2611.isPGroup_center_pQuot' hp K
  set γ : ↥(Subgroup.normalizer (K : Set G)) := ⟨a⁻¹, Subgroup.inv_mem _ ha⟩ with hγ
  have hγp : γ ^ p = 1 := Subtype.ext (by simp [hγ, inv_pow, hap])
  refine h (PSimple p K) hsimple hnonab hchev
    ⟨centerQuotientHom (PQuot p K) (barAut p K γ), ?_,
      fun hmem => hni (i65_inducesInnerMod_of_inner ha hmem)⟩
    (PQuot p K) hq hcenter ⟨MulEquiv.refl _⟩
  rw [← map_pow, ← map_pow, hγp, map_one, map_one]

end CFSG.LocalAnalysis.GLTheoremA
