module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcToralRigid
public import CFSG.LieType.AlgebraicGroups.KernelRootBruhat

public section

namespace CFSG.LieType.AlgebraicGroups

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.Foote5.OddLieCore.Exc
open scoped Pointwise


theorem mem_torusGroup_of_bruhat_factor_of_commute_kernelSpan
    {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (ζ : Kˣ) (hζ : ζ ^ 2 ≠ 1) {z : ModGL τ K}
    (hzAdj : z ∈ adjointGroup τ K)
    (hcomm : ∀ x ∈ rootSpan τ K (kernelRoots (rootCharHom a)), Commute z x)
    {w : WeylGroup τ} {h u v : ModGL τ K} (hh' : h ∈ torusGroup τ K)
    (hu : u ∈ rootSpan τ K (rootCharKernel a ∩ {β | IsRoot τ β ∧ 0 < height β}))
    (hv : v ∈ rootSpan τ K (rootCharKernel a ∩ inversionSet w))
    (hzfactor : z = h * u * canonicalRep (coxeterSystem τ) K w * v)
    (hfixer : (∀ β ∈ posRoots (kernelRoots (rootCharHom a)), w • β = β) → w = 1) :
    z ∈ torusGroup τ K := by
  classical
  let Sigma := kernelRoots (rootCharHom a)
  let P := posRoots Sigma
  have huPos : u ∈ posUnipotent τ K := rootSpan_mono Set.inter_subset_right hu
  have hvInv : v ∈ rootSpan τ K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have hrootTorus : ∀ β : Fin τ.rank → ℤ, ∃ b : Fin τ.rank → Kˣ,
      IsRoot τ β → rootTorusSL2 τ K β ζ = rootDiagUnit τ b ∧
        rootChar b β = ζ ^ 2 := by
    intro β
    by_cases hr : IsRoot τ β
    · obtain ⟨b, hb, hchar⟩ := exists_rootTorusSL2_eq_rootDiagUnit hr ζ
      exact ⟨b, fun _ => ⟨hb, hchar⟩⟩
    · exact ⟨1, fun h => (hr h).elim⟩
  choose A hA using hrootTorus
  have hzTor : ∀ β ∈ Sigma, z ∈ toralCentralizer τ K (A β) := by
    intro β hβ
    have hpos : ∀ c, z * pinnedX τ K β c = pinnedX τ K β c * z :=
      fun c => (hcomm _ (pinnedX_mem_rootSpan hβ c)).eq
    have hneg : ∀ c, z * pinnedX τ K (-β) c = pinnedX τ K (-β) c * z :=
      fun c => (hcomm _ (pinnedX_mem_rootSpan (neg_mem_rootCharKernel hβ) c)).eq
    have h := commute_rootSL2_of_commute hβ.1 hpos hneg (HSL ζ)
    change z * rootTorusSL2 τ K β ζ = rootTorusSL2 τ K β ζ * z at h
    rw [(hA β hβ.1).1] at h
    exact ⟨hzAdj, Subgroup.mem_centralizer_singleton_iff.mpr h⟩
  have hparts := fun β (hβ : β ∈ Sigma) =>
    conj_eq_of_mem_toralCentralizer_bruhat (A β) (hzTor β hβ)
      hh' huPos hvInv hzfactor
  have huOne : u = 1 := by
    exact eq_one_of_conj_rootDiagUnit_eq (fun β hb => hb.2)
      (closedRoots_inter closedRoots_pos) hu A (fun β hb => (hparts β hb.1).1)
      (fun β hb => by rw [(hA β hb.1.1).2]; exact hζ)
  have hvOne : v = 1 := by
    exact eq_one_of_conj_rootDiagUnit_eq (fun β hb => inversionSet_pos hb.2)
      (closedRoots_inter (closedRoots_inversionSet w)) hv A
      (fun β hb => (hparts β hb.1).2)
      (fun β hb => by rw [(hA β hb.1.1).2]; exact hζ)
  have hwfix : ∀ β ∈ P, w • β = β := by
    intro β hβ
    have hβRoot : IsRoot τ β := hβ.1.1
    have hzshort : z = h * canonicalRep (coxeterSystem τ) K w := by
      simpa only [huOne, hvOne, mul_one] using hzfactor
    have hfix : z * pinnedX τ K β 1 * z⁻¹ = pinnedX τ K β 1 := by
      rw [(hcomm _ (pinnedX_mem_rootSpan hβ.1 1)).eq]
      group
    have hmem : z * pinnedX τ K β 1 * z⁻¹ ∈ rootSubgroup τ K (w • β) := by
      rw [hzshort]
      have e : (h * canonicalRep (coxeterSystem τ) K w) *
          pinnedX τ K β 1 * (h *
          canonicalRep (coxeterSystem τ) K w)⁻¹ =
          h * (canonicalRep (coxeterSystem τ) K w *
          pinnedX τ K β 1 * (canonicalRep (coxeterSystem τ) K w)⁻¹) *
          h⁻¹ := by group
      rw [e]
      have htransport : canonicalRep (coxeterSystem τ) K w * pinnedX τ K β 1 *
          (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ rootSubgroup τ K (w • β) := by
        rw [← (canonical_weyl_root_transport τ K).2.1 w β hβRoot]
        exact Subgroup.mem_map_of_mem _ (mem_rootSubgroup.mpr ⟨1, rfl⟩)
      exact (Subgroup.mem_normalizer_iff.mp
        (torusGroup_le_normalizer_rootSubgroup (IsRoot.smul hβRoot w) hh') _).1 htransport
    rw [hfix] at hmem
    obtain ⟨c, hc⟩ := mem_rootSubgroup.mp hmem
    exact eq_of_pinnedX_eq_pinnedX_of_pos' (IsRoot.smul hβRoot w) hβRoot hβ.2
      one_ne_zero hc
  have hwOne : w = 1 := hfixer hwfix
  rw [huOne, hvOne, hwOne, canonicalRep_one, mul_one, mul_one, mul_one] at hzfactor
  rw [hzfactor]
  exact hh'

theorem mem_torusGroup_of_mem_toralRootGroup_of_commute
    {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (ζ : Kˣ) (hζ : ζ ^ 2 ≠ 1)
    {z : ModGL τ K} (hz : z ∈ toralRootGroup τ K a)
    (hcomm : ∀ x ∈ rootSpan τ K (kernelRoots (rootCharHom a)), Commute z x) :
    z ∈ torusGroup τ K := by
  classical
  let Sigma := kernelRoots (rootCharHom a)
  let P := posRoots Sigma
  have hzAdj : z ∈ adjointGroup τ K := (toralRootGroup_le a hz).1
  have hnorm : torusGroup τ K ≤ Subgroup.normalizer
      (rootSpan τ K Sigma : Set (ModGL τ K)) :=
    torusGroup_le_normalizer_rootSpan (fun _ h => h.1)
  have hproduct := Subgroup.coe_mul_of_left_le_normalizer_right
    (torusGroup τ K) (rootSpan τ K Sigma) hnorm
  have hz' : z ∈ (torusGroup τ K : Set (ModGL τ K)) *
      (rootSpan τ K Sigma : Set (ModGL τ K)) := by
    rw [← hproduct]
    exact hz
  obtain ⟨t, ht, s, hs, hst⟩ := hz'
  obtain ⟨w, hw, h, hh, u, hu, v, hv, hsu⟩ :=
    exists_kernelRoots_bruhat_factor (rootCharHom a) hs
  have hzfactor : z = (t * h) * u * canonicalRep (coxeterSystem τ) K w * v := by
    rw [← hst, hsu]
    group
  have hh' : t * h ∈ torusGroup τ K := mul_mem ht hh
  change u ∈ rootSpan τ K P at hu
  change v ∈ rootSpan τ K {β | β ∈ P ∧ height (w • β) < 0} at hv
  have hP : P = rootCharKernel a ∩ {β | IsRoot τ β ∧ 0 < height β} := by
    ext β
    exact ⟨fun hb => ⟨hb.1, hb.1.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
  have hI : {β | β ∈ P ∧ height (w • β) < 0} =
      rootCharKernel a ∩ inversionSet w := by
    ext β
    constructor
    · rintro ⟨hβ, hneg⟩
      exact ⟨hβ.1, hβ.1.1, hβ.2, (IsRoot.smul hβ.1.1 w), hneg⟩
    · rintro ⟨hβ, hroot, hpos, _, hneg⟩
      exact ⟨⟨hβ, hpos⟩, hneg⟩
  rw [hP] at hu
  rw [hI] at hv
  apply mem_torusGroup_of_bruhat_factor_of_commute_kernelSpan a ζ hζ hzAdj hcomm
    hh' hu hv hzfactor
  intro hwfix
  have hwKernel : w ∈ kernelWeylGroup (rootCharHom a) := by
    rw [kernelWeylGroup_eq_closure]
    exact hw
  exact eq_one_of_mem_kernelWeylGroup hwKernel
    (fun β hb => by rw [hwfix β hb]; exact hb)

end CFSG.LieType.AlgebraicGroups
