module

public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
public import CFSG.FeitThompson.Representations.TIDadeMapEqualsInduction
import CFSG.FeitThompson.Representations.TISetDadeData

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {L : Subgroup G} {A D : Set G} {H : G → Subgroup G}

theorem isClassFun_of_mem_classFun {f : G → ℂ} (hf : f ∈ classFun G) : IsClassFun f :=
  isClassFun_iff.2 fun x _ => mem_classFun.1 hf _ _ (isConj_iff.2 ⟨x, rfl⟩).symm

theorem dadeDomain_mono (h : D ⊆ A) : dadeDomain L D ≤ dadeDomain L A := fun _ hf =>
  mem_dadeDomain.2 ⟨(mem_dadeDomain.1 hf).1,
    fun x hx => (mem_dadeDomain.1 hf).2 x fun hxD => hx (h hxD)⟩

theorem isTIWithNormalizer_of_stabilizer_eq (hne : D.Nonempty) (h1 : (1 : G) ∉ D)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' D = D ↔ g ∈ L)
    (hdisj : ∀ g : G, g ∉ L → D ∩ (fun x => g⁻¹ * x * g) '' D = ∅) :
    IsTIWithNormalizer D L where
  nonempty := hne
  one_notMem := h1
  normalizer_eq := by
    ext g
    rw [mem_normalizer_iff_conjInv_image_eq, hstab]
  disjoint_conj_image g hg := by
    have hg' : g⁻¹ ∉ L := fun hc => hg (by simpa using inv_mem hc)
    have key : (fun x => (g⁻¹)⁻¹ * x * g⁻¹) '' D = MulAut.conj g '' D :=
      Set.image_congr' fun x => by simp
    rw [Set.disjoint_iff_inter_eq_empty, ← key]
    exact hdisj g⁻¹ hg'

section Finite

variable [Finite G]

theorem IsDadeData.eq_bot_of_mem_tiSubset (hD : IsDadeData L A H) (hTI : IsTIWithNormalizer D L)
    (hDA : D ⊆ A) {d : G} (hd : d ∈ D) : H d = ⊥ := by
  have h1 : H d ⊓ (L ⊓ Subgroup.centralizer ({d} : Set G)) = ⊥ := hD.inf_eq_bot (hDA hd)
  rw [hTI.inf_centralizer_eq hd] at h1
  rw [← h1]
  exact (inf_eq_left.2 (hD.le_centralizer (hDA hd))).symm

theorem dadeCoset_eq_singleton_of_mem_tiSubset (hD : IsDadeData L A H)
    (hTI : IsTIWithNormalizer D L) (hDA : D ⊆ A) {d : G} (hd : d ∈ D) :
    dadeCoset H d = {d} := by
  ext x
  rw [mem_dadeCoset_iff, hD.eq_bot_of_mem_tiSubset hTI hDA hd, Subgroup.mem_bot, mul_inv_eq_one,
    Set.mem_singleton_iff]

theorem dadeSupport_eq_setOf_isConj_of_mem_tiSubset (hD : IsDadeData L A H)
    (hTI : IsTIWithNormalizer D L) (hDA : D ⊆ A) {d : G} (hd : d ∈ D) :
    dadeSupport H d = {x | IsConj d x} := by
  ext x
  rw [mem_dadeSupport_iff, dadeCoset_eq_singleton_of_mem_tiSubset hD hTI hDA hd]
  simp

theorem dadeMap_eq_tiDadeMap (hD : IsDadeData L A H) (hTI : IsTIWithNormalizer D L)
    (hDA : D ⊆ A) (f : ↥L → ℂ) (hf : f ∈ dadeDomain L D) :
    ((dadeMap hD ⟨f, dadeDomain_mono hDA hf⟩ : classFun G) : G → ℂ) = tiDadeMap D L f := by
  have hfc : IsClassFun f := isClassFun_of_mem_classFun (mem_dadeDomain.1 hf).1
  funext x
  by_cases hx : ∃ d : ↥L, (d : G) ∈ D ∧ IsConj (d : G) x
  · obtain ⟨d, hdD, hdx⟩ := hx
    rw [tiDadeMap_apply_of_isConj hTI hfc d hdD hdx,
      dadeMap_apply_of_mem_dadeSupport hD _ (hDA hdD)
        (mem_dadeSupport_iff.2 ⟨d, self_mem_dadeCoset H _, hdx⟩)]
  · rw [tiDadeMap_eq_zero fun y hy hyx => hx ⟨y, hy, hyx⟩]
    by_cases hxD : x ∈ totalDadeSupport A H
    · obtain ⟨a, ha, hxa⟩ := mem_totalDadeSupport_iff.1 hxD
      rw [dadeMap_apply_of_mem_dadeSupport hD _ ha hxa]
      by_cases haD : a ∈ D
      · exact absurd ⟨⟨a, hD.mem_of_mem ha⟩, haD, by
          rwa [dadeSupport_eq_setOf_isConj_of_mem_tiSubset hD hTI hDA haD] at hxa⟩ hx
      · exact (mem_dadeDomain.1 hf).2 _ haD
    · exact dadeMap_eq_zero_of_notMem hD _ hxD

end Finite

theorem dadeMap_eq_indClassFun [Fintype G] (hD : IsDadeData L A H)
    (hTI : IsTIWithNormalizer D L) (hDA : D ⊆ A) (f : ↥L → ℂ) (hf : f ∈ dadeDomain L D) :
    ((dadeMap hD ⟨f, dadeDomain_mono hDA hf⟩ : classFun G) : G → ℂ) = indClassFun L f := by
  rw [dadeMap_eq_tiDadeMap hD hTI hDA f hf]
  exact tiDadeMap_eq_indClassFun hTI (isClassFun_of_mem_classFun (mem_dadeDomain.1 hf).1)
    (mem_dadeDomain.1 hf).2

theorem dadeMap_apply_eq_indClassFun_apply [Fintype G] (hD : IsDadeData L A H)
    (hTI : IsTIWithNormalizer D L) (hDA : D ⊆ A) (f : ↥L → ℂ) (hf : f ∈ dadeDomain L D) (x : G) :
    ((dadeMap hD ⟨f, dadeDomain_mono hDA hf⟩ : classFun G) : G → ℂ) x = indClassFun L f x :=
  congrFun (dadeMap_eq_indClassFun hD hTI hDA f hf) x

theorem dadeMap_eq_indClassFun_of_stabilizer_eq [Fintype G] (hD : IsDadeData L A H)
    (hDA : D ⊆ A) (hne : D.Nonempty)
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' D = D ↔ g ∈ L)
    (hdisj : ∀ g : G, g ∉ L → D ∩ (fun x => g⁻¹ * x * g) '' D = ∅)
    (f : ↥L → ℂ) (hf : f ∈ dadeDomain L D) :
    ((dadeMap hD ⟨f, dadeDomain_mono hDA hf⟩ : classFun G) : G → ℂ) = indClassFun L f :=
  dadeMap_eq_indClassFun hD
    (isTIWithNormalizer_of_stabilizer_eq hne (fun h1 => hD.one_notMem (hDA h1)) hstab hdisj)
    hDA f hf

end CFSG.FeitThompson

end
