module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOne
public import CFSG.GroupTheory.Fitting.LayerContainment
import CFSG.LieType.HighestRoot.CentChevalleyToral

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup

theorem perfect_le_layer_sup_centralizer {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hP : ⁅P, P⁆ = P)
    (hcomp : ∀ C : Subgroup X, CFSG.IsComponent C →
      P ≤ C ⊔ Subgroup.centralizer (C : Set X)) :
    P ≤ CFSG.layer X ⊔ Subgroup.centralizer (CFSG.layer X : Set X) := by
  have hinner : ∀ (k : X) (_ : k ∈ P) (C : Subgroup X), Open.IsComponentOf C ⊤ →
      ∃ c ∈ C, ∀ m ∈ C, k * m * k⁻¹ = c * m * c⁻¹ := by
    intro k hk C hC
    exact CFSG.GroupTheory.exists_forall_conj_eq_of_mem_sup_centralizer (C := C) (k := k)
      (hcomp C ((CFSG.isComponent_iff_open C).mpr hC) hk)
  have hproduct : P ≤ CFSG.ComponentClassification.Layer.subgroup X ⊔
      Subgroup.centralizer (CFSG.ComponentClassification.Layer.subgroup X : Set X) := by
    intro k hk
    obtain ⟨e, he, haction⟩ :=
      CFSG.ComponentClassification.ComponentInnerActions.exists_layer_implementer k
        (fun C hC => hinner k hk C hC)
    have hcentralizes : e⁻¹ * k ∈
        Subgroup.centralizer
          (CFSG.ComponentClassification.Layer.subgroup X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have heq := congrArg (fun value : X => e⁻¹ * value * k) (haction m hm)
      calc
        m * (e⁻¹ * k) = e⁻¹ * (e * m * e⁻¹) * k := by group
        _ = e⁻¹ * (k * m * k⁻¹) * k := heq.symm
        _ = (e⁻¹ * k) * m := by group
    have hk_eq : e * (e⁻¹ * k) = k := by group
    rw [← hk_eq]
    exact Subgroup.mul_mem_sup he hcentralizes
  simpa only [CFSG.layer_eq_componentClassification] using hproduct

theorem perfect_le_sup_centralizer_of_isComponent {X : Type} [Group X] [Finite X]
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (hKX : CFSG.Open.IsKGroup X) {I : Subgroup X} (hperf : ⁅I, I⁆ = I)
    {C : Subgroup X} (hC : CFSG.IsComponent C)
    (hIY : I ≤ Subgroup.normalizer (C : Set X)) :
    I ≤ C ⊔ Subgroup.centralizer (C : Set X) := by
  let Y : Subgroup X := Subgroup.normalizer (C : Set X)
  have hIY' : I ≤ Y := hIY
  have hKY : CFSG.Open.IsKGroup ↥Y := hKX.subgroup Y
  let L : Subgroup ↥Y := C.subgroupOf Y
  have hLcomp : CFSG.IsComponent L :=
    CFSG.LocalCores.component_overgroup hC
      (Subgroup.le_normalizer : C ≤ Subgroup.normalizer (C : Set X))
  have hLnorm : L.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.le_normalizer : C ≤ Subgroup.normalizer (C : Set X))).mpr le_rfl
  obtain ⟨n, hn⟩ := h711 ↥Y hKY L hLcomp hLnorm
  have hperfI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr hperf
  have hperfY : Group.IsPerfect ↥(I.subgroupOf Y) :=
    Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hIY').symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hIY').symm.surjective
  have hIder : I.subgroupOf Y ≤ derivedSeries ↥Y n :=
    CFSG.LieType.HighestRoot.le_derivedSeries_of_isPerfect hperfY n
  have hle : I.subgroupOf Y ≤ L ⊔ Subgroup.centralizer (L : Set ↥Y) := hIder.trans hn
  have hmap := Subgroup.map_mono (f := Y.subtype) hle
  have hleft : Subgroup.map Y.subtype (I.subgroupOf Y) = I :=
    Subgroup.map_subgroupOf_eq_of_le hIY'
  have hright : Subgroup.map Y.subtype (L ⊔ Subgroup.centralizer (L : Set ↥Y)) ≤
      C ⊔ Subgroup.centralizer (C : Set X) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.map_subgroupOf_eq_of_le
        (Subgroup.le_normalizer : C ≤ Subgroup.normalizer (C : Set X))]
      exact le_sup_left
    · rintro x ⟨z, hz, rfl⟩
      refine Subgroup.mem_sup_right ?_
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hcY : (⟨c, (Subgroup.le_normalizer :
          C ≤ Subgroup.normalizer (C : Set X)) hc⟩ : ↥Y) ∈ L := hc
      have hcomm := Subgroup.mem_centralizer_iff.mp hz
        (⟨c, (Subgroup.le_normalizer :
          C ≤ Subgroup.normalizer (C : Set X)) hc⟩ : ↥Y) hcY
      exact congrArg Subtype.val hcomm
  rw [hleft] at hmap
  exact hmap.trans hright

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
