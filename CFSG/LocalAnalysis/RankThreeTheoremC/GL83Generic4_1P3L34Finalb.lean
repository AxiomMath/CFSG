module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem l34fin_le_pRank_of_le_map {C H : Subgroup G} {N : Subgroup C} [N.Normal]
    (hN : Nat.Coprime 3 (Nat.card N)) {E : Subgroup (C ⧸ N)} (hE : IsElemAbelian 3 E) {k : ℕ}
    (hEc : Nat.card E = 3 ^ k) (hEH : E ≤ (H.subgroupOf C).map (QuotientGroup.mk' N)) :
    k ≤ CFSG.pRank 3 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← pRank_subgroup_eq_internal_top 3 (by norm_num) H]
  have hfr : ((QuotientGroup.mk' N).comp (H.subgroupOf C).subtype).range =
      (H.subgroupOf C).map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.Coprime 3
      (Nat.card ((QuotientGroup.mk' N).comp (H.subgroupOf C).subtype).rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hN.coprime_dvd_right (Subgroup.card_comap_dvd_of_injective N (H.subgroupOf C).subtype
      (H.subgroupOf C).subtype_injective)
  have hEr : E ≤ ((QuotientGroup.mk' N).comp (H.subgroupOf C).subtype).range := hfr ▸ hEH
  have eE := Subgroup.subgroupOfEquivOfLe hEr
  have hE' : IsElemAbelian 3
      (E.subgroupOf ((QuotientGroup.mk' N).comp (H.subgroupOf C).subtype).range) :=
    elementary_transport 3 E _ eE.symm hE
  obtain ⟨L, -, ⟨eL⟩⟩ := coprime_kernel_lifts_pSubgroup 3 Nat.prime_three
    ((QuotientGroup.mk' N).comp (H.subgroupOf C).subtype).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _) hker _ (elementary_isPGroup 3 _ hE')
  have hφ : Function.Injective (C.subtype.comp (H.subgroupOf C).subtype) :=
    C.subtype_injective.comp (H.subgroupOf C).subtype_injective
  refine le_pRank_of_elemAbelian_card (E := L.map (C.subtype.comp (H.subgroupOf C).subtype)) ?_
    (elementary_map_injective 3 L _ hφ (elementary_transport 3 _ L eL.symm hE')) ?_
  · rintro _ ⟨l, -, rfl⟩
    exact Subgroup.mem_subgroupOf.mp l.2
  · rw [Subgroup.card_map_of_injective hφ, Nat.card_congr eL.toEquiv,
      Nat.card_congr eE.toEquiv, hEc]

theorem l34fin_commutator_mul {Y : Type*} [Group Y] {j₁ j₂ e₁ e₂ : Y} (h₁ : Commute e₁ j₂)
    (h₂ : Commute e₁ e₂) (h₃ : Commute e₂ j₁) : ⁅j₁ * e₁, j₂ * e₂⁆ = ⁅j₁, j₂⁆ := by
  have k₁ : e₁ * (j₂ * e₂) * e₁⁻¹ = j₂ * e₂ := by
    rw [(h₁.mul_right h₂).eq, mul_inv_cancel_right]
  have k₂ : e₂ * j₁⁻¹ * e₂⁻¹ = j₁⁻¹ := by
    rw [h₃.inv_right.eq, mul_inv_cancel_right]
  calc ⁅j₁ * e₁, j₂ * e₂⁆ = j₁ * (e₁ * (j₂ * e₂) * e₁⁻¹) * j₁⁻¹ * (j₂ * e₂)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = j₁ * (j₂ * (e₂ * j₁⁻¹ * e₂⁻¹)) * j₂⁻¹ := by rw [k₁]; group
    _ = ⁅j₁, j₂⁆ := by rw [k₂, commutatorElement_def]; group

theorem l34fin_bar_le (hS : Setting G) (hU0 : FullCoreLocal G) (hK1 : KFactL34TwoSignalizer)
    (hK2 : KFactL34Three) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL34Normal M x J) {H : Subgroup G} (hKH : l34Img x J J ≤ l34Img x J H) :
    r1sBar x J ≤ (H.subgroupOf (centralizer ({x} : Set G))).map
      (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)) := by
  have hDn := l34_reducedCentralizer_normal hJ
  have hDc := l34_reducedCentralizer_isCyclic hS hU0 hK1 hK2 hp hM hgen hJ
  have hJp := r1sBar_perfect_l34 hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set π : C →* GenericReduced 3 x := QuotientGroup.mk' (primeComplementCore (G := C) 3) with hπ
  set D : Subgroup (GenericReduced 3 x) := reducedCentralizerOfJ x J with hD
  set Hh : Subgroup (GenericReduced 3 x) := (H.subgroupOf C).map π with hHh
  have hDJ : D = centralizer ((r1sBar x J : Subgroup (GenericReduced 3 x)) :
      Set (GenericReduced 3 x)) := r1s_reducedCentralizerOfJ_eq x J
  have hlift : ∀ j ∈ r1sBar x J, ∃ e ∈ D, j * e ∈ Hh := by
    intro j hj
    have hqj : QuotientGroup.mk' D.normalCore j ∈ l34Img x J H :=
      hKH (by rw [l34Img_J_eq]; exact ⟨j, hj, rfl⟩)
    obtain ⟨c, hc, hcq⟩ := hqj
    have hcq' : QuotientGroup.mk' D.normalCore (π c) = QuotientGroup.mk' D.normalCore j := hcq
    refine ⟨j⁻¹ * π c, ?_, by rw [mul_inv_cancel_left]; exact ⟨c, hc, rfl⟩⟩
    have h1 : QuotientGroup.mk' D.normalCore (j⁻¹ * π c) = 1 := by
      rw [map_mul, map_inv, hcq', inv_mul_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.normalCore_eq_self] at h1
  have hcomm : ⁅r1sBar x J, r1sBar x J⁆ ≤ Hh := by
    rw [Subgroup.commutator_le]
    intro j₁ hj₁ j₂ hj₂
    obtain ⟨e₁, he₁, hh₁⟩ := hlift j₁ hj₁
    obtain ⟨e₂, he₂, hh₂⟩ := hlift j₂ hj₂
    have he₁' : e₁ ∈ centralizer ((r1sBar x J : Subgroup (GenericReduced 3 x)) :
        Set (GenericReduced 3 x)) := hDJ ▸ he₁
    have he₂' : e₂ ∈ centralizer ((r1sBar x J : Subgroup (GenericReduced 3 x)) :
        Set (GenericReduced 3 x)) := hDJ ▸ he₂
    have c₁ : Commute e₁ j₂ := (mem_centralizer_iff.mp he₁' j₂ hj₂).symm
    have c₂ : Commute e₁ e₂ :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥D)).comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
    have c₃ : Commute e₂ j₁ := (mem_centralizer_iff.mp he₂' j₁ hj₁).symm
    rw [← l34fin_commutator_mul c₁ c₂ c₃, commutatorElement_def]
    exact Hh.mul_mem (Hh.mul_mem (Hh.mul_mem hh₁ hh₂) (Hh.inv_mem hh₁)) (Hh.inv_mem hh₂)
  rwa [Subgroup.commutator_eq_self] at hcomm

end CFSG.LocalAnalysis.RankThreeTheoremC
