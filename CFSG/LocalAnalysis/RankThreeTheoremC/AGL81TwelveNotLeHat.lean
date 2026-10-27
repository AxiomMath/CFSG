module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs
public import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
import CFSG.HardMathSupport.Cooperstein.Proving.TwoCoreInf
import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

open CFSG.Open CFSG.AGLEmbedding CFSG.HardMathSupport.Cooperstein.Proving Subgroup

variable {G : Type} [Group G] [Finite G] {M D : Subgroup G}

theorem inf_pCoreOf_le_of_le (hDM : D ≤ M) : D ⊓ pCoreOf 2 M ≤ pCoreOf 2 D := by
  intro x hx
  obtain ⟨hxD, hxT⟩ := mem_inf.mp hx
  obtain ⟨y, hy, hyx⟩ := mem_pCoreOf_iff.mp hxT
  let ι : ↥D →* ↥M := inclusion hDM
  let N : Subgroup ↥D := (CFSG.pCore 2 ↥M).comap ι
  have hNn : N.Normal := (CFSG.pCore_normal (p := 2) (G := ↥M)).comap ι
  have hNp : IsPGroup 2 ↥N :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).comap_of_injective ι (inclusion_injective _)
  have hN : N ≤ CFSG.pCore 2 ↥D := le_sSup ⟨hNn, hNp⟩
  have hz : (⟨x, hxD⟩ : ↥D) ∈ N := by
    show ι ⟨x, hxD⟩ ∈ CFSG.pCore 2 ↥M
    have : ι ⟨x, hxD⟩ = y := Subtype.ext hyx.symm
    rw [this]
    exact hy
  exact mem_pCoreOf_iff.mpr ⟨⟨x, hxD⟩, hN hz, rfl⟩

theorem barMHomSub_mem_pCore_iff (hDM : D ≤ M) (d : ↥D) :
    barMHomSub hDM d ∈ CFSG.pCore 2 ↥(barM M D) ↔ (d : G) ∈ pCoreOf 2 D := by
  have hP : pCoreOf 2 (barM M D) = barM M (pCoreOf 2 D) :=
    le_antisymm (pCoreOf_barM_le_barM_pCoreOf hDM) (barM_pCoreOf_le_pCoreOf_barM hDM)
  have h1 : barMHomSub hDM d ∈ CFSG.pCore 2 ↥(barM M D) ↔
      ((barMHomSub hDM d : ↥(barM M D)) : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ pCoreOf 2 (barM M D) := by
    rw [mem_pCoreOf_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨z, hz, hzd⟩
      rwa [← Subtype.ext hzd]
  rw [h1, hP, coe_barMHomSub]
  constructor
  · rintro ⟨m, hm₀, hmd⟩
    have hm : (m : G) ∈ pCoreOf 2 D := hm₀
    have hq : (m : ↥M)⁻¹ * inclusion hDM d ∈ CFSG.pCore 2 ↥M := by
      rw [← QuotientGroup.eq]
      exact hmd
    have hdM : ((m : G))⁻¹ * (d : G) ∈ D ⊓ pCoreOf 2 M := by
      refine ⟨D.mul_mem (D.inv_mem
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 D hm)) d.2, ?_⟩
      exact mem_pCoreOf_iff.mpr ⟨_, hq, rfl⟩
    have h2 := inf_pCoreOf_le_of_le hDM hdM
    have he : (d : G) = (m : G) * ((m : G)⁻¹ * (d : G)) := by group
    rw [he]
    exact (pCoreOf 2 D).mul_mem hm h2
  · intro hd
    exact ⟨inclusion hDM d, mem_subgroupOf.mpr hd, rfl⟩

theorem le_sup_pCoreOf_of_hatOf_eq (hDM : D ≤ M) {X Y : Subgroup G} (hXD : X ≤ D)
    (hYD : Y ≤ D) (h : hatOf (barM M D) (barM M X) = hatOf (barM M D) (barM M Y)) :
    X ≤ Y ⊔ pCoreOf 2 D := by
  intro x hx
  have hxP : barMHomSub hDM ⟨x, hXD hx⟩ ∈ (barM M X).subgroupOf (barM M D) := by
    rw [subgroupOf_barM_eq_map hDM hXD]
    exact mem_map.mpr ⟨⟨x, hXD hx⟩, mem_subgroupOf.mpr hx, rfl⟩
  have hxhat : QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M D)) (barMHomSub hDM ⟨x, hXD hx⟩) ∈
      hatOf (barM M D) (barM M Y) := h ▸ mem_map.mpr ⟨_, hxP, rfl⟩
  obtain ⟨w, hw, hwx⟩ := mem_map.mp hxhat
  rw [subgroupOf_barM_eq_map hDM hYD] at hw
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hw
  have hyY : (y : G) ∈ Y := mem_subgroupOf.mp hy
  have hq : (barMHomSub hDM y)⁻¹ * barMHomSub hDM ⟨x, hXD hx⟩ ∈ CFSG.pCore 2 ↥(barM M D) := by
    rw [← QuotientGroup.eq]
    exact hwx
  rw [← map_inv, ← map_mul, barMHomSub_mem_pCore_iff] at hq
  have he : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [he]
  exact mul_mem_sup hyY (by simpa using hq)

theorem isSubnormal_hatOf (hDM : D ≤ M) {X : Subgroup G} (hX : IsSubnormal X D) :
    IsSubnormal (hatOf (barM M D) (barM M X)) ⊤ := by
  have h1 : IsSubnormal (barM M X) (barM M D) :=
    (hX.comap M.subtype).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
  have h2 := h1.comap (barM M D).subtype
  rw [comap_subtype, comap_subtype, subgroupOf_self] at h2
  have h3 := h2.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M D)))
  rwa [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3

theorem inf_pCoreOf_eq_of_isSubnormal {X : Subgroup G} (hX : IsSubnormal X D) :
    X ⊓ pCoreOf 2 D = pCoreOf 2 X :=
  le_antisymm (inf_pCoreOf_le_of_le hX.le)
    (le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 X)
      (pCoreOf_le_pCoreOf_of_isSubnormal 2 hX))

theorem nonempty_hatOf_mulEquiv (hDM : D ≤ M) {X : Subgroup G} (hXD : X ≤ D)
    (hO : X ⊓ pCoreOf 2 D = pCoreOf 2 X) :
    Nonempty (↥(hatOf (barM M D) (barM M X)) ≃* ↥X ⧸ CFSG.pCore 2 ↥X) := by
  set φ : ↥X →* ↥(barM M D) ⧸ CFSG.pCore 2 ↥(barM M D) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(barM M D))).comp
      ((barMHomSub hDM).comp (inclusion hXD)) with hφ
  have hrange : φ.range = hatOf (barM M D) (barM M X) := by
    rw [hφ, MonoidHom.range_comp, MonoidHom.range_comp, inclusion_range, hatOf,
      subgroupOf_barM_eq_map hDM hXD]
  have hker : φ.ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, MonoidHom.comp_apply, barMHomSub_mem_pCore_iff]
    have h1 : ((inclusion hXD x : ↥D) : G) = (x : G) := rfl
    rw [h1]
    constructor
    · intro hx
      have h2 : (x : G) ∈ pCoreOf 2 X := hO ▸ ⟨x.2, hx⟩
      obtain ⟨z, hz, hzx⟩ := mem_pCoreOf_iff.mp h2
      rwa [← Subtype.ext hzx]
    · intro hx
      have h2 : (x : G) ∈ pCoreOf 2 X := mem_pCoreOf_iff.mpr ⟨x, hx, rfl⟩
      rw [← hO] at h2
      exact h2.2
  exact ⟨((MulEquiv.subgroupCongr hrange).symm.trans
    (QuotientGroup.quotientKerEquivRange φ).symm).trans (QuotientGroup.quotientMulEquivOfEq hker)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
