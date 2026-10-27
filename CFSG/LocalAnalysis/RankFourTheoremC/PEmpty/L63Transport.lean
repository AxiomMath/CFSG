module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankPlane IsIsolatedPlane IsTwoInvariantIn
  IsMaxTwoInvariantIn)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ}

theorem pRank_map_subtype (hp : 1 < p) (H : Subgroup M) :
    Open.pRank p (H.map M.subtype) = Open.pRank p H := by
  apply le_antisymm
  · obtain ⟨E, hEle, hEe, hEc⟩ := CFSG.SectionRank.exists_pRank hp (H.map M.subtype)
    have hEM : E ≤ M := fun y hy => by
      obtain ⟨y', -, hyy⟩ := Subgroup.mem_map.mp (hEle hy)
      exact hyy ▸ y'.2
    refine CFSG.SectionRank.le_pRank hp (E := E.subgroupOf M) (H := H) ?_
      (CFSG.Open.IsElemAbelian.subgroupOf hEe M) (k := Open.pRank p (H.map M.subtype)) ?_
    · intro y hy
      have hy' : (y : G) ∈ H.map M.subtype := hEle hy
      obtain ⟨y', hy'H, hyy⟩ := Subgroup.mem_map.mp hy'
      have : y' = y := Subtype.ext hyy
      exact this ▸ hy'H
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hEc]
  · obtain ⟨E, hEH, hEe, hEc⟩ := CFSG.SectionRank.exists_pRank hp H
    refine CFSG.SectionRank.le_pRank hp (E := E.map M.subtype) (H := H.map M.subtype)
      (Subgroup.map_mono hEH) (CFSG.Open.IsElemAbelian.map hEe M.subtype) (k := Open.pRank p H) ?_
    rw [Subgroup.card_map_of_injective M.subtype_injective, hEc]

theorem pRank_subgroupOf (hp : 1 < p) {H : Subgroup G} (hH : H ≤ M) :
    Open.pRank p (H.subgroupOf M) = Open.pRank p H := by
  rw [← pRank_map_subtype hp, Subgroup.map_subgroupOf_eq_of_le hH]

theorem plane_map_subtype (x z : M) :
    (zpowers x ⊔ zpowers z).map M.subtype = zpowers (x : G) ⊔ zpowers (z : G) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem plane_eq_subgroupOf (x z : M) :
    zpowers x ⊔ zpowers z = (zpowers (x : G) ⊔ zpowers (z : G)).subgroupOf M := by
  have hle : zpowers (x : G) ⊔ zpowers (z : G) ≤ M := by
    rw [← plane_map_subtype]
    exact Subgroup.map_subtype_le _
  apply Subgroup.map_injective M.subtype_injective
  rw [plane_map_subtype, Subgroup.map_subgroupOf_eq_of_le hle]

theorem smallRankPlane_subgroupOf {P : Subgroup G} {x z : G} (hPM : P ≤ M) (hx : x ∈ M)
    (hz : z ∈ M) (h : SmallRankPlane p P x z) :
    SmallRankPlane p (P.subgroupOf M) (⟨x, hx⟩ : M) (⟨z, hz⟩ : M) := by
  have hB : zpowers (⟨x, hx⟩ : M) ⊔ zpowers (⟨z, hz⟩ : M) =
      (zpowers x ⊔ zpowers z).subgroupOf M := plane_eq_subgroupOf ⟨x, hx⟩ ⟨z, hz⟩
  have hBP : zpowers x ⊔ zpowers z ≤ P := h.isIsolatedPlane.1
  have hBM : zpowers x ⊔ zpowers z ≤ M := hBP.trans hPM
  have hcard : Nat.card ((zpowers x ⊔ zpowers z).subgroupOf M) =
      Nat.card (zpowers x ⊔ zpowers z : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hB]
    exact CFSG.Open.IsElemAbelian.subgroupOf h.isElemAbelian M
  · rw [hB, hcard]
    exact h.card_eq
  · intro y hy hyp
    rw [hB]
    have hyC : (y : G) ∈ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      have hb' : (⟨b, hBM hb⟩ : M) ∈ ((zpowers (⟨x, hx⟩ : M) ⊔ zpowers (⟨z, hz⟩ : M) : Subgroup M)
          : Set M) := by
        rw [hB]
        exact hb
      exact congrArg Subtype.val (mem_centralizer_iff.mp hy _ hb')
    exact h.mem_of_mem_centralizer (y : G) hyC (by simpa using congrArg Subtype.val hyp)
  · refine ⟨fun b hb => ?_, ?_, ?_, ?_⟩
    · rw [hB] at hb
      exact h.isIsolatedPlane.1 hb
    · rw [hB]
      exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp
        (CFSG.Open.IsElemAbelian.subgroupOf h.isElemAbelian M)
    · rw [hB, hcard]
      exact h.isIsolatedPlane.2.2.1
    · intro E hEP hE hVE
      have hE' : CFSG.IsElementaryAbelian p (E.map M.subtype) :=
        CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp
          (CFSG.Open.IsElemAbelian.map (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hE)
            M.subtype)
      have hEP' : E.map M.subtype ≤ P := by
        rintro _ ⟨e, he, rfl⟩
        exact hEP he
      have hVE' : zpowers x ⊔ zpowers z ≤ E.map M.subtype := by
        rw [hB] at hVE
        intro b hb
        exact ⟨⟨b, hBM hb⟩, hVE hb, rfl⟩
      have := h.isIsolatedPlane.2.2.2 _ hEP' hE' hVE'
      rwa [Subgroup.card_map_of_injective M.subtype_injective] at this
  · intro w hwP hwc hwp
    have hwP' : (w : G) ∈ P := hwP
    have hwc' : (w : G) ∈ centralizer (P : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      exact congrArg Subtype.val (mem_centralizer_iff.mp hwc (⟨q, hPM hq⟩ : M) hq)
    have := h.center (w : G) hwP' hwc' (by simpa using congrArg Subtype.val hwp)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp this
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩

theorem pRank_subgroupOf_inf (hp : 1 < p) (H : Subgroup G) :
    Open.pRank p (H.subgroupOf M) = Open.pRank p (M ⊓ H) := by
  have : H.subgroupOf M = (M ⊓ H).subgroupOf M := by
    ext y
    simp [Subgroup.mem_subgroupOf]
  rw [this, pRank_subgroupOf hp inf_le_left]

theorem pRank_normalizer_subgroupOf (hp : 1 < p) {T : Subgroup G} (hT : T ≤ M) :
    Open.pRank p (normalizer ((T.subgroupOf M : Subgroup M) : Set M)) =
      Open.pRank p (M ⊓ normalizer (T : Set G)) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hT, pRank_subgroupOf_inf hp]

theorem isMaxTwoInvariantIn_top {B T : Subgroup G} (hB : B ≤ M)
    (hT : IsMaxTwoInvariantIn B M T) :
    IsMaxTwoInvariantIn (B.subgroupOf M) ⊤ (T.subgroupOf M) := by
  obtain ⟨⟨hTM, hT2, hBT⟩, hmax⟩ := hT
  refine ⟨⟨le_top, hT2.comap_subtype, ?_⟩, fun S' hS' hTS' => ?_⟩
  · rw [← Subgroup.subgroupOf_normalizer_eq hTM]
    exact Subgroup.comap_mono hBT
  · obtain ⟨-, hS'2, hBS'⟩ := hS'
    have hS : IsTwoInvariantIn B M (S'.map M.subtype) := by
      refine ⟨Subgroup.map_subtype_le _, hS'2.map M.subtype, fun b hb => ?_⟩
      have hb' : (⟨b, hB hb⟩ : M) ∈ normalizer (S' : Set M) :=
        hBS' (show (⟨b, hB hb⟩ : M) ∈ B.subgroupOf M from hb)
      rw [mem_normalizer_iff] at hb' ⊢
      intro y
      constructor
      · rintro ⟨y', hy', rfl⟩
        exact ⟨_, (hb' y').mp hy', rfl⟩
      · intro hy
        obtain ⟨y', hy'S, hy'eq⟩ := hy
        have hbM : b ∈ M := hB hb
        have hy'G : (y' : G) = b * y * b⁻¹ := hy'eq
        have hyM : y ∈ M := by
          have : y = b⁻¹ * (y' : G) * b := by rw [hy'G]; group
          rw [this]
          exact M.mul_mem (M.mul_mem (M.inv_mem hbM) y'.2) hbM
        refine ⟨⟨y, hyM⟩, ?_, rfl⟩
        rw [SetLike.mem_coe, hb' ⟨y, hyM⟩]
        have : (⟨b, hbM⟩ : M) * ⟨y, hyM⟩ * (⟨b, hbM⟩ : M)⁻¹ = y' :=
          Subtype.ext (by simpa using hy'G.symm)
        rw [this]
        exact hy'S
    have hTS : T ≤ S'.map M.subtype := by
      intro t ht
      exact ⟨⟨t, hTM ht⟩, hTS' (show (⟨t, hTM ht⟩ : M) ∈ T.subgroupOf M from ht), rfl⟩
    have := hmax _ hS hTS
    apply Subgroup.map_injective M.subtype_injective
    rw [this, Subgroup.map_subgroupOf_eq_of_le hTM]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
