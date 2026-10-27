module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem simple_oddCore_of_u43 [Finite G] {Y : Subgroup G} (h : IsOmega6Minus Y) :
    IsSimpleGroup (Y ⧸ CFSG.oddCore Y) := by
  unfold IsOmega6Minus at h
  exact (CFSG.LieType.Simplicity.fam_classical_converse (Y ⧸ CFSG.oddCore Y)
    ⟨.PSU, 4, 3, 1, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2

theorem sec711M_not_central [Finite G] {Y : Subgroup G} (hY : IsOm6M Y) {y : G} (hy : y ∈ Y)
    (hy2 : orderOf y = 2) : y ∉ centralizer (Y : Set G) := by
  intro hyc
  have hycenter : (⟨y, hy⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * y = y * (g : G)
    exact Subgroup.mem_centralizer_iff.mp hyc g g.2
  have hmem : (⟨y, hy⟩ : ↥Y) ∈ CFSG.oddCore ↥Y := by
    rw [← center_eq_oddCore_of_simple hY.1 (simple_oddCore_of_u43 hY.2)]
    exact hycenter
  have hoddmem : y ∈ oddCoreIn Y := by
    rw [oddCoreIn, CFSG.inSubgroup]
    exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, hmem, rfl⟩
  have hodd : Odd (orderOf y) := odd_orderOf_of_mem_oddCoreIn hoddmem
  rw [hy2] at hodd
  obtain ⟨k, hk⟩ := hodd
  omega

theorem sec711M_pocket [Finite G] (hM : Asc82Tab6M) (hF : Asc82AutFacts) {Y : Subgroup G}
    (hY : IsOm6M Y) {y : G} (hy : y ∈ Y) (hy2 : orderOf y = 2) : IsI4PlusIn Y y := by
  refine (hF.pocket_M G Y hY y hy).mpr ⟨hy2, ?_⟩
  have hyN : y ∈ normalizer (Y : Set G) := Subgroup.le_normalizer hy
  exact (hM.inner_iff G Y hY y hy2 hyN).mp
    ⟨Subgroup.mem_sup_left hy, sec711M_not_central hY hy hy2⟩

theorem sec711M_pocket_transfer {b y : G} {Y K : Subgroup G} (hYle : Y ≤ centralizer ({b} : Set G))
    (hYn : (Y.subgroupOf (centralizer ({b} : Set G))).Normal) (hK : Sl23PocketIn Y y K) :
    Sl23Pocket b y K := by
  have hconj : ∀ h ∈ Y, ∀ k ∈ centralizer ({b} : Set G), k * h * k⁻¹ ∈ Y :=
    fun h hh k hk => (Subgroup.normal_subgroupOf_iff hYle).mp hYn h k hh hk
  change Sl23PocketIn (centralizer ({b} : Set G)) y K
  refine Sl23PocketIn.of_normal hK hYle ?_
  intro c hc
  ext x
  rw [mem_conjugate_iff]
  constructor
  · intro hx
    have h := hconj (c * x * c⁻¹) hx c⁻¹ ((centralizer ({b} : Set G)).inv_mem hc)
    have h' : c⁻¹ * (c * x * c⁻¹) * (c⁻¹)⁻¹ = x := by group
    rwa [h'] at h
  · intro hx
    exact hconj x hx c hc

theorem sec711M_layer_involution [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) {t : G}
    {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z) {b : G} (hb2 : orderOf b = 2)
    (hbL : b ∈ L) (hbt : InducesTypeSome L b 6 1 2 (-1)) :
    ∃ y ∈ layerCent L b, y ∈ L ∧ orderOf y = 2 ∧
      IsComponentIn (layerCent L y) (centralizer ({t, y} : Set G)) ∧ InFStar (layerCent L y) := by
  have hbN : b ∈ normalizer (L : Set G) := Subgroup.le_normalizer hbL
  have hX : IsL29 (layerCent L b) := hP.layer_i2 G L hctx.isOm6P b hb2 hbN hbt
  have hXc : IsComponentIn (layerCent L b) (L ⊓ centralizer ({b} : Set G)) :=
    isComponentIn_layerCent (Or.inr (Or.inl hX))
  obtain ⟨y, hyX, hy2⟩ := exists_involution_of_isComponentIn hXc
  have hyL : y ∈ L := (hXc.1 hyX).1
  have hne : layerCent L b ≠ ⊥ := ne_bot_of_shape (Or.inr (Or.inl hX))
  have hyXO : y ∈ XOut L b := by
    rw [hP.xout_eq G L hctx.isOm6P b hb2 hbN hne]
    exact hyX
  have hyt : InducesTypeSome L y 6 1 2 (-1) :=
    hP.inv_of_i4m G L hctx.isOm6P b hb2 hbN hbt y hyXO hy2
  have hyN : y ∈ normalizer (L : Set G) := Subgroup.le_normalizer hyL
  have hLy : IsL29 (layerCent L y) := hP.layer_i2 G L hctx.isOm6P y hy2 hyN hyt
  refine ⟨y, hyX, hyL, hy2, ?_, ?_⟩
  · rw [centralizer_pair_eq_inf]
    exact isComponentIn_pair_layerCent h36 hctx (Or.inr (Or.inl hLy))
  · refine Or.inr ⟨(isComponentIn_layerCent (Or.inr (Or.inl hLy))).isQuasisimple, ?_⟩
    exact Or.inl hLy

theorem sec711_not_omega6Minus [Finite G] (h36 : Asc82Lemma36) (h35 : Asc82Lemma35)
    (hP : Asc82Tab6P) (hM : Asc82Tab6M) (hF : Asc82AutFacts) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec7Ctx G t L S z) {b : G} (hb2 : orderOf b = 2) (hbL : b ∈ L)
    (hbt : InducesTypeSome L b 6 1 2 (-1)) {Y : Subgroup G}
    (hYc : IsComponentIn Y (centralizer ({b} : Set G)))
    (hYn : (Y.subgroupOf (centralizer ({b} : Set G))).Normal) (hYF : InFStar Y)
    (hXY : layerCent L b ≤ Y) (hY6 : IsOmega6Minus Y) : False := by
  obtain ⟨y, hyX, hyL, hy2, hJ, hJF⟩ := sec711M_layer_involution h36 hP hctx hb2 hbL hbt
  have hyY : y ∈ Y := hXY hyX
  have hOm6M : IsOm6M Y := ⟨hYc.isQuasisimple, hY6⟩
  obtain ⟨-, K, hK⟩ := sec711M_pocket hM hF hOm6M hyY hy2
  have hKb : Sl23Pocket b y K := sec711M_pocket_transfer hYc.1 hYn hK
  have hKY : K ≤ Y := hK.2.1.trans inf_le_left
  have hPD : Sec3PocketData b Y y K := ⟨hb2, hYc, hYF, hy2, hyY, hKY, hKb⟩
  have hty : t ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hctx.le_centralizer hyL)).symm
  exact h35 G t L hctx.toSec3SettingLB b Y y K t hPD hctx.involution hty
    (layerCent L y) ⟨hJ, hJF⟩

end CFSG.OddStandard.SmallF3.Omega
