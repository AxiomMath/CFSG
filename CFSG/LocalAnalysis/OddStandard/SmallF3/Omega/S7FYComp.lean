module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7EndM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec64Chain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_exists_Y [Finite G] (h36 : Asc82Lemma36) (hP : Asc82Tab6P) (h63 : Asc82Lemma63)
    {t : G} {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z) (hHyp : Asc82Hyp62 G) {b : G}
    (hb2 : orderOf b = 2) (hbL : b ∈ L) (hbt : InducesTypeSome L b 6 1 2 (-1)) :
    ∃ Y : Subgroup G, IsComponentIn Y (centralizer ({b} : Set G)) ∧ InFStar Y ∧
      layerCent L b ≤ Y := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hbN : b ∈ normalizer (L : Set G) := Subgroup.le_normalizer hbL
  have hX : IsL29 (layerCent L b) := hP.layer_i2 G L hctx.isOm6P b hb2 hbN hbt
  have hXc : IsComponentIn (layerCent L b) (centralizer ({t, b} : Set G)) := by
    rw [centralizer_pair_eq_inf]
    exact isComponentIn_pair_layerCent h36 hctx (Or.inr (Or.inl hX))
  have hXF : InFStar (layerCent L b) := Or.inr ⟨hXc.isQuasisimple, Or.inl hX⟩
  have hcomm : t * b = b * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hctx.le_centralizer hbL)).symm
  have htb : t ∈ centralizer ({b} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  obtain ⟨K, hK, hXle⟩ := hS.lBalance t b hS.involution hb2 hcomm _ hXc
  have hKF : InFStar K := hS.a2 t b hS.involution hb2 hcomm _ K hXc hK hXle hXF
  have hKt : K = CFSG.conjugate K t :=
    h63 G t L hS hHyp b hb2 K (CFSG.conjugate K t) hK hKF (hK.conjugate htb) (hKF.conjugate t)
  refine ⟨K, hK, hKF, ?_⟩
  rw [← hKt, sup_idem] at hXle
  exact hXle

theorem s7f_normal_of_63 [Finite G] (h63 : Asc82Lemma63) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hHyp : Asc82Hyp62 G) {y : G} (hy : orderOf y = 2)
    {Y : Subgroup G} (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hYF : InFStar Y) :
    (Y.subgroupOf (centralizer ({y} : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hYc.1).mpr fun _ hr =>
    sec64_mem_normalizer h63 hS hHyp hy hYc hYF hr

theorem s7f_not_om6m [Finite G] (h36 : Asc82Lemma36) (h35 : Asc82Lemma35) (hP : Asc82Tab6P)
    (hM : Asc82Tab6M) (hF : Asc82AutFacts) {t : G} {L S : Subgroup G} {z : G}
    (hctx : Sec7Ctx G t L S z) {b : G} (hb2 : orderOf b = 2) (hbL : b ∈ L)
    (hbt : InducesTypeSome L b 6 1 2 (-1)) {x : G} (hx : orderOf x = 2) {Y : Subgroup G}
    (hYc : IsComponentIn Y (centralizer ({x} : Set G)))
    (hYn : (Y.subgroupOf (centralizer ({x} : Set G))).Normal) (hYF : InFStar Y)
    (hXY : layerCent L b ≤ Y) (hY6 : IsOmega6Minus Y) : False := by
  obtain ⟨y, hyX, hyL, hy2, hJ, hJF⟩ := sec711M_layer_involution h36 hP hctx hb2 hbL hbt
  have hyY : y ∈ Y := hXY hyX
  obtain ⟨-, K, hK⟩ := sec711M_pocket hM hF ⟨hYc.isQuasisimple, hY6⟩ hyY hy2
  have hKx : Sl23Pocket x y K := sec711M_pocket_transfer hYc.1 hYn hK
  have hPD : Sec3PocketData x Y y K :=
    ⟨hx, hYc, hYF, hy2, hyY, hK.2.1.trans inf_le_left, hKx⟩
  have hty : t ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hctx.le_centralizer hyL)).symm
  exact h35 G t L hctx.toSec3SettingLB x Y y K t hPD hctx.involution hty (layerCent L y) ⟨hJ, hJF⟩

end CFSG.OddStandard.SmallF3.Omega
