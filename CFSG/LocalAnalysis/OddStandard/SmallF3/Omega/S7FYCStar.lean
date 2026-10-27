module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FYComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L71

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem s7f_inCStar_om6p [Finite G] (hsh : Asc82Shapes) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {x : G} (hx : orderOf x = 2) {Y : Subgroup G}
    (hYc : IsComponentIn Y (centralizer ({x} : Set G))) (h6p : IsOmega6Plus Y) : InCStar Y :=
  asc82Lemma71_of hsh G x Y
    (sec3SettingLB_of_component hS hx hYc ⟨hYc.isQuasisimple, Or.inl (Or.inr (Or.inl h6p))⟩) h6p

theorem s7f_inCStar_l281 [Finite G] (hsh : Asc82Shapes) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {x : G} (hx : orderOf x = 2) {Y : Subgroup G}
    (hYc : IsComponentIn Y (centralizer ({x} : Set G))) (hYF : InFStar Y) (h81 : IsL281 Y) :
    InCStar Y := by
  refine inCStar_of_ctrQ_maximal hS.a2 ⟨x, hx, hYc⟩ hYF fun Y' hY'C hY'F hdvd => ?_
  have hq' := sec65_quasisimple hY'F
  rw [ctrQ_of_l281 hYc.isQuasisimple h81] at hdvd ⊢
  rcases sec65_shape hsh hS hY'C hY'F with h | h | h | h | h | h
  · rw [ctrQ_of_l29 hq' h] at hdvd
    omega
  · exact ctrQ_of_l281 hq' h
  · rcases h with h | h
    · rw [ctrQ_of_l33 hq' h] at hdvd
      omega
    · rw [ctrQ_of_u33 hq' h] at hdvd
      omega
  · rw [ctrQ_of_psp4 hq' h] at hdvd
    omega
  · rw [ctrQ_of_l43 hq' h] at hdvd
    omega
  · rw [ctrQ_of_u43 hq' h] at hdvd
    omega

theorem s7f_inCStar_om5 [Finite G] (h35 : Asc82Lemma35) (h36 : Asc82Lemma36)
    (h63 : Asc82Lemma63) (hsh : Asc82Shapes) (hP : Asc82Tab6P) (hM : Asc82Tab6M)
    (hF : Asc82AutFacts) {t : G} {L S : Subgroup G} {z : G} (hctx : Sec7Ctx G t L S z)
    (hHyp : Asc82Hyp62 G) {b : G} (hb2 : orderOf b = 2) (hbL : b ∈ L)
    (hbt : InducesTypeSome L b 6 1 2 (-1)) {x : G} (hx : orderOf x = 2) {Y : Subgroup G}
    (hYc : IsComponentIn Y (centralizer ({x} : Set G))) (hYF : InFStar Y)
    (hXY : layerCent L b ≤ Y) (h5 : IsOmega5 Y) : InCStar Y := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hYq := hYc.isQuasisimple
  have h25920 : ctrQ Y = 25920 := ctrQ_of_psp4 hYq h5
  refine ⟨⟨x, hx, hYc⟩, fun Y' hch => ?_⟩
  have hpl := sec64_plain_of_chain h63 hS hHyp hYF hch
  rcases sec64_plain_chain hsh hP hS hHyp ⟨x, hx, hYc⟩ hYF hpl with heq | ⟨harr, hcases⟩ |
      ⟨h29, -⟩
  · subst heq
    exact ⟨MulEquiv.refl _⟩
  · rcases hcases with ⟨h29, -⟩ | ⟨-, h6p | h6m⟩ | ⟨h33, -⟩ | ⟨hu33, -⟩
    · rw [ctrQ_of_l29 hYq h29] at h25920
      omega
    · exact (sec63_no_om5_om6p hP hHyp harr h5 h6p).elim
    · exfalso
      have hY'F : InFStar Y' := inFStar_of_walterArrow hS.a2 harr hYF
      obtain ⟨-, y, -, hy, -, -, hY'c, hYY', -⟩ := harr
      exact s7f_not_om6m h36 h35 hP hM hF hctx hb2 hbL hbt hy hY'c
        (s7f_normal_of_63 h63 hS hHyp hy hY'c hY'F) hY'F (hXY.trans hYY') h6m
    · rw [ctrQ_of_l33 hYq h33] at h25920
      omega
    · rw [ctrQ_of_u33 hYq hu33] at h25920
      omega
  · rw [ctrQ_of_l29 hYq h29] at h25920
    omega

end CFSG.OddStandard.SmallF3.Omega
