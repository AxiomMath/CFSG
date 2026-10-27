module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.BlowUpACentre
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeVert
import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeCover
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.GH74.GLS.C3.Layer1.St1RigStep

public section

namespace CFSG.OddStandard.HigherRank

open CFSG Subgroup
open CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.ComponentClassification.GSThmB

theorem isL34Quotient_iff_lieModel_fusionZStar {A : Type} [Group A] :
    IsL34Quotient (A ⧸ pPrimeCore 2 A) ↔
      Blueprint.LieModel (A ⧸ Open.fusionZStar A) .PSL 3 2 2 :=
  ⟨fun h => Blueprint.LieModel.of_mulEquiv (Sol78.coreQuotientCenterEquiv A) h,
    fun h => Blueprint.LieModel.of_mulEquiv (Sol78.coreQuotientCenterEquiv A).symm h⟩

private theorem lieModel_vertical
    (hP9 : GS82PumpInputs.L34ExpFourPumpInput) {X : Type} [Group X] [Finite X] {y u : X}
    (hy : orderOf y = 2) (hyY : y ∈ centralizer ({u} : Set X))
    (hKY : SectionRank.IsKGroupCat ↥(centralizer ({u} : Set X))) {Λ K' : Subgroup X}
    (hΛ : IsPCompIn 2 (centralizer ({y} : Set X) ⊓ centralizer ({u} : Set X)) Λ)
    (hΛL : IsL34Quotient (kBar (Λ.subgroupOf (centralizer ({u} : Set X)))))
    (hΛ16 : Nat.card ↥(center (kBar (Λ.subgroupOf (centralizer ({u} : Set X))))) = 16)
    (hK'c : IsPCompIn 2 (centralizer ({u} : Set X)) K')
    {L : Subgroup (barQ ↥(centralizer ({u} : Set X)))} (hK'L : bar u K' = L)
    (hstab : conjSub (sbar y hyY)⁻¹ L = L) (hΛK' : bar u Λ ≤ L) :
    Blueprint.LieModel (↥(K'.subgroupOf (centralizer ({u} : Set X))) ⧸
      Open.fusionZStar ↥(K'.subgroupOf (centralizer ({u} : Set X)))) .PSL 3 2 2 := by
  have hΛC := le_centralizer_mk hΛ.1 hyY
  have hΛ2 := isTwoComponent_centralizer_mk hΛ hyY
  have hM2 : TwoComponents.IsTwoComponent (K'.subgroupOf (centralizer ({u} : Set X))) :=
    (isPCompIn_two_iff.mp hK'c).2
  have hperf : ⁅Λ.subgroupOf (centralizer ({u} : Set X)),
      Λ.subgroupOf (centralizer ({u} : Set X))⁆ = Λ.subgroupOf (centralizer ({u} : Set X)) :=
    commutator_self_of_isTwoComponent hΛC hΛ2
  have : Group.IsPerfect ↥(Λ.subgroupOf (centralizer ({u} : Set X))) :=
    Subgroup.isPerfect_iff.mpr hperf
  have hΛM : Λ.subgroupOf (centralizer ({u} : Set X)) ≤
      K'.subgroupOf (centralizer ({u} : Set X)) :=
    le_of_map_le_of_residual (barMk ↥(centralizer ({u} : Set X))) barMk_surjective
      odd_card_ker_barMk _ _ (ClassicalInvolution.Balance.twoResidual_eq_top_of_perfect
        Group.IsPerfect.commutator_eq_top) hM2.1 (hΛK'.trans hK'L.symm.le)
  have hLx' : L.map (MulAut.conj (barMk ↥(centralizer ({u} : Set X)) ⟨y, hyY⟩)).toMonoidHom =
      L := by
    have h := conjSub_conjSub_inv (barMk ↥(centralizer ({u} : Set X)) ⟨y, hyY⟩) L
    rw [show conjSub (barMk ↥(centralizer ({u} : Set X)) ⟨y, hyY⟩)⁻¹ L = L from hstab] at h
    exact h
  have hcomp : (barMk ↥(centralizer ({u} : Set X))).comp
      (MulAut.conj (⟨y, hyY⟩ : ↥(centralizer ({u} : Set X)))).toMonoidHom =
      (MulAut.conj (barMk ↥(centralizer ({u} : Set X)) ⟨y, hyY⟩)).toMonoidHom.comp
        (barMk ↥(centralizer ({u} : Set X))) := by
    ext a
    simp
  have hMx : (K'.subgroupOf (centralizer ({u} : Set X))).map
      (MulAut.conj (⟨y, hyY⟩ : ↥(centralizer ({u} : Set X)))).toMonoidHom =
      K'.subgroupOf (centralizer ({u} : Set X)) := by
    refine OddKernelTwoComponents.lift_unique (barMk ↥(centralizer ({u} : Set X)))
      barMk_surjective odd_card_ker_barMk _ _
      ((TwoComponentTransport.equiv_iff (MulAut.conj _) _).mpr hM2) hM2 ?_
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact (congrArg _ hK'L).trans (hLx'.trans hK'L.symm)
  have hy'N : (⟨y, hyY⟩ : ↥(centralizer ({u} : Set X))) ∈
      normalizer ((K'.subgroupOf (centralizer ({u} : Set X)) : Subgroup _) :
        Set ↥(centralizer ({u} : Set X))) :=
    mem_normalizer_iff_map_conj_eq.mpr hMx
  have hΛpc := (CatalogueBAlternating.pComponent_two_iff _).mpr hΛ2
  have hΛE : ¬ IsElementaryAbelian 2
      ↥(center (kBar (Λ.subgroupOf (centralizer ({u} : Set X))))) :=
    not_isElementaryAbelian_center_of_isL34Quotient (isQuasisimple_hat ⟨hΛC, hΛpc⟩).1 hΛL hΛ16
  rcases hP9 ↥(centralizer ({u} : Set X)) hKY _
      ((CatalogueBAlternating.pComponent_two_iff _).mpr hM2) ⟨y, hyY⟩
      (orderOf_mk_centralizer hyY hy) hy'N _ hΛM hΛC hΛpc hΛL hΛE with h | ⟨-, -, h4⟩
  · exact h
  · exact absurd (hΛ16.symm.trans h4) (by norm_num)

private theorem lieModel_diagonal {X : Type} [Group X] [Finite X] {y u : X}
    (hy : orderOf y = 2) (hyY : y ∈ centralizer ({u} : Set X)) {Λ K' : Subgroup X}
    (hΛ : IsPCompIn 2 (centralizer ({y} : Set X) ⊓ centralizer ({u} : Set X)) Λ)
    (hΛL : IsL34Quotient (kBar (Λ.subgroupOf (centralizer ({u} : Set X)))))
    (hK'c : IsPCompIn 2 (centralizer ({u} : Set X)) K')
    {L : Subgroup (barQ ↥(centralizer ({u} : Set X)))} (hK'L : bar u K' = L)
    (hAB : ⁅L, conjSub (sbar y hyY)⁻¹ L⁆ = ⊥) (hΛδ : bar u Λ ≤ (swapDiag hAB).range) :
    Blueprint.LieModel (↥(K'.subgroupOf (centralizer ({u} : Set X))) ⧸
      Open.fusionZStar ↥(K'.subgroupOf (centralizer ({u} : Set X)))) .PSL 3 2 2 := by
  obtain ⟨e⟩ := GS82PumpInputs.DPrime.nonempty_fusionZStarQuot_equiv
    (orderOf_mk_centralizer hyY hy) (le_centralizer_mk hΛ.1 hyY)
    (isTwoComponent_centralizer_mk hΛ hyY) (hK'L ▸ isComponent_bar hK'c) hAB hΛδ
    (isPCompIn_two_iff.mp hK'c).2 hK'L
  exact Blueprint.LieModel.of_mulEquiv e (isL34Quotient_iff_lieModel_fusionZStar.mp hΛL)

private theorem isKGroupCat_centralizer {X : Type} [Group X] [Finite X]
    (hX : IsKProperSimple X) {u : X} (hu : orderOf u = 2) :
    SectionRank.IsKGroupCat ↥(centralizer ({u} : Set X)) := by
  refine hX.isKGroupNative_of_ne_top fun htop => ?_
  have hc : u ∈ center X := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({u} : Set X) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.mp hg
  have : IsSimpleGroup X := hX.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · rw [h, mem_bot] at hc
    rw [hc, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · obtain ⟨a, b, hab⟩ := hX.2.1
    exact hab (mem_center_iff.mp (h ▸ mem_top b) a)

private theorem kBar_equiv_of_pumpUpLT
    (hP9 : GS82PumpInputs.L34ExpFourPumpInput) {X : Type} [Group X] [Finite X]
    (hX : IsKProperSimple X) {y u : X} {N K' : Subgroup X} (hlt : PumpUpLT 2 y N u K')
    (hN : IsL34Quotient (kBar N)) (hN16 : Nat.card ↥(center (kBar N)) = 16) :
    Nonempty (kBar K' ≃* kBar N) := by
  have hy : orderOf y = 2 := hlt.1.1
  have hu : orderOf u = 2 := hlt.2.1.1
  have hyY : y ∈ centralizer ({u} : Set X) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ, hK'c, ⟨L, -, himg, hcases⟩, -, -, -⟩ := step_core hlt hyY
  obtain ⟨eΛN⟩ := GS82PumpInputs.DPrime.nonempty_coreQuotEquiv_of_cover
    (hΛ.le.trans inf_le_left) hΛ.cover
  obtain ⟨eΛ⟩ := hat_equiv_subgroupOf (hΛ.le.trans inf_le_right)
  have hΛL : IsL34Quotient (kBar (Λ.subgroupOf (centralizer ({u} : Set X)))) :=
    isL34Quotient_of_mulEquiv (eΛ.symm.trans eΛN).symm hN
  have hΛ16 : Nat.card ↥(center (kBar (Λ.subgroupOf (centralizer ({u} : Set X))))) = 16 :=
    (Nat.card_congr (Subgroup.centerCongr (eΛ.symm.trans eΛN)).toEquiv).trans hN16
  have hs2 : orderOf (sbar y hyY) = 2 := orderOf_sbar hy hyY
  have hss : sbar y hyY * sbar y hyY = 1 := by
    have h1 := pow_orderOf_eq_one (sbar y hyY)
    rwa [hs2, sq] at h1
  have hsinv : (sbar y hyY)⁻¹ = sbar y hyY := inv_eq_of_mul_eq_one_left hss
  have hK'Z : Blueprint.LieModel (↥(K'.subgroupOf (centralizer ({u} : Set X))) ⧸
      Open.fusionZStar ↥(K'.subgroupOf (centralizer ({u} : Set X)))) .PSL 3 2 2 := by
    rcases hcases with ⟨hstab, hΛK'⟩ | ⟨-, hAB, hΛδ⟩
    · have hbarK' : bar u K' = L := by
        rcases himg with h | h
        · exact h
        · rw [h, hstab]
      exact lieModel_vertical hP9 hy hyY (isKGroupCat_centralizer hX hu) hΛ.pcW hΛL hΛ16 hK'c
        hbarK' hstab hΛK'
    · rcases himg with h | h
      · exact lieModel_diagonal hy hyY hΛ.pcW hΛL hK'c h hAB hΛδ
      · have hconj2 : conjSub (sbar y hyY)⁻¹ (conjSub (sbar y hyY)⁻¹ L) = L := by
          have h3 : conjSub (sbar y hyY)⁻¹ (conjSub (sbar y hyY)⁻¹ L) =
              conjSub (sbar y hyY) (conjSub (sbar y hyY)⁻¹ L) :=
            congrArg (fun g => conjSub g (conjSub (sbar y hyY)⁻¹ L)) hsinv
          rw [h3]
          exact conjSub_conjSub_inv _ L
        have hAB1 : ⁅conjSub (sbar y hyY)⁻¹ L,
            conjSub (sbar y hyY)⁻¹ (conjSub (sbar y hyY)⁻¹ L)⁆ = ⊥ := by
          rw [hconj2, Subgroup.commutator_comm]
          exact hAB
        have hrange := range_swapDiag_conj hss hAB hAB1
        exact lieModel_diagonal hy hyY hΛ.pcW hΛL hK'c h hAB1 (hrange ▸ hΛδ)
  have hK'L : IsL34Quotient (kBar K') := by
    obtain ⟨eK⟩ := hat_equiv_subgroupOf hK'c.1
    exact isL34Quotient_of_mulEquiv eK.symm (isL34Quotient_iff_lieModel_fusionZStar.mpr hK'Z)
  refine hat_equiv_of_pumpUpLT hlt ?_
  calc hatCard K' ≤ 16 * 20160 := hatCard_le_of_isL34Quotient hK'c hK'L
    _ = hatCard N := by
      show 16 * 20160 = Nat.card (kBar N)
      rw [card_eq_of_isL34Quotient hN, hN16]

theorem kBar_equiv_of_chain
    (hP9 : GS82PumpInputs.L34ExpFourPumpInput) {X : Type} [Group X] [Finite X]
    (hX : IsKProperSimple X) {a b : X × Subgroup X}
    (h : Relation.ReflTransGen (fun c d : X × Subgroup X => PumpUpLT 2 c.1 c.2 d.1 d.2) a b)
    (hL : IsL34Quotient (kBar a.2)) (h16 : Nat.card ↥(center (kBar a.2)) = 16) :
    Nonempty (kBar b.2 ≃* kBar a.2) := by
  induction h with
  | refl => exact ⟨MulEquiv.refl _⟩
  | tail _ hstep ih =>
    obtain ⟨e⟩ := ih
    obtain ⟨e'⟩ := kBar_equiv_of_pumpUpLT hP9 hX hstep (isL34Quotient_of_mulEquiv e.symm hL)
      ((Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans h16)
    exact ⟨e'.trans e⟩

end CFSG.OddStandard.HigherRank
