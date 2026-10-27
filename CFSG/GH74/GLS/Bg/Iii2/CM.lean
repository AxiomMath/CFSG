module

public import CFSG.GH74.GLS.Bg.Iii2.CMAux
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.Iii2.CMPU

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.TwoThin
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Bg.Iii2.CMEngine

theorem cm_of : CM := by
  intro G _ _ hG h3 x u hxo huo hux R hR hcSec hcard
  classical
  have hxY : x ∈ centralizer ({u} : Set G) := mem_centralizer_symm hux
  have hRR : ∀ K ∈ R, IsRigidRankOneComp x K := fun K hK => (hR K).mp hK
  have hrk3 : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := fun y hy =>
    TwoThin.rankThreeCentralizers G hG.1 hG.2.1 h3 y hy
  have hex : ∀ K ∈ R, ∃ J : Subgroup G, PumpUpLT 2 x K u J := fun K hK =>
    exists_pumpUpLT (hRR K hK).1.1 huo (Subgroup.mem_inf.mpr ⟨hux, hcSec K hK⟩) (hrk3 u huo)
  choose! Jf hJf using hex
  have hrig : ∀ K ∈ R, IsRigidRankOneComp u (Jf K) := fun K hK =>
    isRigidRankOneComp_of_pumpUpLT (hRR K hK) (hJf K hK)
  have hstep : ∀ K ∈ R, ∃ Λ : Subgroup G, StepData x u hxY K (Jf K) Λ := fun K hK =>
    exists_stepData (hRR K hK) (hJf K hK) hxY
  choose! Λf hΛf using hstep
  have hKc : ∀ K ∈ R, IsPCompIn 2 (centralizer ({x} : Set G)) K := fun K hK => (hRR K hK).1.1.2.2
  have hinj : Set.InjOn Jf (R : Set (Subgroup G)) := by
    intro K hK K' hK' hJ
    by_contra hne
    have h2 : StepData x u hxY K' (Jf K) (Λf K') := by
      rw [hJ]
      exact hΛf K' hK'
    exact bar_lam_ne_of_ne (hKc K hK) (hKc K' hK') hne (hΛf K hK).lam (hΛf K' hK').lam
      ((hΛf K hK).bar_eq_of_eq h2)
  have hsub : Jf '' (R : Set (Subgroup G)) ⊆ {J' : Subgroup G | IsRigidRankOneComp u J'} := by
    rintro _ ⟨K, hK, rfl⟩
    exact hrig K hK
  have hncard : (Jf '' (R : Set (Subgroup G))).ncard = R.card := by
    rw [hinj.ncard_image, Set.ncard_coe_finset]
  have hEq : Jf '' (R : Set (Subgroup G)) = {J' : Subgroup G | IsRigidRankOneComp u J'} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hncard]; exact hcard) (Set.toFinite _)
  have hvert : ∀ K ∈ R, x ∈ normalizer (Jf K : Set G) := by
    intro K hK
    by_contra hx
    have hJ'rr : IsRigidRankOneComp u (cmap x (Jf K)) := isRigidRankOneComp_cmap (hrig K hK) hxY
    have hmem : cmap x (Jf K) ∈ Jf '' (R : Set (Subgroup G)) := by
      rw [hEq]
      exact hJ'rr
    obtain ⟨K', hK', hJK'⟩ := hmem
    have hne : K ≠ K' := by
      rintro rfl
      exact hx (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hJK'.symm)
    have h2 : StepData x u hxY K' (cmap x (Jf K)) (Λf K') := by
      rw [← hJK']
      exact hΛf K' hK'
    exact bar_lam_ne_of_ne (hKc K hK) (hKc K' hK') hne (hΛf K hK).lam (hΛf K' hK').lam
      ((hΛf K hK).bar_eq_of_cmap hxo hx h2)
  refine ⟨Jf, hinj, hrig, hEq.symm, ?_⟩
  intro K hK P hP hPu p hp
  have hlam : IsLam x u K (Λf K) := (hΛf K hK).lam
  have hbar : bar u (Λf K) = bar u (Jf K) :=
    ((hΛf K hK).cases.resolve_right (fun h => h.1 (hvert K hK))).2
  have hΛJ : Λf K ≤ Jf K := lam_le_of_bar_le hlam (hrig K hK).1.1.2.2 hbar.le
  have hpK : p ∈ K := hP.le hp
  have hpY : p ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr (hPu p hp).symm
  have h2el : ∃ n : ℕ, p ^ (2 ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hP.isPGroup ⟨p, hp⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  exact hΛJ (hlam.twoElt p (Subgroup.mem_inf.mpr ⟨hpK, hpY⟩) h2el)

end CFSG.GH74.GLS.Bg.Iii2
