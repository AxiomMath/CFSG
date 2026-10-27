module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Embed
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Norm
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18He
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSuz

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.ComponentClassification.RankTwoSporadic (IsActionHom)
open CFSG.Blueprint.NativeSporadic

theorem step18_of'
    (h4 : AS76b.Asc75Theorem4) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) : Step18 := by
  intro G _ _ A R g E F hF hL hbelow z hzE hz hS2 hzR
  obtain ⟨S, -, hSz⟩ := hS2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h34 : AS76b.Asc08Lemma34 := AS76b.asc08Lemma34
  by_contra hW
  have hB := hF.base
  have hstd := hB.hyp.standard
  obtain ⟨hHA, hFs⟩ := h34 G A hB.hyp31
  obtain ⟨hNtop, hAW, hzW, hH⟩ := rankTwoHyp_normalizer_of_frame h4 h34 hE16 hF hL hzE hW
  have hcard : Nat.card (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G)) <
      Nat.card G := by
    have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hNtop)
    rwa [card_top] at this
  have hAN : A ≤ normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G) :=
    hAW.trans (centralizer_le_normalizer _)
  let eA : ↥(A.subgroupOf (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G))) ≃*
      ↥A := subgroupOfEquivOfLe hAN
  have hL₁ : TypeL34 (rankTwoQuot
      (A.subgroupOf (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G)))) :=
    statedClassicalModel_of_mulEquiv
      (QuotientGroup.congr (center _) (center _) eA (Subgroup.map_center_eq eA)) hL
  have hconc := hbelow _ _ hcard hH hL₁
  have hAL := normalizer_le_normalizer_closureIn h4 h34 hE16 hF hL hbelow hzE hW hconc
  have hCL := odd_card_centralizer_closureIn hstd hAN hH.not_normal
  have hzL := hzW.trans
    (le_normalizer_closureIn A (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G)))
  have hLH : closureIn A (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G)) ≤
      CFSG.generalizedFitting G := hHA ▸ closureIn_le_normalClosure A _
  have hWL : AS76b.oddCoreIn (centralizer ({z} : Set G)) ≤ centralizer
      (closureIn A (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G)) : Set G) :=
    le_centralizer_iff.mp (closureIn_le_centralizer hAW)
  have hRz : R ≤ centralizer ({z} : Set G) := fun r hr => by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨r, hF.R_le_E hr⟩ ⟨z, hzE⟩)
  have hS : IsSylowOf 2 (S : Subgroup G) ⊤ :=
    isSylowOf_iff.mpr ⟨le_top, S.isPGroup', by rw [relIndex_top_right]; exact S.not_dvd_index⟩
  let eL : ↥(closureIn A (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G))) ≃*
      ↥(rankTwoX
        (A.subgroupOf (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G)))) :=
    ((rankTwoX _).equivMapOfInjective _ (normalizer _).subtype_injective).symm
  have hperf : commutator ↥(closureIn A
      (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G))) = ⊤ :=
    commutator_eq_top_of_mulEquiv eL.symm
      (commutator_rankTwoX_eq_top (commutator_eq_top_of_mulEquiv eA.symm hstd.1.1))
  rcases hconc with ⟨⟨eSuz⟩, hZ3⟩ | ⟨-, ⟨eHe⟩⟩
  ·
    obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoSporadic.Suz.suzAutModel hperf
      ((QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans eSuz)
    exact false_of_frame18 hF hHA hFs hz hzR hS hSz hRz suz_fusionModel suz_involutionTwoClasses
      (isActionHom_subtype_comp CFSG.Sporadic.SuzOddCore.suzM_le_suzT hψ) (range_subtype_comp_le ψ)
      (by rw [Nat.card_congr (Subgroup.centerCongr eL).toEquiv]; exact hZ3) hCL hzL hAL hLH hW hWL
  ·
    let e₂ := eL.trans eHe
    have hZL : center ↥(closureIn A
        (normalizer (AS76b.oddCoreIn (centralizer ({z} : Set G)) : Set G))) = ⊥ := by
      rw [← map_center_eq e₂.symm, center_eq_bot_of_autModel RankTwoSporadic.He.heAutModel,
        Subgroup.map_bot]
    obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoSporadic.He.heAutModel hperf
      ((QuotientGroup.quotientMulEquivOfEq hZL).trans (QuotientGroup.quotientBot.trans e₂))
    exact false_of_frame18 hF hHA hFs hz hzR hS hSz hRz he_fusionModel he_involutionTwoClasses
      (isActionHom_subtype_comp CFSG.Sporadic.HeldB.heP_le_heAutGroup hψ) (range_subtype_comp_le ψ)
      (by rw [hZL, card_bot]; norm_num) hCL hzL hAL hLH hW hWL

end CFSG.ComponentClassification.AS81
