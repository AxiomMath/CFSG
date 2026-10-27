module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCL34
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaAdapt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGammaMove
import CFSG.GH74.KGroups.L34Tables
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved
import CFSG.Adapters.TauCetiLieModels
import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier


theorem kFactTenNineWCGammaL34 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal], IsRankThreeL34 K →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ hL S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq2, hqe, hv, ⟨e0⟩⟩ := hL
  have hm := CFSG.Models.lieModel_A 2 q hv e0
  rw [hq2, hqe] at hm
  obtain ⟨e⟩ := L34.equiv_of_lieModel (CFSG.Models.LieModel.toBlueprint (by decide) hm)
  obtain ⟨M, hP, hAM⟩ := L34.autModel e
  have hK : Nat.card K = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_group L34.QP L34.QP_ok, L34.QP_valid.2]
  have h9 : ∀ T : Sylow 3 K, Nat.card (T : Subgroup K) = 9 := by
    intro T
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    have hmul := (T : Subgroup K).card_mul_index
    rw [hk, hK] at hmul
    have hidx := T.not_dvd_index
    have hk3 : k ≤ 2 := by
      by_contra! h
      have : 3 ^ 3 ∣ 20160 := (Nat.pow_dvd_pow 3 h).trans ⟨_, hmul.symm⟩
      norm_num at this
    interval_cases k
    · exfalso; apply hidx; rw [show (T : Subgroup K).index = 20160 by omega]; norm_num
    · exfalso; apply hidx; rw [show (T : Subgroup K).index = 6720 by omega]; norm_num
    · rw [hk]; norm_num
  refine false_of_fuse_gamma_out (fun k hk => L34.center_trivial e k fun n => (hk n).symm) ?_ ?_
    S A hA3 Y hY hwc
  ·
    intro T φ ⟨m, hm⟩ hfix
    set σ : Equiv.Perm (Fin 42) := (M.Φ φ : Equiv.Perm (Fin 42))
    have hσA : σ ∈ L34.QA.originalSubgroup := hAM ▸ (M.Φ φ).2
    have h27 : σ ^ 27 = 1 := by
      have hσm : σ ^ 3 ^ m = 1 := by rw [← M.Φ_pow, hm, M.Φ_one]
      have hord : orderOf σ ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hσm
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
      have hdvd : orderOf σ ∣ 241920 := by
        have := Subgroup.orderOf_dvd_natCard L34.QA.originalSubgroup hσA
        rwa [card_group L34.QA L34.QA_ok, L34.QA_valid.2] at this
      have hj3 : j ≤ 3 := by
        by_contra! h
        have : 3 ^ 4 ∣ 241920 := (Nat.pow_dvd_pow 3 h).trans (hj ▸ hdvd)
        norm_num at this
      exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ Nat.pow_dvd_pow 3 hj3)
    set T' : Subgroup (Equiv.Perm (Fin 42)) :=
      ((T : Subgroup K).map M.e.toMonoidHom).map M.P.subtype
    have hT' : Nat.card T' = 9 := by
      rw [Subgroup.card_map_of_injective M.P.subtype_injective,
        Subgroup.card_map_of_injective M.e.injective, h9 T]
    have hle : T' ≤ L34.QP.originalSubgroup ⊓
        Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 42))) := by
      rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨hP ▸ (M.e t).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hs := M.spec φ t
      rw [hfix t ht] at hs
      simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
      calc ((M.e t : M.P) : Equiv.Perm (Fin 42)) * σ
          = ((M.Φ φ : Equiv.Perm (Fin 42)) * (M.e t : Equiv.Perm (Fin 42)) *
              (M.Φ φ : Equiv.Perm (Fin 42))⁻¹) * σ := by rw [← hs]
        _ = σ * ((M.e t : M.P) : Equiv.Perm (Fin 42)) := by simp [σ]
    have hσP := l34_outer3 σ hσA h27 (hT' ▸ Subgroup.card_dvd_of_le hle)
    exact M.inner_of_mem φ (hP ▸ hσP)
  ·
    intro T a ha hoa _
    obtain ⟨n, hn, hb⟩ := move_of_transitive
      (fun T a b ha hb ha1 hb1 => kFactL34SylowTransitive K ⟨q, hq2, hqe, hv, ⟨e0⟩⟩ T a b ha hb
        ha1 hb1)
      (fun T => by rw [h9 T]; norm_num) T a ha hoa
    exact gamma_of_fuse_normalizer ha hoa ⟨n, hn, hb⟩

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
