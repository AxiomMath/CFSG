module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporFinal
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.LocalAnalysis.GL83PartI.I_24_3.List
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Rest
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporFalse

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover SporadicMultipliers
  sporadicMultiplierOrder)
open CFSG.LocalAnalysis.UniquenessCase.UCK (SporPlaneConf K315Spor)
open CFSG.RankThree.PartTwo.KFacts (congr_mulAutConj)

variable {X : Type} [Group X] [Finite X] {K E S : Subgroup X}

namespace K37Setting

theorem exists_sporPlaneConf (h : K37Setting X K E S) {T : Type} [Group T] (ψ : ↥K ≃* T)
    (hSC : ¬ S ≤ Subgroup.centralizer (K : Set X)) :
    ∃ Ē R : Subgroup (MulAut T), SporPlaneConf T 3 Ē R := by
  obtain ⟨Θ, hΘinj, hΘapp, hΘc⟩ : ∃ Θ : MulAut ↥K →* MulAut T, Function.Injective Θ ∧
      (∀ (α : MulAut ↥K) (y : ↥K), Θ α (ψ y) = ψ (α y)) ∧
      ∀ y : ↥K, Θ (MulAut.conj y) = MulAut.conj (ψ y) :=
    ⟨(MulAut.congr ψ).toMonoidHom, (MulAut.congr ψ).injective,
      fun α y => by simp [MulAut.congr_apply], congr_mulAutConj ψ⟩
  refine ⟨(autIm E K).map Θ, (autIm S K).map Θ, h.isElemAbelian_autIm.map Θ, ?_,
    (isPGroup_autIm (K := K) h.two).map Θ, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hΘinj, h.card_autIm]
  · intro hbot
    exact hSC (le_centralizer_of_autIm_eq_bot h.S_le_normalizer_K
      ((Subgroup.map_eq_bot_iff_of_injective _ hΘinj).mp hbot))
  · rintro _ ⟨_, ⟨⟨g, hgN⟩, hg, rfl⟩, rfl⟩
    exact Subgroup.le_normalizer_map Θ (Subgroup.mem_map_of_mem Θ
      (mem_normalizer_autIm hgN (h.le_normalizer_S (Subgroup.mem_subgroupOf.mp hg))))
  · rintro k ⟨_, ⟨_, ⟨⟨e, heN⟩, he, rfl⟩, rfl⟩, hε1, hεk⟩
    have he1 : e ≠ 1 := by
      rintro rfl
      exact hε1 (by
        rw [show (⟨1, heN⟩ : ↥(Subgroup.normalizer (K : Set X))) = 1 from rfl, map_one, map_one])
    have h1 : K.normalizerMonoidHom ⟨e, heN⟩ (ψ.symm k) = ψ.symm k :=
      ψ.injective (by rw [← hΘapp, MulEquiv.apply_symm_apply]; exact hεk)
    have h2 : e * (ψ.symm k : X) * e⁻¹ = ψ.symm k := by
      have h3 := congrArg Subtype.val h1
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
    have hkΓ : ((ψ.symm k : ↥K) : X) ∈ rankThreeGamma 1 3 E := by
      refine h.centralizer_le (Subgroup.mem_subgroupOf.mp he) he1
        (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
      calc ((ψ.symm k : ↥K) : X) * e = e * (ψ.symm k : X) * e⁻¹ * e := by rw [h2]
        _ = e * (ψ.symm k : X) := by group
    have hn : MulAut.conj (ψ.symm k) ∈
        Subgroup.normalizer ((autIm S K : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) :=
      h.conj_mem_normalizer_autIm (ψ.symm k).2 hkΓ
    have hn' := Subgroup.le_normalizer_map Θ (Subgroup.mem_map_of_mem Θ hn)
    rw [hΘc, MulEquiv.apply_symm_apply] at hn'
    exact hn'


theorem le_centralizer_of_spor (hSpM : SporadicMultipliers) (hK : K315Spor)
    (h : K37Setting X K E S) {s : TauCeti.SporadicName}
    (hφ : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (hO : ¬ K37Open K E) : S ≤ Subgroup.centralizer (K : Set X) := by
  obtain ⟨φ⟩ := hφ
  by_contra hSC
  have hO' := hO
  simp only [K37Open, not_or] at hO'
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, h11, h12, h13, h14, h15⟩ := hO'
  have hs : s ∈ CFSG.RankThree.PartOne.Census3.sporadicsThm3 := by
    by_contra hs
    exact h15 ⟨s, hs, ⟨φ⟩⟩
  have hZ : Subgroup.center ↥K = ⊥ := by
    rcases h.isPGroup_center.card_eq_or_dvd with h1 | hz
    · exact Subgroup.eq_bot_of_card_eq _ h1
    have hdvd := hz.trans (GL83.I243.CoverList.card_center_dvd_sporadic hSpM h.quasi φ)
    have hcov : IsThreeCenterCover ↥K (TauCeti.CFSGIndex.sporadic s).Group := ⟨h.quasi, hz, ⟨φ⟩⟩
    have h5 : ∀ t ∈ CFSG.RankThree.PartOne.Census3.sporadicsThm3, 3 ∣ sporadicMultiplierOrder t →
        t = .M22 ∨ t = .J3 ∨ t = .McL ∨ t = .Suz ∨ t = .ONan := by
      decide
    rcases h5 s hs hdvd with rfl | rfl | rfl | rfl | rfl
    · exact (h10 hcov).elim
    · exact (h11 hcov).elim
    · exact (h12 hcov).elim
    · exact (h13 hcov).elim
    · exact (h14 hcov).elim
  have ψ : ↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans φ
  haveI : Finite (TauCeti.CFSGIndex.sporadic s).Group := Finite.of_equiv _ ψ.toEquiv
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.quasi.2.1
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s).Group := φ.symm.isSimpleGroup
  have hZT : Subgroup.center (TauCeti.CFSGIndex.sporadic s).Group = ⊥ := by
    rw [← Subgroup.map_center_eq ψ, hZ, Subgroup.map_bot]
  obtain ⟨Ē, R, hconf⟩ := h.exists_sporPlaneConf ψ hSC
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.Spor.not_sporPlaneConf_of_planeGenOrExc hZT
    Nat.prime_three (by norm_num) (CFSG.LocalAnalysis.UniquenessCase.UCK.Spor.planeGenOrExc_catalog
      (hK s hs 3 Nat.prime_three (by norm_num) Ē R hconf) Nat.prime_three (by norm_num)) hconf

end K37Setting

end CFSG.LocalAnalysis.RankThreeUC.S15.K37
