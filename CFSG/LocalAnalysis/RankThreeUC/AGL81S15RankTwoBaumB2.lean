module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumO1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumSp4
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoB2OffInner
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
public import CFSG.ClassicalGroups.Symplectic.ComponentCoverGriessB2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open KFactsPair

@[expose] def K517_4b_baumPower_B2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
    GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
    gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
    ∀ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, d.1 = .B 2 Q) →
      IsRankTwoPlus d.1 → IsRankTwoType d.1 →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ indexQ d.1 - 1 →
        ∀ s ∈ gnImg T (CFSG.Quasithin.baum T), ∃ j : ℕ,
          ∀ x ∈ Ls ⊓ Subgroup.normalizer
              ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)),
            s * x * s⁻¹ * (x ^ j)⁻¹ ∈ gnImg T T ⊓ Ls

theorem K517_4b_baumPower_B2_of_K543DynkinB2 (hO1 : K543DynkinB2) : K517_4b_baumPower_B2 := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hQd hR2P hR2T hLd q hq hq2 hqd s hs
  obtain ⟨Q, hdQ⟩ := hQd
  obtain ⟨eL⟩ := hLd
  rcases d with ⟨d, hv⟩
  have hd' : d = TauCeti.LieTypeIndex.B 2 Q := hdQ
  subst hd'
  have hQ : Q.p = 2 := hR2T
  have hf : 2 ≤ Q.exponent := two_le_exponent_of_valid_B2 hQ hv
  obtain ⟨e⟩ := CFSG.ClassicalGroups.Symplectic.exists_mulEquiv_statedSp_of_component_B2
    hY.1.2.2 hf hQ rfl eL
  have hcomm : ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls := (hGood.shape Ls hY).1
  have hsT : s ∈ gnImg T T :=
    Subgroup.map_mono (show CFSG.Quasithin.baum T ≤ T from inf_le_left) hs
  let H : Subgroup ↥Ls := (gnImg T T ⊓ Ls).subgroupOf Ls
  let α : MulAut ↥Ls := Ls.normalizerMonoidHom ⟨s, hinv hsT⟩
  have hHstab : H.map α.toMonoidHom = H :=
    map_subgroupOf_inf_normalizerMonoidHom_eq_of_mem hinv hsT
  have hS := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
    hX.sylow hY.1.2.1
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf H ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · rw [show (H.subgroupOf (⊤ : Subgroup ↥Ls)).index = H.index from
          Subgroup.relIndex_top_right _]
      exact hS.2.2
  have hU' : CFSG.QuasithinUnique.IsSylowTwoOf (H.map e.toMonoidHom) ⊤ := by
    have h := CFSG.Quasithin.H13.L32A.C.SkPf.isSylowTwoOf_map_symm e.symm hU
    rwa [MulEquiv.symm_symm] at h
  obtain ⟨A, σ, hAσ⟩ := hO1 X T hX Ls hY.1 hcomm Q.exponent hf e ⟨s, hinv hsT⟩
  have hα_congr : (H.map e.toMonoidHom).map (MulAut.congr e α).toMonoidHom =
      H.map e.toMonoidHom := by
    rw [Subgroup.map_map]
    have hcomp : (MulAut.congr e α).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change (MulAut.congr e α) (e x) = e (α x)
      rw [MulAut.congr_apply]
      simp [MulEquiv.trans_apply]
    rw [hcomp, ← Subgroup.map_map, hHstab]
  obtain ⟨k, hk⟩ := exists_pow_mul_inv_mem_of_conjSp_fieldSp hU' A σ (by
    rw [← hAσ]
    exact hα_congr)
  refine exists_pow_conj_mul_inv_mem_of_pow_action_equiv (S := gnImg T T) hinv e hsT ⟨k, ?_⟩
  intro b hb
  rw [hAσ]
  exact hk b hb

end CFSG.LocalAnalysis.RankThreeUC.S15

end
