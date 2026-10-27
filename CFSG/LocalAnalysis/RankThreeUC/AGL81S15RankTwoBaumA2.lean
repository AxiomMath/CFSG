module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumO1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumSL3
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (slFieldAut)
open KFactsPair

@[expose] def K517_4b_baumPower_A2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X),
    GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
    gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
    ∀ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, d.1 = .A 2 Q) →
      IsRankTwoPlus d.1 → IsRankTwoType d.1 →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ indexQ d.1 - 1 →
        ∀ s ∈ gnImg T (CFSG.Quasithin.baum T), ∃ j : ℕ,
          ∀ x ∈ Ls ⊓ Subgroup.normalizer
              ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)),
            s * x * s⁻¹ * (x ^ j)⁻¹ ∈ gnImg T T ⊓ Ls

theorem K517_4b_baumPower_A2_of_identification
    (hid : ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T →
      GNGood T T₁ T₂ → ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      ∀ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), IsRankTwoType d.1 →
        d.1 = .A 2 Q →
        Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ q : ℕ, q.Prime → q ∣ indexQ d.1 - 1 →
          2 ≤ Q.exponent ∧
            Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 Q.exponent)))
    (hO1 : K541DynkinA2) : K517_4b_baumPower_A2 := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY hinv d hQd _hR2P hR2T hLd q hq _hq2 hqdiv
  obtain ⟨Q, hQd⟩ := hQd
  obtain ⟨hn2, ⟨e⟩⟩ := hid X T T₁ T₂ hX hGood Ls hY d Q hR2T hQd hLd q hq hqdiv
  have hL : CFSG.Open.IsComponentOf Ls ⊤ := hY.1
  have hcomm : ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls := (hGood.shape Ls hY).1
  intro s hs
  have hsT : s ∈ gnImg T T := Subgroup.map_mono inf_le_left hs
  obtain ⟨P, σ, hPσ⟩ := hO1 X T hX Ls hL hcomm Q.exponent hn2 e ⟨s, hinv hsT⟩
  have hS := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
    hX.sylow hL.2.1
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf ((gnImg T T ⊓ Ls).subgroupOf Ls) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
    · rw [show (((gnImg T T ⊓ Ls).subgroupOf Ls).subgroupOf (⊤ : Subgroup ↥Ls)).index =
          ((gnImg T T ⊓ Ls).subgroupOf Ls).index from Subgroup.relIndex_top_right _]
      exact hS.2.2
  let U' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 Q.exponent)) :=
    ((gnImg T T ⊓ Ls).subgroupOf Ls).map e.toMonoidHom
  have hU' : CFSG.QuasithinUnique.IsSylowTwoOf U' ⊤ := by
    have h := CFSG.Quasithin.H13.L32A.C.SkPf.isSylowTwoOf_map_symm e.symm hU
    simpa [U'] using h
  have hHmap := map_subgroupOf_inf_normalizerMonoidHom_eq_of_mem (S := gnImg T T) hinv hsT
  have hcomp : (MulAut.congr e (Ls.normalizerMonoidHom ⟨s, hinv hsT⟩)).toMonoidHom.comp
        e.toMonoidHom =
      e.toMonoidHom.comp (Ls.normalizerMonoidHom ⟨s, hinv hsT⟩).toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    show (MulAut.congr e (Ls.normalizerMonoidHom ⟨s, hinv hsT⟩)) (e x) =
      e ((Ls.normalizerMonoidHom ⟨s, hinv hsT⟩) x)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hαU' : U'.map
      (MulAut.congr e (Ls.normalizerMonoidHom ⟨s, hinv hsT⟩)).toMonoidHom = U' := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hHmap]
  have hα'' : U'.map (slConjugation 3 (GaloisField 2 Q.exponent) P *
      slFieldAut (Fin 3) (GaloisField 2 Q.exponent) σ).toMonoidHom = U' := by
    rw [← hPσ]
    exact hαU'
  obtain ⟨k, hk⟩ := exists_pow_mul_inv_mem_of_slConjugation_slFieldAut hU' P σ hα''
  exact exists_pow_conj_mul_inv_mem_of_pow_action_equiv hinv e hsT
    ⟨k, fun b hb => by rw [hPσ]; exact hk b hb⟩

end CFSG.LocalAnalysis.RankThreeUC.S15

end
