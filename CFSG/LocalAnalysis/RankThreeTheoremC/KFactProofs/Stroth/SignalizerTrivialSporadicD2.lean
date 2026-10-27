module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicBase
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

open CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankFourTheoremC

theorem signalizerTrivialOn_of_d2Heis {i : TauCeti.CFSGIndex} {p : ℕ} (hp : p.Prime)
    (H : D2HeisLocalAt i fun q => q = p) (hsig : SignalizerAutAt p i)
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* i.Group))
    (hcen : Subgroup.center K = ⊥) : SignalizerTrivialOn p K := by
  obtain ⟨e⟩ := hK
  have hKc : Subgroup.centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  have hnormal : ((MulAut.conj : K →* MulAut K).range).Normal := normal_range_conj
  refine signalizerTrivialOn_of_local hp (k := 3) (by norm_num) hcen ?_ ?_ ?_
  · intro B Y hB hBc hY hBY hin
    exact hsig K ⟨e⟩ B Y hB hBc hY hBY (Or.inl hin)
  · intro P
    have h := H K ⊤ inferInstance hKc ⟨Subgroup.topEquiv.trans e⟩ p rfl P
    exact ⟨h.2.1, h.2.2.2.2.2.2.1⟩
  · intro R
    have h := H (MulAut K) (MulAut.conj : K →* MulAut K).range hnormal
      (centralizer_range_conj_eq_bot hcen) ⟨(mulEquivRangeConj hcen).symm.trans e⟩ p rfl R
    exact ⟨h.2.1, h.2.2.2.1⟩

theorem signalizerTrivialOn_of_d2Torus {i : TauCeti.CFSGIndex} {p : ℕ} (hp : p.Prime)
    (H : D2TorusLocalAt i fun q => q = p) (hsig : SignalizerAutAt p i)
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* i.Group))
    (hcen : Subgroup.center K = ⊥) : SignalizerTrivialOn p K := by
  obtain ⟨e⟩ := hK
  have hKc : Subgroup.centralizer (((⊤ : Subgroup K) : Subgroup K) : Set K) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hcen]
  have hnormal : ((MulAut.conj : K →* MulAut K).range).Normal := normal_range_conj
  refine signalizerTrivialOn_of_local hp (k := 2) le_rfl hcen ?_ ?_ ?_
  · intro B Y hB hBc hY hBY hin
    exact hsig K ⟨e⟩ B Y hB hBc hY hBY (Or.inl hin)
  · intro P
    obtain ⟨-, hcard, -, -, -, t, htN, m, -, -, hm, -, -, -, -, hline⟩ :=
      H K ⊤ inferInstance hKc ⟨Subgroup.topEquiv.trans e⟩ p rfl P
    refine ⟨hcard, pow_eq_one_of_torus hp hcard htN fun Y₀ hY₀ hY₀c => ?_⟩
    simpa using hline 1 one_pos (by omega) Y₀ hY₀ hY₀c
  · intro R
    have h := H (MulAut K) (MulAut.conj : K →* MulAut K).range hnormal
      (centralizer_range_conj_eq_bot hcen) ⟨(mulEquivRangeConj hcen).symm.trans e⟩ p rfl R
    exact ⟨h.2.1, h.2.2.2.1⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
