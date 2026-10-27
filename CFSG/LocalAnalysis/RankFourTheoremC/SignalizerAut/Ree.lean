module

public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Basic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.AGLEmbedding CFSG.LieType.Ree
open CFSG.Blueprint.Chevalley (ModGL)


theorem not_gl83OuterType24_of_isReeGTwoIndex {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsReeGTwoIndex p d) : ¬ GL83OuterType24 p (.lie d) := by
  obtain ⟨hp, m, hm⟩ := hd
  rintro ⟨d', hd', ⟨-, q, hq, -⟩ | ⟨hp5, -⟩⟩
  · obtain rfl : d = d' := TauCeti.CFSGIndex.lie.inj hd'
    rw [hm] at hq
    cases hq
  · omega

theorem signalizerAutAt_ree
    {p : ℕ} {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex p d) :
    SignalizerAutAt p (.lie d) := by
  have hout := not_gl83OuterType24_of_isReeGTwoIndex hd
  obtain rfl : p = 3 := hd.1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, -, -, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd ⟨MulEquiv.refl _⟩
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have : Finite (ModGL ReeTag.G2.tag (GaloisField 3 (2 * a + 1))) :=
    CFSG.LieType.Chevalley.finite_modGL
  have : Finite ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) := Subtype.finite
  obtain ⟨⟨P, hP⟩, hNU, -, -⟩ := ReeModel.std_facts hK
  refine signalizerAutAt_of_model_weakTI Nat.prime_three hout e.symm
    (ReeTag.center_reeGamma_G2_eq_bot hK) (R := ReeModel.stdU a (GaloisField 3 (2 * a + 1)))
    (hP ▸ P.card_eq_multiplicity) (weakTI_of_inf_eq_bot fun g hg => ?_)
  rw [hNU] at hg
  exact ReeModel.inf_map_conj_eq_bot hK hg

end CFSG.LocalAnalysis.RankFourTheoremC
