module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneCoreData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel

public section

namespace CFSG.AGLEmbedding.KFactProofs.RankOneCore

open CFSG.AGLEmbedding CFSG.LieType.Ree

theorem rankOneCoreData_stdU {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    RankOneCoreData ↥(ReeTag.G2.reeGamma K a) (ReeModel.stdU a K) := by
  obtain ⟨-, hNU, hco, -⟩ := ReeModel.std_facts hK
  refine ⟨fun Q hQU hQ g hg => ?_, ?_⟩
  · rw [hNU]
    by_contra hgB
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQ
    have hgxQ : g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hg x).1 x.2
    have h1 : g * x * g⁻¹ ∈
        ReeModel.stdU a K ⊓ (ReeModel.stdU a K).map (MulAut.conj g).toMonoidHom :=
      ⟨hQU hgxQ, ⟨x, hQU x.2, by simp [MulAut.conj_apply]⟩⟩
    rw [ReeModel.inf_map_conj_eq_bot hK hgB, Subgroup.mem_bot] at h1
    apply hx
    apply Subtype.ext
    calc ((x : ↥(ReeTag.G2.reeGamma K a)) : ↥(ReeTag.G2.reeGamma K a))
        = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [hNU]
    exact hco.1

theorem rankOneCoreData_ree {L : Type} [Group L] [Finite L]
    {d : TauCeti.ValidLieTypeIndex} (hd : IsReeGTwoIndex 3 d) (h : Nonempty (L ≃* CatGroup d))
    (U : Sylow 3 L) : RankOneCoreData L (U : Subgroup L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, -, -, -⟩ := ReeModel.std_facts hK
  refine RankOneCoreData.of_equiv_sylow e U P ?_
  rw [hP]
  exact rankOneCoreData_stdU hK

end CFSG.AGLEmbedding.KFactProofs.RankOneCore
