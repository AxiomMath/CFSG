module

public import CFSG.GH74.Generic.BProg.B2.PumpupTableBasic
public import CFSG.GH74.Generic.BProg.B1.Stage3aRankRee
import CFSG.GH74.Generic.BProg.B1.Stage3aRankJ1
import CFSG.GH74.Generic.S1.Exo.Q3HNoQ8L2
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylow
import CFSG.CGT.PushingUpLit.SolK.GenFour
public import CFSG.GH74.Generic.BProg.B2.PumpupTable

public section

namespace CFSG.GH74.Generic.BProg.B2.PumpupTableL2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic.BProg.B2.PumpupTableBasic

theorem rankCertified_of_shape45
    {X : Type} [Group X] (h : QShape4 X ∨ QShape5 X) : RankCertified X 2 := by
  rcases h with ⟨f, hm⟩ | h5
  · exact CFSG.GH74.Generic.BProg.B1.rankCertified_reeModel_two hm
  · obtain ⟨e0⟩ := h5
    exact (CFSG.GH74.Generic.BProg.B1.rankCertified_walterJ1_two).of_mulEquiv
      (e0.trans CFSG.Walter.walterJ1EquivNative.symm).symm

theorem sectionalTwoRankLE_two_of_psl2_model {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hp2 : p ≠ 2) (hY : LieModel Y .PSL 2 p f) : SectionalTwoRankLE Y 2 := by
  obtain ⟨hp, hf, -, -, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.AutL2Facts.lieModel_psl2_data hY
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 Y))
  obtain ⟨m, -, ⟨φ⟩⟩ := CFSG.ComponentClassification.AutL2Facts.sylow_two_dihedral_of_equiv e
    (CFSG.ComponentClassification.AutL2Facts.isOddPrimePower_of hp hp2 hf hF) S
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  obtain ⟨C, hC, hidx⟩ := CFSG.CGT.PushingUpLit.SolK.dihedral_cyclic_index (2 ^ m)
  refine CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_of_sylow S ?_
  exact SectionalTwoRankLE.of_mulEquiv φ.symm
    (CFSG.CGT.PushingUpLit.SolK.sectionalTwoRankLE_two_of_cyclic_index C (Or.inr hidx))

theorem pumpup_l2
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (_hf : 1 ≤ f) :
    PumpupEmpty (fun X _ => LieModel X .PSL 2 p f) := by
  intro N _ _ H t L hs hH
  obtain ⟨Z, _, hZo, hZn, hsh⟩ := hs.shape
  have hLH : L ≤ H := hs.comp.1.trans inf_le_left
  have hst := stated_of_lieModel (Or.inl rfl) hH
  rcases hsh with h1 | h3 | h4 | h5
  · obtain ⟨ψ, hψ⟩ := q8_in_H_of_shape hLH hZn hZo (exists_q8_of_shape13 (Or.inl h1))
    exact CFSG.GH74.Generic.S1.Exo.no_q8_of_psl2_model hp hp2 hst ψ hψ
  · obtain ⟨ψ, hψ⟩ := q8_in_H_of_shape hLH hZn hZo (exists_q8_of_shape13 (Or.inr h3))
    exact CFSG.GH74.Generic.S1.Exo.no_q8_of_psl2_model hp hp2 hst ψ hψ
  · exact (rankCertified_in_H_of_shape hLH hZn (rankCertified_of_shape45 (Or.inl h4))).not_sectionalTwoRankLE
      (sectionalTwoRankLE_two_of_psl2_model hp2 hH)
  · exact (rankCertified_in_H_of_shape hLH hZn (rankCertified_of_shape45 (Or.inr h5))).not_sectionalTwoRankLE
      (sectionalTwoRankLE_two_of_psl2_model hp2 hH)

end CFSG.GH74.Generic.BProg.B2.PumpupTableL2
