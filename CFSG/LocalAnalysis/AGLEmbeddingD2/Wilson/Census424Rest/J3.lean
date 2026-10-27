module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofJ3
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census424Rest

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint

theorem false_of_maximal_nine_J3
    {X : Type} [Group X] [Finite X] (φ : X ≃* NativeSporadic.Carrier .J3) {D : Subgroup X}
    (hD : Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D)
    (hD9 : Nat.card D = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b⟩ : Nonempty (NativeSporadic.Carrier .J3 ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :=
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  obtain ⟨T, hDT⟩ := (Sec5.isPGroup_of_isElemAbelian hD.prop).exists_le_sylow
  have hF := CFSG.AGLEmbedding.kFactJ3Sylow X ⟨φ.trans b⟩ T
  obtain ⟨⟨hZcomm, hZ3⟩, hZ9⟩ := hF.center_elem
  obtain ⟨W, hW, hW27⟩ := Res423Three.exists_E27_of_J3 φ
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := (T : Subgroup X))
    (Sylow.card_eq_multiplicity T) (Sec5.isPGroup_of_isElemAbelian hW)
  refine Res423Three.false_of_maximal_of_central (T := T)
    (Z := CFSG.Quasithin.centerOf (T : Subgroup X))
    (W := W.map (MulAut.conj g⁻¹).toMonoidHom) (fun z hz x hx => ?_) ⟨hZcomm, hZ3⟩ hZ9
    (Item434AltPerm.map_conj_inv_le hg) ?_ (Res423Two.isElemAbelian_map' _ hW) hDT hD hD9
  · exact Subgroup.mem_centralizer_iff.mp hz.2 x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hW27]

theorem census424_of_j3
    {X : Type} [Group X] [Finite X] (φ : X ≃* NativeSporadic.Carrier .J3) : Census424 X := by
  intro D c d K h
  exact (false_of_maximal_nine_J3 φ h.maximal h.card_eq).elim

end CFSG.AGLEmbeddingD2.Wilson.Census424Rest
