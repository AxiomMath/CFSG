module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCenterOver
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanReeCenterOverGen

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.Ree

theorem kFactReeCenterOver :
    KFactReeCenterOver := by
  intro L _ _ d hd h T₁ Y hZY hY
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, -, -, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e T₁ P
  have hU : (T₁ : Subgroup L).map e'.toMonoidHom =
      ReeModel.stdU a (GaloisField 3 (2 * a + 1)) := he'.trans hP
  have hZ : ((T₁ : Subgroup L) ⊓ Subgroup.centralizer ((T₁ : Subgroup L) : Set L)).map
      e'.toMonoidHom = ReeModel.stdU a (GaloisField 3 (2 * a + 1)) ⊓ Subgroup.centralizer
        ((ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :
          Subgroup ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) :
          Set ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) := by
    ext x
    obtain ⟨y, rfl⟩ := e'.surjective x
    rw [ReeModel.mem_map_iff, Subgroup.mem_inf, Subgroup.mem_inf, ← hU, ReeModel.mem_map_iff,
      ReeModel.mem_centralizer_map_iff]
  have hY' : ReeModel.stdU a (GaloisField 3 (2 * a + 1)) ⊓ Subgroup.centralizer
        ((ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :
          Subgroup ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) :
          Set ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) ≤ Y.map e'.toMonoidHom := by
    rw [← hZ]
    exact Subgroup.map_mono hZY
  have hsolv : ¬ Group.IsSolvable (Y.map e'.toMonoidHom) := fun hs => hY
    (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective Y e'.toMonoidHom e'.injective).toMonoidHom)
      (Subgroup.equivMapOfInjective Y e'.toMonoidHom e'.injective).injective)
  have htop := ReeCenterOver.ree_zero_overgroup hK ha (Y.map e'.toMonoidHom) hY' hsolv
  rw [eq_top_iff]
  intro x _
  have hx : e' x ∈ Y.map e'.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
  rwa [ReeModel.mem_map_iff] at hx

end CFSG.AGLEmbedding
