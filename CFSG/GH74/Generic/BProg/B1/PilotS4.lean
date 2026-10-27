module

public import CFSG.GH74.Generic.BProg.B1.PilotS4Facts

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS4

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.GH74.L5U5 Subgroup

theorem not_qShape1_of_center_trivial {Kt : Type} [Group Kt] (h1 : QShape1 Kt)
    (hZ : ∀ z : Kt, (∀ g : Kt, g * z = z * g) → z = 1) : False := by
  have hc := IsSL4Model.natCard_center h1
  have hz : Subgroup.center Kt = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    exact hZ z (fun g => Subgroup.mem_center_iff.1 hz g)
  rw [hz, Subgroup.card_bot] at hc
  omega

end CFSG.GH74.Generic.BProg.B1.PilotS4

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg Subgroup

theorem sourceExistsFor_shape4 :
    SourceExistsFor QShape4 := by
  intro G _ _ _hyp _noAlt x K hcirc h4
  exact PilotS5.exists_source_of_four hcirc.1.1.1.1 hcirc.1.1.1.2.2 (PilotS4.center_of_qShape4 h4)
    (PilotS4.exists_four_of_qShape4 h4) (Or.inr (Or.inl h4))

theorem admissibleExistsFor_shape4 :
    AdmissibleExistsFor QShape4 := by
  intro G _ _ _hyp _noAlt x K hcirc h4 A hA
  have hx : orderOf x = 2 := hcirc.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hcirc.1.1.1.2.2
  obtain ⟨-, -, -, hcase⟩ := hA
  obtain ⟨n, hn⟩ := PilotS4.splitGrp_of_qShape4 h4
  rcases hcase with ⟨-, h1⟩ | ⟨E, hEK, hAE, -, hEel, hE4, -⟩
  · exact (PilotS4.not_qShape1_of_center_trivial h1 hn.center).elim
  · have hxK : x ∉ K := PilotS5.not_mem_of_center_trivial hx hK.1 hn.center
    obtain ⟨eK⟩ := PilotS5.hat_equiv_imgBar hK
    exact PilotS5.exists_adm_of_split hx hK hxK (hn.map_equiv eK).splitLike hEK hAE hEel hE4

end CFSG.GH74.Generic.BProg.B1
