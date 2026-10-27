module

public import CFSG.GH74.QTGen4.U42.ModelCoordsB
public import CFSG.GH74.QTGen4.U42.CoordsB
public import CFSG.GH74.QTGen4.U42.CoordsC

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5 CFSG.Quasithin.H13.F431.U42 U42F431

theorem exists_model_coords_relabelled :
    ∃ e : ↥P2 ≃* Mof (alternatingGroup (Fin 5)),
      (∀ (v : Y) (hv : v ∈ Vsub),
        ((e ⟨v, Vsub_le_P2 hv⟩ : Mof _) : Mc) =
          SemidirectProduct.inl (pact sigma0 (psiEq ⟨v, hv⟩))) ∧
      ∀ g : ↥P2, ((e g : Mof _) : Mc).right = permOf4 g := by
  have hVT : modelCoordData.V ≤ T.subgroupOf P2 := fun x hx =>
    Subgroup.mem_subgroupOf.2 (Vsub_le_T (Subgroup.mem_subgroupOf.1 hx))
  have hcard : Nat.card (T.subgroupOf P2) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T_le_P2').toEquiv, card_T]
  have hT : IsPGroup 2 (T.subgroupOf P2) := IsPGroup.of_card (n := 6) (hcard.trans (by norm_num))
  have hTi : ¬ 2 ∣ (T.subgroupOf P2).index := by
    have hi := Subgroup.index_mul_card (H := T.subgroupOf P2)
    rw [hcard, card_P2] at hi
    have hidx : (T.subgroupOf P2).index = 15 := by omega
    rw [hidx]
    decide
  have hρT : ∀ t ∈ T.subgroupOf P2, InK4 (modelCoordData.ρ t) := by
    intro t ht
    exact (model_T_iff t).1 (Subgroup.mem_subgroupOf.1 ht)
  have hK4 : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → ∃ t ∈ T.subgroupOf P2, modelCoordData.ρ t = σ := by
    intro σ hσ
    obtain ⟨t, htT, htp⟩ := exists_T_permOf4 σ hσ
    exact ⟨t, Subgroup.mem_subgroupOf.2 htT, htp⟩
  obtain ⟨A, hA, hA'⟩ :=
    modelCoordData.exists_complement_plain (T.subgroupOf P2) hVT hT hTi hρT hK4
  obtain ⟨e4, he4V, he4R⟩ := CoordData.equiv_of_complement modelCoordData A hA hA'
  have hrange : permHom4.range = alternatingGroup (Fin 5) := by
    have hle : permHom4.range ≤ alternatingGroup (Fin 5) := by
      rintro _ ⟨g, rfl⟩
      rw [Equiv.Perm.mem_alternatingGroup, permHom4_apply, permOf4_apply]
      simp [Equiv.Perm.sign_mul, sign_permOf_eq_one g]
    have hmap : permHom4.range = permHom.range.map (MulAut.conj sigma0).toMonoidHom :=
      MonoidHom.range_comp _ _
    have hcardR : Nat.card permHom4.range = 60 := by
      rw [hmap, Subgroup.card_map_of_injective (f := (MulAut.conj sigma0).toMonoidHom)
        (MulAut.conj sigma0).injective, card_range_permHom]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [card_alt5, hcardR]))
  have h1 : Mof permHom4.range = Mof (alternatingGroup (Fin 5)) := by rw [hrange]
  let e : ↥P2 ≃* Mof (alternatingGroup (Fin 5)) := e4.trans (MulEquiv.subgroupCongr h1)
  refine ⟨e, ?_, ?_⟩
  · intro v hv
    exact he4V ⟨⟨v, Vsub_le_P2 hv⟩, Subgroup.mem_subgroupOf.2 hv⟩
  · intro g
    exact he4R g

end CFSG.GH74.QTGen4.U42
