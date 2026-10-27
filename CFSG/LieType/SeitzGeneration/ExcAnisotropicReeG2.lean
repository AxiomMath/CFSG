module

public import CFSG.LieType.SeitzGeneration.ExcReeG2Rank
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeG2
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2

theorem false_of_inner_plane_of_no_plane {C : Type*} [Group C] {p : ℕ}
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C))
    (hno : ∀ F : Subgroup C, IsElemAbelian p F → Nat.card F = p ^ 2 → False)
    {E : Subgroup (MulAut C)} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hin : E ≤ (MulAut.conj : C →* MulAut C).range) : False := by
  have hmap : (E.comap (MulAut.conj : C →* MulAut C)).map (MulAut.conj : C →* MulAut C) = E :=
    Subgroup.map_comap_eq_self hin
  exact hno _ (isElemAbelian_comap_of_injective _ hinj hE) (by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hc])

section Ree


theorem no_plane_cat_reeG2 {m : ℕ} (hv : (LieTypeIndex.reeG2 m).Valid) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (F : Subgroup (Cat ⟨.reeG2 m, hv⟩)) (hF : IsElemAbelian p F)
    (hc : Nat.card F = p ^ 2) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := exists_reeGamma_equiv_cat_G2 hv
  have hm1 : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa [LieTypeIndex.inStandardRange_iff] using h
  have : IsElementaryAbelian p ↥F := isElementaryAbelian_of_isElemAbelian hF
  have hF₁el : IsElementaryAbelian p ↥(F.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hF₂el : IsElementaryAbelian p
      ↥((F.map e.toMonoidHom).map (ReeTag.G2.reeGamma X m).subtype) :=
    IsElementaryAbelian.map _
  refine no_plane_reeGamma_G2 hm1 hX hp hp3 (Subgroup.map_subtype_le _) hF₂el ?_
  rw [Subgroup.card_map_of_injective (ReeTag.G2.reeGamma X m).subtype_injective,
    Subgroup.card_map_of_injective e.injective, hc]

theorem seitzExcAnisotropicReeG2_vacuous : SeitzExcAnisotropicReeG2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, ⟨m, rfl⟩, -, -⟩
  have hp3 : p ≠ 3 := by simpa using hpd
  have hp4 : 3 < p := by
    have := hp.two_le
    omega
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := exists_reeGamma_equiv_cat_G2 hv
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.reeG2 m, hv⟩ →* MulAut _) :=
    conj_injective_of_mulEquiv e
      (conj_injective_of_center_eq_bot (ReeTag.center_reeGamma_G2_eq_bot hX))
  exact (false_of_inner_plane_of_no_plane hinj
    (fun F hF hc' => no_plane_cat_reeG2 hv hp hp4 F hF hc') hE hc hin).elim

end Ree

end CFSG.LieType.SeitzGeneration
