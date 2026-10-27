module

public import CFSG.Quasithin.Background.B69E22Link
public import CFSG.Quasithin.Background.E2TwoProofAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace B69K

theorem exists_asHyp_of_component {Γ : Type} [Group Γ] [Finite Γ] {S N : Subgroup Γ}
    (hmp : MinParabolic (⊤ : Subgroup Γ) S N) {L : Subgroup Γ}
    (hL : CFSG.Open.IsComponentOf L ⊤) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (K T' M' : Subgroup Y),
      E2P.ASHyp K T' M' ∧ ∃ π : ↥L →* ↥K, Function.Surjective π := by
  classical
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  have hΓns : ¬ Group.IsSolvable Γ := fun hY => by
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective (f := L.subtype)
      L.subtype_injective
    exact Group.IsPerfect.not_isSolvable ↥L this
  set J : Subgroup Γ := kerIn N ⊤ with hJ
  set φ := QuotientGroup.mk' J with hφ
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hker : φ.ker ≤ N := by
    rw [hφ, QuotientGroup.ker_mk']
    exact kerIn_le
  have hmpQ := hmp.map_of_surjective hsurj hker
  have hJ' : kerIn (N.map φ) ⊤ = ⊥ := by
    rw [kerIn_map_top hsurj hker]
    exact QuotientGroup.map_mk'_self J
  have hnsQ : ¬ Group.IsSolvable (Γ ⧸ J) := fun hs => by
    have := hmp.isSolvable_kerIn
    exact hΓns (Group.isSolvable_of_ker_le_range J.subtype φ
      (by rw [hφ, QuotientGroup.ker_mk', Subgroup.range_subtype]))
  obtain ⟨Ls, hF⟩ := E2P.exists_factor hmpQ hJ' hnsQ
  have hLf : ¬ L ≤ φ.ker := by
    intro hle
    rw [hφ, QuotientGroup.ker_mk'] at hle
    have hJs : Group.IsSolvable ↥J := hmp.isSolvable_kerIn
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥L this
  have hLb := B69.isComponentOf_map_top φ hsurj hL hLf
  have hLssn : Ls.IsSubnormal := (CFSG.Adapters.isSubnormal_top_iff Ls).1 hF.isSubnormal
  have hT2 : IsPGroup 2 ↥(S.map φ) := hmpQ.isSylow.2.1
  obtain ⟨z, hz⟩ := B69.exists_conj_eq_of_component hLb hLssn hF.simple hT2 hF.sup_eq_top
  have e2 : ↥Ls ≃* ↥(L.map φ) :=
    (Ls.equivMapOfInjective (MulAut.conj z).toMonoidHom (MulAut.conj z).injective).trans
      (MulEquiv.subgroupCongr hz.symm)
  have hK := hF.asHyp_autOn
  have hinj := innAut_injective hF.simple hF.nonab
  have e : ↥Ls ≃* ↥((innAut Ls).range.subgroupOf (autOn ⊤ Ls)) :=
    (MonoidHom.ofInjective hinj).trans
      (Subgroup.subgroupOfEquivOfLe (E2P.range_innAut_le Ls)).symm
  haveI : Finite (MulAut ↥Ls) := inferInstanceAs (Finite (↥Ls ≃* ↥Ls))
  refine ⟨↥(autOn ⊤ Ls), inferInstance, inferInstance, _, _, _, hK, ?_⟩
  let π : ↥L →* ↥((innAut Ls).range.subgroupOf (autOn ⊤ Ls)) :=
    e.toMonoidHom.comp (e2.symm.toMonoidHom.comp (φ.subgroupMap L))
  exact ⟨π, e.surjective.comp (e2.symm.surjective.comp (φ.subgroupMap_surjective L))⟩

end B69K

end CFSG.Quasithin
