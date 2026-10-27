module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5aAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Interface
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Setup.X5

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.Quasithin
  CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

theorem conj_mem_autOn {G : Type*} [Group G] {H L : Subgroup G} (hLH : L ≤ H) (l : L) :
    (MulAut.conj l : MulAut L) ∈ autOn H L := by
  have hl : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l.2
  refine Subgroup.mem_map.mpr ⟨⟨(l : G), hl⟩, Subgroup.mem_subgroupOf.mpr (hLH l.2), ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  show ((conjAct L ⟨(l : G), hl⟩ x : L) : G) = ((MulAut.conj l x : L) : G)
  rw [conjAct]
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem no_unitary_three_at_three_component (hT : ActorComponentTransfer) {V : Type} [CommGroup V]
    [Finite V] {H T M E : Subgroup (MulAut V)} (hA : ActorBase V H T M E)
    (hns : ¬ Group.IsSolvable H) {L : Subgroup (MulAut V)} (hL : IsComponentIn L H) :
    ¬ CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 3 3 1 := by
  intro hmodel
  obtain ⟨hSyl, -, P, hP⟩ := hT V H T M E hA hns L hL
  have hqs : CFSG.IsQuasisimple L :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hL.1)).mp hL.2.1
  have : Group.IsPerfect L := hqs.1
  have hinj := PerfectAutomorphisms.centerQuotientHom_injective L
  set Φ := PerfectAutomorphisms.centerQuotientHom L with hΦ
  have hD : (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range ≤
      (autOn H L).map Φ := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨MulAut.conj l, conj_mem_autOn hL.1 l, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj l⟩
  have hSyl' : IsSylowTwoOf ((autOn T L).map Φ) ((autOn H L).map Φ) :=
    isSylowTwoOf_map_of_injective hinj hSyl
  exact not_isUniqueMaxOver_of_two_gen
    (unitary_three_at_three_overgroups_not_minimal hmodel hD hSyl')
    ⟨P.map Φ, IsUniqueMaxOver.map hinj hP⟩

end CFSG.QuasithinUnique.Setup.X5
