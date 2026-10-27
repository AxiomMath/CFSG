module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Interface
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X35 CFSG.Quasithin CFSG.Blueprint
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom
  centerQuotientHom_injective onCenterQuotient_apply_mk)
open CFSG.LocalAnalysis.ComponentInitial (isQuasisimple_congr)

section CenterQuotient

variable {G : Type} [Group G]

theorem inner_le_autOn {H L : Subgroup G} (hLH : L ≤ H) : inner ↥L ≤ autOn H L := by
  rintro _ ⟨l, rfl⟩
  have hl : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l.2
  refine Subgroup.mem_map.mpr ⟨⟨(l : G), hl⟩, Subgroup.mem_subgroupOf.mpr (hLH l.2), ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  show ((conjAct L ⟨(l : G), hl⟩ x : L) : G) = ((MulAut.conj l x : L) : G)
  rw [conjAct]
  simp [Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem inner_le_map_centerQuotientHom (L : Subgroup G) :
    inner (↥L ⧸ Subgroup.center ↥L) ≤ (inner ↥L).map (centerQuotientHom ↥L) := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨MulAut.conj l, ⟨l, rfl⟩, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj l⟩

end CenterQuotient

theorem false_of_actorComponentTransfer (hT : ActorComponentTransfer) {V : Type} [CommGroup V]
    [Finite V] {H T M E : Subgroup (MulAut V)} (hA : ActorBase V H T M E)
    (hns : ¬ Group.IsSolvable H) {L : Subgroup (MulAut V)} (hL : IsComponentIn L H)
    (hX : TwoGeneratingSylowOvergroups (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨hSyl, -, P, hP⟩ := hT V H T M E hA hns L hL
  have hqs : CFSG.IsQuasisimple L :=
    (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hL.1)).mp hL.2.1
  have : Group.IsPerfect L := hqs.1
  have hinj := centerQuotientHom_injective ↥L
  have hD : inner (↥L ⧸ Subgroup.center ↥L) ≤ (autOn H L).map (centerQuotientHom ↥L) :=
    (inner_le_map_centerQuotientHom L).trans (Subgroup.map_mono (inner_le_autOn hL.1))
  have hSyl' : IsSylowTwoOf ((autOn T L).map (centerQuotientHom ↥L))
      ((autOn H L).map (centerQuotientHom ↥L)) := isSylowTwoOf_map_of_injective hinj hSyl
  exact not_isUniqueMaxOver_of_two_gen (hX _ hD _ hSyl')
    ⟨P.map (centerQuotientHom ↥L), IsUniqueMaxOver.map hinj hP⟩

theorem no_even_triality_or_large_Ree_component
    (hT : ActorComponentTransfer) {V : Type}
    [CommGroup V] [Finite V] {H T M E : Subgroup (MulAut V)} (hA : ActorBase V H T M E)
    (hns : ¬ Group.IsSolvable H) {L : Subgroup (MulAut V)} (hL : IsComponentIn L H) (f : ℕ) :
    ¬ ChevalleyExceptionalModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 2 f ∧
      ¬ ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 2 f :=
  ⟨fun h => false_of_actorComponentTransfer hT hA hns hL
      (even_triality_model_two_extensions h).2.1,
    fun h => false_of_actorComponentTransfer hT hA hns hL
      (large_Ree_model_two_extensions h).2.1⟩

end CFSG.QuasithinUnique.Setup.X6
