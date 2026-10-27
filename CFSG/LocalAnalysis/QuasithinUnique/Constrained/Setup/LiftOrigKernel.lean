module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxTransport
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Actor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FrattiniBasic

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Transport

variable {G : Type} [Group G]

theorem map_oddOrderSubgroup_top (X : Subgroup G) :
    (oddOrderSubgroup (⊤ : Subgroup ↥X)).map X.subtype = oddOrderSubgroup X := by
  unfold oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨-, hodd⟩, rfl⟩
    refine ⟨x.2, ?_⟩
    have h := Subgroup.orderOf_coe x
    rw [← h] at hodd
    exact hodd
  · rintro ⟨hg, hodd⟩
    refine ⟨⟨g, hg⟩, ⟨trivial, ?_⟩, rfl⟩
    have h := Subgroup.orderOf_coe (⟨g, hg⟩ : ↥X)
    rw [← h]
    exact hodd

theorem map_pCore_eq_pCoreOf (X : Subgroup G) :
    (CFSG.pCore 2 ↥X).map X.subtype = pCoreOf 2 X := by
  unfold pCoreOf
  try with_reducible rfl

theorem isTwoReducedIn_top_subgroupOf {X V : Subgroup G} (h : IsTwoReducedIn X V) :
    IsTwoReducedIn (⊤ : Subgroup ↥X) (V.subgroupOf X) := by
  obtain ⟨hVX, hX, hVe, hred⟩ := h
  refine ⟨le_top, fun x _ => (mem_normalizer_subgroupOf_iff hVX x).2 (hX x.2), ?_, ?_⟩
  · exact C1GN.isElemAbelian_map_subtype.mp (by
      rw [Subgroup.map_subgroupOf_eq_of_le hVX]
      exact hVe)
  · intro D _ hDn hD
    have hDX : D.map X.subtype ≤ X := Subgroup.map_subtype_le D
    have hsub : (D.map X.subtype).subgroupOf X = D :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective D
    have hD₀ : D.map X.subtype ≤ Subgroup.centralizer (V : Set G) := by
      refine hred (D.map X.subtype) hDX (fun g hg => ?_) ?_
      · have h1 := hDn (Subgroup.mem_top (⟨g, hg⟩ : ↥X))
        rw [← hsub] at h1
        exact (mem_normalizer_subgroupOf_iff hDX ⟨g, hg⟩).1 h1
      · rintro _ ⟨d, hd, rfl⟩
        obtain ⟨k, hk⟩ := hD d hd
        refine ⟨k, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
        have := Subgroup.mem_centralizer_iff.1 hk ⟨v, hVX hv⟩
          (show (⟨v, hVX hv⟩ : ↥X) ∈ V.subgroupOf X from hv)
        exact congrArg Subtype.val this
    intro d hd
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hD₀ ⟨d, hd, rfl⟩) (v : G) hv)

end Transport

end CFSG.QuasithinUnique.Setup.Lift
