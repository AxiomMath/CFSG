module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbNodes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbLeviRad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviNode
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbIndepAbstract
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbIndepLie

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Indep

open scoped commutatorElement
open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes CFSG.AGLEmbeddingD2.Tits.GN516.Levi

variable {K S : Type} [Group K] [Finite K] [Group S] [Finite S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

@[expose] def orbitSet (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut S))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank) : Set (Fin D.rank) :=
  Set.range fun a : ↥𝒜 => nodeHom h 𝒜 h𝒜 a i

theorem image_orbitSet (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut S))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank) (a : ↥𝒜) :
    nodePerm h a.1 (h𝒜 a.1 a.2) '' orbitSet h 𝒜 h𝒜 i = orbitSet h 𝒜 h𝒜 i := by
  ext j
  simp only [Set.mem_image, orbitSet, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    exact ⟨a * b, by rw [map_mul, Equiv.Perm.mul_apply, nodeHom_apply]⟩
  · rintro ⟨b, rfl⟩
    refine ⟨nodeHom h 𝒜 h𝒜 (a⁻¹ * b) i, ⟨a⁻¹ * b, rfl⟩, ?_⟩
    rw [← nodeHom_apply, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem map_map_unipJ_orbitSet (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut S))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank) (a : ↥𝒜) :
    ((unipJ D (orbitSet h 𝒜 h𝒜 i)).map π).map a.1.toMonoidHom =
      (unipJ D (orbitSet h 𝒜 h𝒜 i)).map π := by
  rw [map_unipJ_nodePerm h a.1 (h𝒜 a.1 a.2), image_orbitSet]

theorem map_map_unipJ_singleton (h : BorelQuotient D n H π M) (𝒜 : Subgroup (MulAut S))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (a : ↥𝒜) (j : Fin D.rank) :
    ((unipJ D {j}).map π).map a.1.toMonoidHom = (unipJ D {nodeHom h 𝒜 h𝒜 a j}).map π := by
  rw [map_unipJ_nodePerm h a.1 (h𝒜 a.1 a.2), Set.image_singleton, ← nodeHom_apply]

theorem indep_alternative (h : BorelQuotient D n H π M) (hnode : ∀ j, NodeLevi D j)
    (𝒜 : Subgroup (MulAut S))
    (h𝒜 : ∀ α ∈ 𝒜, ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π)
    (i : Fin D.rank)
    (hind : ∀ j ∈ orbitSet h 𝒜 h𝒜 i, ∀ k ∈ orbitSet h 𝒜 h𝒜 i, j ≠ k → D.cartan j k = 0) :
    Group.IsSolvable ↥((unipJ D (orbitSet h 𝒜 h𝒜 i)).map π) ∨
    ∃ C : Subgroup S, C ≤ pElementSubgroup 2 C ∧ C ≤ (unipJ D (orbitSet h 𝒜 h𝒜 i)).map π ∧
      (unipJ D (orbitSet h 𝒜 h𝒜 i)).map π ≤ Subgroup.normalizer (C : Set S) ∧
      (unipJ D (orbitSet h 𝒜 h𝒜 i)).map π ≤ ⨆ a : ↥𝒜, C.map a.1.toMonoidHom ∧
      ∀ a : ↥𝒜, nodeHom h 𝒜 h𝒜 a i ≠ i →
        ⁅C, C.map a.1.toMonoidHom⁆ ≤ pCoreOf 2 ((unipJ D (orbitSet h 𝒜 h𝒜 i)).map π) := by
  have hLN : ∀ j, (rankOne D.rootGroup j).map π ≤ (unipJ D {j}).map π := fun j =>
    Subgroup.map_mono (rankOne_le_unipJ (Set.mem_singleton j))
  have hNa : ∀ (a : ↥𝒜) (j : Fin D.rank), ((unipJ D {j}).map π).map a.1.toMonoidHom =
      (unipJ D {nodeHom h 𝒜 h𝒜 a j}).map π := fun a j => map_map_unipJ_singleton h 𝒜 h𝒜 a j
  have hsolN : ∀ j ∈ orbitSet h 𝒜 h𝒜 i, Group.IsSolvable ↥((unipJ D {j}).map π) ↔
      Group.IsSolvable ↥((unipJ D {i}).map π) := by
    rintro _ ⟨a, rfl⟩
    rw [← hNa a i]
    exact isSolvable_map_equiv_iff a.1 _
  have hdich : (∀ j ∈ orbitSet h 𝒜 h𝒜 i, Group.IsSolvable ↥((rankOne D.rootGroup j).map π)) ∨
      ∀ j ∈ orbitSet h 𝒜 h𝒜 i, ⁅(rankOne D.rootGroup j).map π, (rankOne D.rootGroup j).map π⁆ =
        (rankOne D.rootGroup j).map π := by
    by_cases hs : Group.IsSolvable ↥(rankOne D.rootGroup i)
    · left
      intro j hj
      have h1 : Group.IsSolvable ↥((unipJ D {j}).map π) :=
        (hsolN j hj).2 (isSolvable_map_unipJ_singleton h hs)
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (hLN j))
        (Subgroup.inclusion_injective (hLN j))
    · right
      intro j hj
      rcases hnode j with hsj | hq
      · exfalso
        apply hs
        have h1 : Group.IsSolvable ↥((unipJ D {i}).map π) :=
          (hsolN j hj).1 (isSolvable_map_unipJ_singleton h hsj)
        refine isSolvable_of_map h ?_
        exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (hLN i))
          (Subgroup.inclusion_injective (hLN i))
      · exact commutator_map_eq_of_perfect π hq.1
  exact indep_abstract 𝒜 (nodeHom h 𝒜 h𝒜) i (orbitSet h 𝒜 h𝒜 i) rfl
    (fun j => (rankOne D.rootGroup j).map π) (fun j => (unipJ D {j}).map π)
    ((unipRad D (orbitSet h 𝒜 h𝒜 i)).map π) ((posUnipotent D).map π)
    ((unipJ D (orbitSet h 𝒜 h𝒜 i)).map π)
    (map_unipJ_eq_sup h _) (Subgroup.map_mono (unipRad_le_posUnipotent _))
    ((isPGroup_posUnipotent h).map π) (fun a => h𝒜 a.1 a.2)
    (map_unipJ_le_normalizer_map_unipRad h _) (fun a => map_map_unipJ_orbitSet h 𝒜 h𝒜 i a)
    (fun j hj k hk hjk => map_rankOne_le_centralizer h hjk (hind j hj k hk hjk)) hNa hLN
    (fun j hj => perfRad_map_unipJ_singleton_le h hind hj)
    (fun j _ X hX => map_rankOne_le_pElementSubgroup_two h j hX) hdich

end CFSG.AGLEmbeddingD2.Tits.GN516.Indep
