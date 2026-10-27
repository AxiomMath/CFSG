module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.ExcE6Levi

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

section Injective

variable {k : Type} [Field k] [Finite k]

theorem e6Isogeny_injective_of_card_nine (hk : Nat.card k = 9) :
    Function.Injective (CFSG.LieType.Steinberg.Isogeny.e6Isogeny k) := by
  have hZ : Subgroup.center ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup k) =
      ⊥ := by
    have h1 := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 k).1
    rw [hk] at h1
    have h2 : Nat.gcd 3 (9 - 1) = 1 := by norm_num
    rw [h2] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  rw [← MonoidHom.ker_eq_bot_iff,
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center, hZ]

end Injective

section Image

variable {k : Type} [Field k] [Finite k]

variable (k) in
@[expose] noncomputable def e6EpsK :
    ↥(e6Data_valid.minGroup k) →* ModGL .E6 k :=
  (adjointGroup .E6 k).subtype.comp (e6Isogeny k)

theorem e6EpsK_injective (hε : Function.Injective (e6Isogeny k)) :
    Function.Injective (e6EpsK k) :=
  fun _ _ h => hε (Subtype.ext h)

theorem map_stdRankOne_e6_genK {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    (stdRankOne (e6Datum k) γ).map (e6Isogeny k) = stdRankOne (e6AdjDatum k) γ := by
  change ((e6Datum k).rootGroup γ ⊔
      (e6Datum k).rootGroup (-γ)).map (e6Isogeny k) =
    rootGroup (rootOperatorFamily .E6) k γ ⊔
      rootGroup (rootOperatorFamily .E6) k (-γ)
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (map_e6Isogeny_rootGroup k hγ)
    (map_e6Isogeny_rootGroup k (IsRoot.neg hγ))

private theorem exists_xUnit_of_mem_rootGroup_K (j : Fin (Tag.rank .E6))
    {x : ↥(e6Data_valid.minGroup k)}
    (hx : x ∈ (e6Datum k).rootGroup (Pi.single j 1)) :
    ∃ c : k, e6EpsK k x = xUnit .E6 k j c := by
  have h1 : e6Isogeny k x ∈
      rootGroup (rootOperatorFamily .E6) k (Pi.single j 1) := by
    rw [← map_e6Isogeny_rootGroup k (isRoot_single .E6 j)]
    exact Subgroup.mem_map_of_mem _ hx
  exact (mem_adjRootGroup_single _ _).1 h1

private theorem exists_yUnit_of_mem_rootGroup_K (j : Fin (Tag.rank .E6))
    {x : ↥(e6Data_valid.minGroup k)}
    (hx : x ∈ (e6Datum k).rootGroup (-Pi.single j 1)) :
    ∃ c : k, e6EpsK k x = yUnit .E6 k j c := by
  have h1 : e6Isogeny k x ∈
      rootGroup (rootOperatorFamily .E6) k (-Pi.single j 1) := by
    rw [← map_e6Isogeny_rootGroup k (IsRoot.neg (isRoot_single .E6 j))]
    exact Subgroup.mem_map_of_mem _ hx
  exact (mem_adjRootGroup_neg_single _ _).1 h1

private theorem exists_mem_rootGroup_of_xUnit_K (j : Fin (Tag.rank .E6)) (c : k) :
    ∃ x ∈ (e6Datum k).rootGroup (Pi.single j 1),
      e6EpsK k x = xUnit .E6 k j c := by
  have hmem : (⟨xUnit .E6 k j c, xUnit_mem_adjointGroup _ _⟩ :
      ↥(adjointGroup .E6 k)) ∈
        rootGroup (rootOperatorFamily .E6) k (Pi.single j 1) :=
    (mem_adjRootGroup_single _ _).2 ⟨c, rfl⟩
  rw [← map_e6Isogeny_rootGroup k (isRoot_single .E6 j)] at hmem
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
  exact ⟨x, hx, congrArg Subtype.val hxe⟩

private theorem exists_mem_rootGroup_of_yUnit_K (j : Fin (Tag.rank .E6)) (c : k) :
    ∃ x ∈ (e6Datum k).rootGroup (-Pi.single j 1),
      e6EpsK k x = yUnit .E6 k j c := by
  have hmem : (⟨yUnit .E6 k j c, yUnit_mem_adjointGroup _ _⟩ :
      ↥(adjointGroup .E6 k)) ∈
        rootGroup (rootOperatorFamily .E6) k (-Pi.single j 1) :=
    (mem_adjRootGroup_neg_single _ _).2 ⟨c, rfl⟩
  rw [← map_e6Isogeny_rootGroup k (IsRoot.neg (isRoot_single .E6 j))] at hmem
  obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.1 hmem
  exact ⟨x, hx, congrArg Subtype.val hxe⟩

theorem map_iSup_rankOne_e6K :
    (⨆ i : Fin 5, CFSG.LieType.CurtisTits.rankOne (e6Datum k).rootGroup (path6 i)).map
      (e6EpsK k) = subsystemGroup .E6 k JE6 := by
  refine (Subgroup.map_iSup _ _).trans (le_antisymm (iSup_le fun i => ?_) ?_)
  · have hj : path6 i ∈ JE6 := fun h => path6_ne i (Fin.ext h)
    refine (Subgroup.map_sup _ _ _).le.trans (sup_le ?_ ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := exists_xUnit_of_mem_rootGroup_K (path6 i) hx
      rw [hc]
      exact xUnit_mem_subsystemGroup hj c
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc⟩ := exists_yUnit_of_mem_rootGroup_K (path6 i) hx
      rw [hc]
      exact yUnit_mem_subsystemGroup hj c
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, c, rfl | rfl⟩
    · obtain ⟨i, rfl⟩ := exists_path6_eq j hj
      obtain ⟨x, hx, hxe⟩ := exists_mem_rootGroup_of_xUnit_K (path6 i) c
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map.2 ⟨x, Subgroup.mem_sup_left hx, hxe⟩)
    · obtain ⟨i, rfl⟩ := exists_path6_eq j hj
      obtain ⟨x, hx, hxe⟩ := exists_mem_rootGroup_of_yUnit_K (path6 i) c
      exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_map.2 ⟨x, Subgroup.mem_sup_right hx, hxe⟩)

end Image

section Commute

variable {k : Type} [Field k]

theorem commutes_iSup_rankOne_theta_e6K :
    Commutes (⨆ i : Fin 5, CFSG.LieType.CurtisTits.rankOne (e6Datum k).rootGroup (path6 i))
      ((e6Datum k).rootGroup theta6 ⊔ (e6Datum k).rootGroup (-theta6)) := by
  have hext := e6Datum_steinbergExtras k
  set D := e6Datum k with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, IsLongestRoot D (Pi.single i 1) := fun i => isLongest_single_E6 rfl _ i
  let z0 : Fin D.rank := ⟨0, by show 0 < 6; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  have hθ : theta6 ∈ D.roots := RRoot.mem_roots D.isFiniteType rroot_theta6
  refine commutes_iSup_left.mpr fun i => ?_
  exact commutes_rankOne_theta D hext hℓ hθ (k := path6 i)
    ((coroot_apply D.cartan (path6 i) theta6).trans (coroot_theta6 _ (path6_ne i)))

end Commute

end CFSG.OddStandard.HigherRank.F3
