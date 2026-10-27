module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbIndepGroup
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbLeviRad
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbPerfect
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviBQ
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoNode
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.Indep

open scoped commutatorElement
open CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.GN516.Levi CFSG.AGLEmbeddingD2.Tits.GN516.Perf

variable {K S : Type} [Group K] [Finite K] [Group S] [Finite S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

theorem rootGroup_single_le_posUnipotent (k : Fin D.rank) :
    D.rootGroup (Pi.single k 1) ≤ posUnipotent D :=
  rootGroup_le_posUnipotent ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k)
    (ht_single_pos k)

theorem isPGroup_posUnipotent (h : BorelQuotient D n H π M) : IsPGroup 2 ↥(posUnipotent D) :=
  isPGroup_iSup_pos h.extras h.pGroup

theorem map_unipJ_le_normalizer_map_unipRad (h : BorelQuotient D n H π M)
    (J : Set (Fin D.rank)) :
    (unipJ D J).map π ≤ Subgroup.normalizer (((unipRad D J).map π : Subgroup S) : Set S) := by
  have h1 : unipJ D J ≤ parJ D H J := by
    rw [parJ_eq_sup]
    exact le_sup_left
  exact (Subgroup.map_mono (h1.trans (parJ_le_normalizer_unipRad h.ct h.extras J))).trans
    (Subgroup.le_normalizer_map π)

theorem map_unipJ_eq_sup (h : BorelQuotient D n H π M) (J : Set (Fin D.rank)) :
    (unipJ D J).map π =
      (unipRad D J).map π ⊔ ⨆ j ∈ J, (rankOne D.rootGroup j).map π := by
  rw [unipJ_eq_sup h.ct h.extras J, Subgroup.map_sup]
  simp only [Subgroup.map_iSup]

theorem map_rankOne_le_centralizer (h : BorelQuotient D n H π M) {j k : Fin D.rank}
    (hjk : j ≠ k) (hc : D.cartan j k = 0) :
    (rankOne D.rootGroup j).map π ≤
      Subgroup.centralizer (((rankOne D.rootGroup k).map π : Subgroup S) : Set S) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, rankOne_commute h.ct h.extras hjk hc hx hy]

theorem map_rankOne_le_pElementSubgroup_two (h : BorelQuotient D n H π M) (j : Fin D.rank)
    {X : Subgroup S} (hX : (rankOne D.rootGroup j).map π ≤ X) :
    (rankOne D.rootGroup j).map π ≤ pElementSubgroup 2 X := by
  have hα : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem j
  have hα' : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have e : (rankOne D.rootGroup j).map π =
      (D.rootGroup (Pi.single j 1)).map π ⊔ (D.rootGroup (-Pi.single j 1)).map π :=
    Subgroup.map_sup _ _ _
  refine e.le.trans (sup_le ?_ ?_)
  · exact le_pElementSubgroup_two_of_isPGroup ((le_sup_left.trans e.ge).trans hX)
      ((h.pGroup _ hα).map π)
  · exact le_pElementSubgroup_two_of_isPGroup ((le_sup_right.trans e.ge).trans hX)
      ((h.pGroup _ hα').map π)

theorem perfRad_map_unipJ_singleton_le (h : BorelQuotient D n H π M) {J : Set (Fin D.rank)}
    (hJ : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → D.cartan j k = 0) {j : Fin D.rank} (hj : j ∈ J) :
    perfRad ((unipJ D {j}).map π) ≤
      (unipRad D J).map π ⊔ (rankOne D.rootGroup j).map π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xj : Subgroup K := ⨆ k ∈ J \ {j}, D.rootGroup (Pi.single k 1) with hXj
  have hXU : Xj ≤ posUnipotent D := iSup₂_le fun k _ => rootGroup_single_le_posUnipotent k
  refine perfRad_le_of_le_sup (p := 2) (N := Xj.map π) ?_ ?_ ?_
  · rw [unipJ_singleton h j, Subgroup.map_sup]
    refine sup_le (le_sup_of_le_left le_sup_right) ?_
    have hle := posUnipotentExcept_le_of_independent h.ct h.extras hj hJ
    calc (posUnipotentExcept D j).map π ≤ (unipRad D J ⊔ Xj).map π := Subgroup.map_mono hle
      _ = (unipRad D J).map π ⊔ Xj.map π := Subgroup.map_sup _ _ _
      _ ≤ _ := sup_le_sup_right le_sup_left _
  · refine CFSG.LieType.Steinberg.le_normalizer_sup ?_ ?_
    · exact (Subgroup.map_mono (hXU.trans (posUnipotent_le_unipJ J))).trans
        (map_unipJ_le_normalizer_map_unipRad h J)
    · refine le_normalizer_of_le_centralizer ?_
      rw [Subgroup.map_le_iff_le_comap]
      refine iSup₂_le fun k hk => ?_
      have hkj : k ≠ j := fun e => hk.2 (Set.mem_singleton_iff.2 e)
      exact le_sup_left.trans (Subgroup.map_le_iff_le_comap.1
        (map_rankOne_le_centralizer h hkj (hJ k hk.1 j hj hkj)))
  · exact ((isPGroup_posUnipotent h).to_le hXU).map π

theorem isSolvable_of_map (h : BorelQuotient D n H π M) {X : Subgroup K}
    (hs : Group.IsSolvable ↥(X.map π)) : Group.IsSolvable ↥X := by
  let g : ↥X →* ↥(X.map π) := π.subgroupMap X
  haveI : Group.IsSolvable ↥g.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have hcent : ∀ c : ↥g.ker, ∀ x : K, x * (c.1 : K) = (c.1 : K) * x := by
      intro c x
      have hπ : π (c.1 : K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 c.2)
      exact Subgroup.mem_center_iff.1 (h.ker_central _ (MonoidHom.mem_ker.2 hπ)) x
    exact Subtype.ext (Subtype.ext (hcent a b.1.1).symm)
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

theorem isSolvable_map_unipJ_singleton (h : BorelQuotient D n H π M) {j : Fin D.rank}
    (hs : Group.IsSolvable ↥(rankOne D.rootGroup j)) :
    Group.IsSolvable ↥((unipJ D {j}).map π) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI h1 : Group.IsSolvable ↥(unipJ D {j}) := by
    rw [unipJ_singleton h j, sup_comm]
    have hU : Group.IsSolvable ↥(posUnipotentExcept D j) := by
      have := (isPGroup_posUnipotentExcept h j).isNilpotent
      infer_instance
    exact isSolvable_sup_of_le_normalizer hU hs
      (rankOne_le_normalizer_posUnipotentExcept h.ct h.extras j)
  exact Group.isSolvable_of_surjective (π.subgroupMap_surjective (unipJ D {j}))

end CFSG.AGLEmbeddingD2.Tits.GN516.Indep
