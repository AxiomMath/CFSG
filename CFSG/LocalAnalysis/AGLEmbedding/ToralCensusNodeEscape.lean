module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeWitness
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeGroup
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrStruct
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrFrattini

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {K : Type*} {Y : Type} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem iSup_torus_le_normalizer_posUnipotentExcept
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (i : Fin D.rank) :
    (⨆ k, H k) ≤ Subgroup.normalizer (posUnipotentExcept D i : Set K) := by
  refine le_normalizer_iSup₂ fun t ht γ hγ y hy => ?_
  exact (le_iSup₂_of_le (f := fun γ (_ : γ ∈ (RootSystem.ofCartan D.isFiniteType
    D.divisible).posExcept i) => D.rootGroup γ) γ hγ le_rfl)
    ((Subgroup.mem_normalizer_iff.1 (iSup_le_normalizer_rootGroup hct hγ.1.1 ht) y).1 hy)

theorem exists_conj_mem_rankOne_of_single [Finite K] [Finite Y] (h : BorelQuotient D n H π M)
    {J : Subgroup Y} (hBJ : (borel D H).map π ≤ J) {i : Fin D.rank}
    (hI : negIndices D (J.comap π) = {i}) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {u : Y}
    (hu : u ∈ perfectJoin J) (hup : u ^ p = 1) :
    ∃ g ∈ J, g * u * g⁻¹ ∈ (rankOne D.rootGroup i).map π := by
  have hBA : borel D H ≤ J.comap π := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hi : i ∈ negIndices D (J.comap π) := by rw [hI]; rfl
  set T := (⨆ k, H k).map π with hT
  set R := (posUnipotentExcept D i).map π with hR
  set Li := (rankOne D.rootGroup i).map π with hLi
  have hLiJ : Li ≤ J :=
    (Subgroup.map_mono (rankOne_le_of_mem_negIndices hBA hi)).trans (Subgroup.map_comap_le _ _)
  have hRJ : R ≤ J := (Subgroup.map_mono ((posUnipotentExcept_le_posUnipotent i).trans
    posUnipotent_le_borel)).trans hBJ
  have hJ : J ≤ T ⊔ (Li ⊔ R) := by
    rw [eq_map_borel_sup_of_le h.ct h.extras h.surj hBJ]
    refine sup_le ?_ (iSup₂_le fun j hj => ?_)
    · rw [CFSG.LieType.Steinberg.borel, Subgroup.map_sup, posUnipotent_eq_sup h.extras i,
        Subgroup.map_sup]
      refine sup_le le_sup_left (sup_le (le_sup_of_le_right le_sup_right) ?_)
      exact le_sup_of_le_right (le_sup_of_le_left (Subgroup.map_mono le_sup_left))
    · rw [hI] at hj
      rw [Set.mem_singleton_iff.1 hj]
      exact le_sup_of_le_right le_sup_left
  have hTN : T ≤ Subgroup.normalizer ((Li ⊔ R : Subgroup Y) : Set Y) := fun t ht =>
    ParabAutIrr.mem_normalizer_sup
      (((Subgroup.map_mono (iSup_torus_le_normalizer_rankOne h.ct i)).trans
        (Subgroup.le_normalizer_map π)) ht)
      (((Subgroup.map_mono (iSup_torus_le_normalizer_posUnipotentExcept h.ct i)).trans
        (Subgroup.le_normalizer_map π)) ht)
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.torus_mul_comm ha hb]
  have hPN := perfectJoin_le_of_le_sup hJ hTN hTc
  have hR2 : IsPGroup 2 R := ((isPGroup_iSup_pos h.extras h.pGroup).to_le
    (posUnipotentExcept_le_posUnipotent i)).map π
  have hLR : Li ≤ Subgroup.normalizer (R : Set Y) :=
    (Subgroup.map_mono (rankOne_le_normalizer_posUnipotentExcept h.ct h.extras i)).trans
      (Subgroup.le_normalizer_map π)
  obtain ⟨g, hg, hgu⟩ := exists_conj_mem_of_sup hp hp2 hR2 hLR (hPN hu) (k := 1)
    (by rwa [pow_one])
  exact ⟨g, sup_le hLiJ hRJ hg, hgu⟩

theorem exists_escape_of_witness (h : BorelQuotient D n H π M) {J : Subgroup Y}
    (hBJ : (borel D H).map π ≤ J) {i k m : Fin D.rank} (hk : k ∉ negIndices D (J.comap π))
    {x : K} {w : (coxeterMatrix D.isFiniteType).Group} (hx : ActsAs D x w)
    (hpos : 0 < weylAction D.isFiniteType w (Pi.single m 1) k)
    (hm : ⁅rankOne D.rootGroup m, rankOne D.rootGroup m⁆ = rankOne D.rootGroup m)
    (hcomm : Commutes (rankOne D.rootGroup i)
      ((rankOne D.rootGroup m).map (MulAut.conj x).toMonoidHom))
    {y : Y} (hy : y ∈ (rankOne D.rootGroup i).map π) :
    ∃ P : Subgroup Y, ⁅P, P⁆ = P ∧ (∀ z ∈ P, z * y = y * z) ∧ ¬ P ≤ J :=
  ⟨_, map_rankOne_conj_perfect π x hm, fun z hz => ((hcomm.map π) y hy z hz).symm,
    map_rankOne_conj_not_le h.ct h.extras hBJ hk hx hpos⟩

end CFSG.AGLEmbedding.ToralCensus
