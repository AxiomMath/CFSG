module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviBorelFields
import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLeviCenter
import CFSG.LocalAnalysis.AGLEmbeddingD2.ParabLeviRankOne
import CFSG.GroupTheory.PCore.InfPCoreOf
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackage

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.ABGLocalTools CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData Subgroup
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {e : ℕ} {J : Set (Fin D.rank)}

omit [Finite K] in
private theorem nodeComponent_ne_univ {D : UniversalRootDatum K} {J : Set (Fin D.rank)}
    {i : Fin D.rank} (hi : i ∈ J) (hJ : J ≠ Set.univ) : nodeComponent D J i ≠ Set.univ := by
  have hsub := nodeComponent_subset hi
  intro h
  exact hJ (Set.eq_univ_of_univ_subset (by rwa [h] at hsub))

omit [Finite K] in
private theorem nodeComponent_eq_singleton_of_ncard_eq_one {D : UniversalRootDatum K}
    {J : Set (Fin D.rank)} {i : Fin D.rank}
    (h1 : (nodeComponent D J i).ncard = 1) : nodeComponent D J i = {i} := by
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
  have hai : a = i := by
    have hmem : i ∈ ({a} : Set (Fin D.rank)) := ha ▸ mem_nodeComponent_self J i
    simpa [eq_comm] using hmem
  rwa [hai] at ha

omit [Finite K] in
private theorem two_le_ncard_of_ncard_ne_one {D : UniversalRootDatum K}
    {J : Set (Fin D.rank)} {i : Fin D.rank}
    (h1 : (nodeComponent D J i).ncard ≠ 1) : 2 ≤ (nodeComponent D J i).ncard := by
  have hpos : 0 < (nodeComponent D J i).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨i, mem_nodeComponent_self J i⟩
  omega

private theorem eq_one_of_mem_center_of_pow_two_eq_one {G : Type} [Group G]
    (hpc : CFSG.pCore 2 G = ⊥) {z : G} (hz : z ∈ Subgroup.center G) {k : ℕ}
    (hzk : z ^ 2 ^ k = 1) : z = 1 := by
  have hcard : Nat.card ↥(Subgroup.zpowers z) = orderOf z := Nat.card_zpowers z
  have hpz : IsPGroup 2 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card_dvd_pow (n := k) (by
      rw [hcard]
      exact orderOf_dvd_of_pow_eq_one hzk)
  rw [Subgroup.zpowers_eq_closure] at hpz
  have hnorm : (Subgroup.closure ({z} : Set G)).Normal := by
    apply Subgroup.normal_of_le_center
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rwa [hy]
  have hcore : Subgroup.closure ({z} : Set G) ≤ CFSG.pCore 2 G :=
    le_sSup ⟨hnorm, hpz⟩
  have hmem : z ∈ Subgroup.closure ({z} : Set G) := Subgroup.subset_closure rfl
  have hz' : z ∈ CFSG.pCore 2 G := hcore hmem
  rw [hpc] at hz'
  simpa using hz'

omit [Finite K] in
theorem borelLeviSet_pCore_eq_bot (h : BorelQuotient D n H π e) (hfac : GomiLeviFactorsMap D π)
    (hJ : J ≠ Set.univ) {A : Subgroup Y} (hA : A ∈ borelLeviSet D π J) :
    CFSG.pCore 2 ↥A = ⊥ := by
  obtain ⟨i, hiJ, rfl⟩ := hA
  by_cases h1 : (nodeComponent D J i).ncard = 1
  · rw [nodeComponent_eq_singleton_of_ncard_eq_one h1]
    exact BorelQuotient.pCore_map_leviM_singleton_eq_bot h i
  · exact GomiLeviFactor.pCore_eq_bot
      (hfac _ (isNodeConnected_nodeComponent hiJ)
        (two_le_ncard_of_ncard_ne_one h1) (nodeComponent_ne_univ hiJ hJ))

omit [Finite K] in
theorem borelLeviSet_inf_eq_bot (h : BorelQuotient D n H π e) (hfac : GomiLeviFactorsMap D π)
    (hJ : J ≠ Set.univ) {A : Subgroup Y} (hA : A ∈ borelLeviSet D π J) :
    pCoreOf 2 ((parJ D H J).map π) ⊓ A = ⊥ := by
  have hAle : A ≤ (parJ D H J).map π := borelLeviSet_le hA
  have hpc : pCoreOf 2 A = ⊥ := by
    rw [show pCoreOf 2 A = (CFSG.pCore 2 ↥A).map A.subtype from rfl,
      borelLeviSet_pCore_eq_bot h hfac hJ hA, Subgroup.map_bot]
  have hinf : A ⊓ pCoreOf 2 ((parJ D H J).map π) ≤ pCoreOf 2 A :=
    inf_pCoreOf_le_pCoreOf 2 hAle
  have hzero : A ⊓ pCoreOf 2 ((parJ D H J).map π) = ⊥ :=
    le_bot_iff.mp (hinf.trans (le_of_eq hpc))
  rw [inf_comm]
  exact hzero

theorem borelLeviSet_center_commutator_le (h : BorelQuotient D n H π e)
    (hfac : GomiLeviFactorsMap D π) (hJ : J ≠ Set.univ) {A : Subgroup Y}
    (hA : A ∈ borelLeviSet D π J) :
    ⁅(center ↥A).map A.subtype, (parJ D H J).map π⁆ ≤ pCoreOf 2 ((parJ D H J).map π) := by
  obtain ⟨i, hiJ, rfl⟩ := hA
  set C := nodeComponent D J i with hC
  have hCJ : C ⊆ J := by rw [hC]; exact nodeComponent_subset hiJ
  have hmemA : (leviM D C).map π ∈ borelLeviSet D π J := by
    refine ⟨i, hiJ, ?_⟩
    rw [hC]
  have hpc : CFSG.pCore 2 ↥((leviM D C).map π) = ⊥ :=
    borelLeviSet_pCore_eq_bot h hfac hJ hmemA
  have h0 : ∀ k ∈ C, ∀ l ∈ J, l ∉ C → D.cartan k l = 0 := by
    intro k hk l hl hln
    have hne : nodeComponent D J i ≠ nodeComponent D J l := by
      intro heq
      apply hln
      rw [hC, heq]
      exact mem_nodeComponent_self J l
    exact cartan_eq_zero_of_nodeComponent_ne hiJ hl hne hk (mem_nodeComponent_self J l)
  have hodd : ∀ z ∈ Subgroup.center ↥((leviM D C).map π), ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 :=
    fun z hz k hzk => eq_one_of_mem_center_of_pow_two_eq_one hpc hz hzk
  exact (BorelQuotient.commutator_map_center_le h hCJ h0 hodd).trans (map_leviRad_le_pCoreOf h J)

omit [Finite Y] in
theorem borelLeviSet_factor (h : BorelQuotient D n H π e) (hfac : GomiLeviFactorsMap D π)
    (hJ : J ≠ Set.univ) {A : Subgroup Y} (hA : A ∈ borelLeviSet D π J) :
    IsGomiChevTwo ↥A ∨ Nonempty (↥A ≃* Equiv.Perm (Fin 6)) ∨
      ⊤ ⊓ normalizer (((posUnipotent D).map π : Subgroup Y) : Set Y) ⊓ A ⋖ A := by
  obtain ⟨i, hiJ, rfl⟩ := hA
  by_cases h1 : (nodeComponent D J i).ncard = 1
  · rw [nodeComponent_eq_singleton_of_ncard_eq_one h1]
    right
    right
    rw [BorelQuotient.normalizer_map_posUnipotent h, top_inf_eq]
    exact BorelQuotient.map_borel_inf_map_leviM_singleton_covBy h i
  · have hf : GomiLeviFactor ↥((leviM D (nodeComponent D J i)).map π) :=
      hfac _ (isNodeConnected_nodeComponent hiJ)
        (two_le_ncard_of_ncard_ne_one h1) (nodeComponent_ne_univ hiJ hJ)
    change IsGomiChevTwo ↥((leviM D (nodeComponent D J i)).map π) ∨
      Nonempty (↥((leviM D (nodeComponent D J i)).map π) ≃* Equiv.Perm (Fin 6)) at hf
    rcases hf with hch | hS
    · exact Or.inl hch
    · exact Or.inr (Or.inl hS)

theorem isGomiLeviPackage_borelLeviSet (h : BorelQuotient D n H π e)
    (hfac : GomiLeviFactorsMap D π) (hJ : J ≠ Set.univ) :
    IsGomiLeviPackage ⊤ ((posUnipotent D).map π) ((parJ D H J).map π) (borelLeviSet D π J) where
  le_parabolic _ hA := borelLeviSet_le hA
  inf_eq_bot _ hA := borelLeviSet_inf_eq_bot h hfac hJ hA
  commute _ h₁ _ h₂ hne := borelLeviSet_commute h h₁ h₂ hne
  pElementSubgroup_eq _ hA := borelLeviSet_pElementSubgroup_eq h hA
  sylow_le := map_posUnipotent_le h J
  normal _ hA := map_parJ_le_normalizer_pCoreOf_sup h hA
  center_commutator_le _ hA := borelLeviSet_center_commutator_le h hfac hJ hA
  atom A hA hAP := borelLeviSet_atom h A hA hAP
  factor _ hA := borelLeviSet_factor h hfac hJ hA

end CFSG.GroupTheory
