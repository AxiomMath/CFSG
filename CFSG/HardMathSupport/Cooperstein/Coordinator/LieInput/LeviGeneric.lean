module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.LeviAssembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUModel

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.AGLEmbeddingD2.ParabLevi CFSG.Open CFSG.AGLEmbedding

section Generic

variable {K Y : Type} [Group K] [Group Y]

theorem leviM_mono_gen {D : UniversalRootDatum K} {J J' : Set (Fin D.rank)} (h : J ⊆ J') :
    leviM D J ≤ leviM D J' :=
  iSup₂_le fun i hi => rankOne_le_leviM (h hi)

theorem leviM_le_centralizer_of_rankOne {D : UniversalRootDatum K} {J J' : Set (Fin D.rank)}
    (h : ∀ i ∈ J, ∀ j ∈ J', rankOne D.rootGroup i ≤
      Subgroup.centralizer (rankOne D.rootGroup j : Set K)) :
    leviM D J ≤ Subgroup.centralizer ((leviM D J' : Subgroup K) : Set K) := by
  refine iSup₂_le fun i hi x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have : leviM D J' ≤ Subgroup.centralizer ({x} : Set K) := by
    refine iSup₂_le fun j hj y hy => ?_
    have hc := h i hi j hj hx
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (hc y hy).symm
  have h2 := this hy
  rw [Subgroup.mem_centralizer_iff] at h2
  exact (h2 x rfl).symm

theorem decomp_of_chev (π : K →* Y)
    (hker : ∀ z ∈ π.ker, z ∈ Subgroup.center K)
    (A G : Subgroup K) (hA : A ≤ Subgroup.normalizer (G : Set K)) {M : Type} [Group M]
    (e : M ≃* ↥G) (h : CFSG.IsQuasisimple M ∧ IsClassicalTwoOrG2 (M ⧸ Subgroup.center M)) :
    ∃ E C : Subgroup K, E ≤ G ∧ C ≤ G ∧ G ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧
      E ≤ Subgroup.normalizer (C : Set K) ∧ A ≤ Subgroup.normalizer (E : Set K) ∧
      A ≤ Subgroup.normalizer (C : Set K) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π))) :=
  decomp_ns π A G hA (chev_map_of_central_kernel π hker e h)

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem leviOb_of_node_family
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (π : K →* Y) (I : Set (Fin D.rank))
    {β : Type} [Fintype β] (J : β → Set (Fin D.rank))
    (hJI : ∀ b, J b ⊆ I) (hcov : ∀ i ∈ I, ∃ b, i ∈ J b)
    (hcomm : ∀ b b', b ≠ b' → ∀ i ∈ J b, ∀ j ∈ J b',
      rankOne D.rootGroup i ≤ Subgroup.centralizer (rankOne D.rootGroup j : Set K))
    (hdec : ∀ b, ∃ E C : Subgroup K, E ≤ leviM D (J b) ∧ C ≤ leviM D (J b) ∧
      leviM D (J b) ≤ E ⊔ C ∧ Group.IsSolvable ↥E ∧ E ≤ Subgroup.normalizer (C : Set K) ∧
      (⨆ k, H k) ≤ Subgroup.normalizer (E : Set K) ∧
      (⨆ k, H k) ≤ Subgroup.normalizer (C : Set K) ∧
      (C ≠ ⊥ → CFSG.IsQuasisimple ↥(C.map π) ∧
        IsClassicalTwoOrG2 (↥(C.map π) ⧸ Subgroup.center ↥(C.map π)))) :
    LeviOb D H π I := by
  choose E C hEG hCG hGEC hEs hEC hTE hTC hCq using hdec
  refine leviOb_of_blocks D H π I (fun b => leviM D (J b)) C E
    (Group.isSolvable_of_comm fun a b => (isMulCommutative_torus hext).is_comm.comm a b) ?_ ?_
    hEG hCG hGEC ?_ hEs hEC hTE hTC hCq
  · intro b
    exact leviM_mono_gen (hJI b)
  · refine iSup₂_le fun i hi => ?_
    obtain ⟨b, hb⟩ := hcov i hi
    exact (rankOne_le_leviM hb).trans (le_iSup (fun b => leviM D (J b)) b)
  · intro b b' hbb'
    exact leviM_le_centralizer_of_rankOne (hcomm b b' hbb')

end Generic

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
