module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParEngine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Gen

theorem map_pElementSubgroup_le_pElementSubgroup_map {G G' : Type*} [Group G] [Group G']
    (f : G →* G') (A : Subgroup G) :
    (pElementSubgroup 2 A).map f ≤ pElementSubgroup 2 (A.map f) := by
  unfold pElementSubgroup
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, ⟨hxA, k, hk⟩, rfl⟩
  have hd : orderOf (f x) ∣ 2 ^ k := hk ▸ orderOf_map_dvd f x
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  exact Subgroup.subset_closure ⟨⟨x, hxA, rfl⟩, j, hj⟩

theorem le_pElementSubgroup_of_isPGroup {G : Type*} [Group G] {A B : Subgroup G} (hBA : B ≤ A)
    (hB : IsPGroup 2 B) : B ≤ pElementSubgroup 2 A := fun x hx =>
  Subgroup.subset_closure ⟨hBA hx, (IsPGroup.iff_orderOf.1 hB) ⟨x, hx⟩ |>.imp fun k hk => by
    rw [← hk, ← Subgroup.orderOf_coe]⟩

end Gen

section Main

variable {K : Type*} {S : Type} [Group K] [Finite K] [Group S] [Finite S] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* S} {M : ℕ}

theorem bq_ker_le_borel (h : BorelQuotient D n H π M) : π.ker ≤ borel D H :=
  fun z hz => CFSG.ClassicalInvolution.WeakCT.normalizer_posUnipotent_le_borel h.ct h.extras
    (Subgroup.center_le_normalizer (posUnipotent D : Set K) (h.ker_central z hz))

theorem comap_map_of_ker_le {A : Subgroup K} (hA : π.ker ≤ A) : (A.map π).comap π = A := by
  rw [Subgroup.comap_map_eq, sup_eq_left.2 hA]

theorem rankOne_le_pElementSubgroup (h : BorelQuotient D n H π M) {A : Subgroup K}
    {i : Fin D.rank} (hA : rankOne D.rootGroup i ≤ A) :
    rankOne D.rootGroup i ≤ pElementSubgroup 2 A := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  exact sup_le (le_pElementSubgroup_of_isPGroup (le_sup_left.trans hA) (h.pGroup _ hα))
    (le_pElementSubgroup_of_isPGroup (le_sup_right.trans hA) (h.pGroup _ hα'))

theorem posUnipotent_le_pElementSubgroup (h : BorelQuotient D n H π M) {A : Subgroup K}
    (hA : posUnipotent D ≤ A) : posUnipotent D ≤ pElementSubgroup 2 A :=
  le_pElementSubgroup_of_isPGroup hA (isPGroup_iSup_pos h.extras h.pGroup)

theorem unipJ_le_pElementSubgroup (h : BorelQuotient D n H π M) {A : Subgroup K}
    {J : Set (Fin D.rank)} (hA : unipJ D J ≤ A) : unipJ D J ≤ pElementSubgroup 2 A :=
  sup_le (posUnipotent_le_pElementSubgroup h (le_sup_left.trans hA))
    (iSup₂_le fun j hj => rankOne_le_pElementSubgroup h
      ((rankOne_le_unipJ hj).trans hA))

theorem two_mem_map_unipJ (h : BorelQuotient D n H π M) (J : Set (Fin D.rank)) {a : S}
    (ha : a ∈ (parJ D H J).map π) {k : ℕ} (hk : a ^ 2 ^ k = 1) : a ∈ (unipJ D J).map π := by
  rw [parJ_eq_sup, Subgroup.map_sup] at ha
  refine mem_of_pow_two_pow_eq_one_of_mem_sup (M := M) ?_ h.odd ?_ ha hk
  · exact (Subgroup.map_mono (torus_le_normalizer_unipJ h.ct J)).trans
      (Subgroup.le_normalizer_map π)
  · rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, CFSG.ClassicalInvolution.WeakCT.pow_eq_one_of_mem_torus h.extras h.torus_pow ht,
      map_one]

theorem ker_le_parJ (h : BorelQuotient D n H π M) (J : Set (Fin D.rank)) :
    π.ker ≤ parJ D H J := (bq_ker_le_borel h).trans (borel_le_parJ J)

theorem isMinOverBorel_map_parJ (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    IsMinOverBorel (⊤ : Subgroup S) ((posUnipotent D).map π) ((parJ D H {i}).map π) := by
  have hN := h.normalizer_map_posUnipotent
  refine ⟨le_top, ?_, ?_⟩
  · rw [top_inf_eq, hN]
    refine lt_of_le_of_ne (Subgroup.map_mono (borel_le_parJ _)) fun heq => ?_
    have := congrArg (Subgroup.comap π) heq
    rw [comap_map_of_ker_le (bq_ker_le_borel h), comap_map_of_ker_le (ker_le_parJ h _)] at this
    exact (borel_lt_parJ (J := {i}) h.ct h.extras ⟨i, rfl⟩).ne this
  · intro Q hQ1 hQ2
    rw [top_inf_eq, hN] at hQ1 ⊢
    have h1 : borel D H ≤ Q.comap π := Subgroup.map_le_iff_le_comap.1 hQ1
    have h2 : Q.comap π ≤ parJ D H {i} := by
      have := Subgroup.comap_mono (f := π) hQ2
      rwa [comap_map_of_ker_le (ker_le_parJ h _)] at this
    rcases eq_borel_or_eq_parJ_singleton h.ct h.extras h1 h2 with e | e
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective h.surj Q, e]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective h.surj Q, e]

theorem exists_eq_map_parJ (h : BorelQuotient D n H π M) {A : Subgroup S}
    (hA : IsMinOverBorel (⊤ : Subgroup S) ((posUnipotent D).map π) A) :
    ∃ i, A = (parJ D H {i}).map π := by
  have hN := h.normalizer_map_posUnipotent
  obtain ⟨-, h1, h2⟩ := hA
  rw [top_inf_eq, hN] at h1 h2
  have hBA : borel D H ≤ A.comap π := Subgroup.map_le_iff_le_comap.1 h1.le
  have hne : A.comap π ≠ borel D H := fun e => by
    have := congrArg (Subgroup.map π) e
    rw [Subgroup.map_comap_eq_self_of_surjective h.surj] at this
    exact h1.ne this.symm
  obtain ⟨k, hk⟩ := negIndices_nonempty_of_ne h.ct h.extras hBA hne
  have hLk : rankOne D.rootGroup k ≤ A.comap π := rankOne_le_of_mem_negIndices hBA hk
  have hPk : parJ D H {k} ≤ A.comap π := sup_le hBA (iSup₂_le fun j hj => by
    rw [Set.mem_singleton_iff.1 hj]; exact hLk)
  have hle : (parJ D H {k}).map π ≤ A := by
    have := Subgroup.map_mono (f := π) hPk
    rwa [Subgroup.map_comap_eq_self_of_surjective h.surj] at this
  have hlt : (borel D H).map π < (parJ D H {k}).map π := by
    refine lt_of_le_of_ne (Subgroup.map_mono (borel_le_parJ _)) fun heq => ?_
    have := congrArg (Subgroup.comap π) heq
    rw [comap_map_of_ker_le (bq_ker_le_borel h), comap_map_of_ker_le (ker_le_parJ h _)] at this
    exact (borel_lt_parJ (J := {k}) h.ct h.extras ⟨k, rfl⟩).ne this
  refine ⟨k, ?_⟩
  rcases h2 _ hlt.le hle with e | e
  · exact absurd e hlt.ne'
  · exact e.symm

theorem map_rankOne_le_pElementSubgroup (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    (rankOne D.rootGroup i).map π ≤ pElementSubgroup 2 ((parJ D H {i}).map π) :=
  (Subgroup.map_mono (rankOne_le_pElementSubgroup h (rankOne_le_parJ (J := {i}) rfl))).trans
    (map_pElementSubgroup_le_pElementSubgroup_map π _)

theorem iSup_map_parJ_le (J : Set (Fin D.rank)) :
    (⨆ j ∈ J, (parJ D H {j}).map π) ≤ (parJ D H J).map π :=
  iSup₂_le fun j hj => Subgroup.map_mono (sup_le (borel_le_parJ J) (iSup₂_le fun i hi => by
    rw [Set.mem_singleton_iff.1 hi]; exact rankOne_le_parJ hj))

theorem ov_of_borelQuotient (h : BorelQuotient D n H π M) {X : Subgroup S}
    (hTX : (posUnipotent D).map π ≤ X)
    (hX : ¬ X ≤ Subgroup.normalizer (((posUnipotent D).map π : Subgroup S) : Set S)) :
    ∃ i, pElementSubgroup 2 ((parJ D H {i}).map π) ≤ X := by
  have hN := h.normalizer_map_posUnipotent
  rw [hN] at hX
  have hU : posUnipotent D ≤ X.comap π := Subgroup.map_le_iff_le_comap.1 hTX
  have hnB : ¬ X.comap π ≤ borel D H := by
    intro hle
    apply hX
    intro x hx
    obtain ⟨y, rfl⟩ := h.surj x
    exact ⟨y, hle hx, rfl⟩
  obtain ⟨i, hi⟩ := exists_negIndex_of_not_le_borel h.ct h.extras hU hnB
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hLi : rankOne D.rootGroup i ≤ X.comap π :=
    sup_le ((rootGroup_le_posUnipotent hα (ht_single_pos i)).trans hU) hi
  have hNi : unipJ D {i} ≤ X.comap π := sup_le hU (iSup₂_le fun j hj => by
    rw [Set.mem_singleton_iff.1 hj]; exact hLi)
  refine ⟨i, ?_⟩
  unfold pElementSubgroup
  rw [Subgroup.closure_le]
  rintro a ⟨ha, k, hk⟩
  have := two_mem_map_unipJ h {i} ha (k := k) (by rw [← hk]; exact pow_orderOf_eq_one a)
  obtain ⟨y, hy, rfl⟩ := this
  exact hNi hy

theorem sub_of_borelQuotient (h : BorelQuotient D n H π M) (J : Set (Fin D.rank))
    (k : Fin D.rank) (hle : pElementSubgroup 2 ((parJ D H {k}).map π) ≤
      ⨆ j ∈ J, (parJ D H {j}).map π) : k ∈ J := by
  have h3 : rankOne D.rootGroup k ≤ ((parJ D H J).map π).comap π :=
    Subgroup.map_le_iff_le_comap.1
      ((map_rankOne_le_pElementSubgroup h k).trans (hle.trans (iSup_map_parJ_le J)))
  rw [comap_map_of_ker_le (ker_le_parJ h J)] at h3
  exact mem_of_rankOne_le_parJ h.ct h.extras h3

theorem two_of_borelQuotient (h : BorelQuotient D n H π M) (J : Set (Fin D.rank))
    (hJ : J.Nonempty) {a : S} (ha : a ∈ ⨆ j ∈ J, (parJ D H {j}).map π)
    (h2 : ∃ m : ℕ, orderOf a = 2 ^ m) :
    a ∈ ⨆ j ∈ J, pElementSubgroup 2 ((parJ D H {j}).map π) := by
  obtain ⟨m, hm⟩ := h2
  have h3 := two_mem_map_unipJ h J (iSup_map_parJ_le J ha) (k := m)
    (by rw [← hm]; exact pow_orderOf_eq_one a)
  have h4 : (unipJ D J).map π ≤ ⨆ j ∈ J, pElementSubgroup 2 ((parJ D H {j}).map π) := by
    rw [unipJ, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · obtain ⟨j0, hj0⟩ := hJ
      have : posUnipotent D ≤ pElementSubgroup 2 (parJ D H {j0}) :=
        posUnipotent_le_pElementSubgroup h (posUnipotent_le_borel.trans (borel_le_parJ _))
      exact ((Subgroup.map_mono this).trans
        (map_pElementSubgroup_le_pElementSubgroup_map π _)).trans
        (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => pElementSubgroup 2 ((parJ D H {j}).map π))
          j0 hj0 le_rfl)
    · rw [Subgroup.map_iSup]
      refine iSup_le fun j => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hj => ?_
      exact (map_rankOne_le_pElementSubgroup h j).trans
        (le_iSup₂_of_le (f := fun j (_ : j ∈ J) => pElementSubgroup 2 ((parJ D H {j}).map π))
          j hj le_rfl)
  exact h4 h3

theorem nonnorm_of_borelQuotient (h : BorelQuotient D n H π M) (i : Fin D.rank) :
    ¬ pElementSubgroup 2 ((parJ D H {i}).map π) ≤
      Subgroup.normalizer (((posUnipotent D).map π : Subgroup S) : Set S) := by
  intro hle
  rw [h.normalizer_map_posUnipotent] at hle
  have h3 : rankOne D.rootGroup i ≤ ((borel D H).map π).comap π :=
    Subgroup.map_le_iff_le_comap.1 ((map_rankOne_le_pElementSubgroup h i).trans hle)
  rw [comap_map_of_ker_le (bq_ker_le_borel h)] at h3
  exact not_rankOne_le_borel h.ct h.extras i h3

theorem parJ_map_injective (h : BorelQuotient D n H π M) :
    Function.Injective (fun i : Fin D.rank => (parJ D H {i}).map π) := by
  intro i j e
  have e' := congrArg (Subgroup.comap π) e
  simp only at e'
  rw [comap_map_of_ker_le (ker_le_parJ h _), comap_map_of_ker_le (ker_le_parJ h _)] at e'
  have : rankOne D.rootGroup j ≤ parJ D H {i} :=
    (rankOne_le_parJ (J := {j}) rfl).trans e'.symm.le
  exact (Set.mem_singleton_iff.1 (mem_of_rankOne_le_parJ h.ct h.extras this)).symm

@[expose] noncomputable def minParData_of_borelQuotient (h : BorelQuotient D n H π M) :
    MinParData (⊤ : Subgroup S) ((posUnipotent D).map π) where
  ι := Fin D.rank
  P := fun i => (parJ D H {i}).map π
  P_min := isMinOverBorel_map_parJ h
  P_all := fun A hA => by
    obtain ⟨i, hi⟩ := exists_eq_map_parJ h hA
    exact ⟨i, hi⟩
  P_inj := parJ_map_injective h
  OV := fun X hTX _ hX => ov_of_borelQuotient h hTX hX
  sub := fun J k _ hle => sub_of_borelQuotient h J k hle
  two := fun J a hJ ha h2 => two_of_borelQuotient h J hJ ha h2
  nonnorm := nonnorm_of_borelQuotient h

@[expose] noncomputable def minParData_of_borelQuotient' (h : BorelQuotient D n H π M)
    {T : Subgroup S} (hT : (posUnipotent D).map π = T) : MinParData (⊤ : Subgroup S) T where
  ι := Fin D.rank
  P := fun i => (parJ D H {i}).map π
  P_min := fun i => by subst hT; exact (minParData_of_borelQuotient h).P_min i
  P_all := fun A hA => by subst hT; exact (minParData_of_borelQuotient h).P_all A hA
  P_inj := (minParData_of_borelQuotient h).P_inj
  OV := fun X h1 h2 h3 => by subst hT; exact (minParData_of_borelQuotient h).OV X h1 h2 h3
  sub := fun J k hJ hle => (minParData_of_borelQuotient h).sub J k hJ hle
  two := fun J a hJ ha h2 => (minParData_of_borelQuotient h).two J a hJ ha h2
  nonnorm := fun i => by subst hT; exact (minParData_of_borelQuotient h).nonnorm i

end Main

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
