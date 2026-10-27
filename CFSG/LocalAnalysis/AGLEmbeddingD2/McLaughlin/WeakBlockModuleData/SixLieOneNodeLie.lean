module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOneNode

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.AGLEmbeddingD2.McLaughlin.Lie

section Radicals

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem borel_le_sup_radicals_of_torus_le (I : Set (Fin D.rank)) (Λ : Subgroup K)
    (hH : ∀ k, H k ≤ Λ)
    (hroots : ∀ γ ∈ D.roots, 0 < ht γ → (∀ j ∉ I, γ j = 0) → D.rootGroup γ ≤ Λ) :
    borel D H ≤ Λ ⊔ ⨆ j ∈ Iᶜ, radical D j := by
  refine sup_le ?_ ?_
  · exact iSup_le fun k => (hH k).trans le_sup_left
  · refine iSup₂_le fun γ hγ => ?_
    by_cases h : ∃ j ∉ I, γ j ≠ 0
    · obtain ⟨j, hj, hγj⟩ := h
      have hpos : 0 < γ j :=
        lt_of_le_of_ne (coord_nonneg_of_ht_pos hγ.1 hγ.2 j) (Ne.symm hγj)
      exact (rootGroup_le_radical hγ.1 hpos).trans (le_sup_of_le_right
        (le_iSup₂_of_le (f := fun j (_ : j ∈ Iᶜ) => radical D j) j hj le_rfl))
    · push Not at h
      exact (hroots γ hγ.1 hγ.2 h).trans le_sup_left

end Radicals

section Main

variable {K Y : Type} [Group K] [Group Y] [Finite K] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem card_inf_threePrimeSub_of_oneNode {exc : Fin D.rank → Fin D.rank → Prop}
    (h : BorelQuotient D n H π M) (hL : TwoLevi D exc)
    (hexc : ∀ i j, exc i j → ∃ V : Subgroup K,
      V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧
        ∃ v ∈ V, v ^ 3 = 1 ∧ v ∉ Subgroup.center K)
    (h3 : ∀ i, HasOrderThree D i)
    (hnode : ∀ i, ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i ∨
      Nat.card (rankOne D.rootGroup i) ∣ 6)
    (hone : ∀ i j, i ≠ j → D.cartan i j = 0 →
      ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i ∨
        ⁅rankOne D.rootGroup j, rankOne D.rootGroup j⁆ = rankOne D.rootGroup j)
    (hT0 : Nat.card (⨆ k, H k : Subgroup K) ∣ 3)
    (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {E : Subgroup Y} (hEJ : E ≤ J) (hE : Nat.card E = 9) :
    Nat.card (E ⊓ threePrimeSub J : Subgroup Y) = 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (borel D H).map π' ≤ J := hNπ ▸ hNJ
  have hBA : borel D H ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hroot : ∀ i : Fin D.rank, (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hroot' : ∀ i : Fin D.rank, (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ (hroot i)
  have hno : ∀ V : Subgroup K, V ≤ J.comap π' → ⁅V, V⁆ = V → ∀ v ∈ V, v ^ 3 = 1 →
      v ∉ Subgroup.center K → False := by
    intro V hVJ hV v hv hv3 hvc
    have hord : orderOf (π' v) = 3 :=
      orderOf_eq_prime (by rw [← map_pow, hv3, map_one]) fun h1 => hvc (hQ.ker_central v h1)
    have hdvd : 3 ∣ Nat.card (V.map π') := by
      have := Subgroup.orderOf_dvd_natCard (V.map π') ⟨v, hv, rfl⟩
      rwa [hord] at this
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (hperf _ (Subgroup.map_le_iff_le_comap.2 hVJ) (by rw [← Subgroup.map_commutator, hV])) hdvd
  set I : Finset (Fin D.rank) := Finset.univ.filter fun i => i ∈ negIndices D (J.comap π')
    with hI
  have hmemI : ∀ i, i ∈ I ↔ i ∈ negIndices D (J.comap π') := fun i => by simp [hI]
  have hLJ : ∀ i ∈ I, rankOne D.rootGroup i ≤ J.comap π' := fun i hi =>
    rankOne_le_of_mem_negIndices hBA ((hmemI i).1 hi)
  choose x hx y hy hxy3 c hc using h3
  have hxyL : ∀ i, x i * y i ∈ rankOne D.rootGroup i := fun i =>
    mul_mem (Subgroup.mem_sup_left (hx i)) (Subgroup.mem_sup_right (hy i))
  have hxyc : ∀ i, x i * y i ∉ Subgroup.center K := fun i hcen =>
    hc i (Subgroup.mem_center_iff.1 hcen (c i)).symm
  have hnp : ∀ i ∈ I, ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ ≠ rankOne D.rootGroup i :=
    fun i hi hp => hno _ (hLJ i hi) hp _ (hxyL i) (hxy3 i) (hxyc i)
  have hcard2 : ∀ i ∈ I, ∀ γ : Fin D.rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      Nat.card (D.rootGroup γ) = 2 := by
    intro i hi γ hγ
    have hγr : γ ∈ D.roots := by rcases hγ with rfl | rfl <;> simp [hroot, hroot']
    have hle : D.rootGroup γ ≤ rankOne D.rootGroup i := by
      rcases hγ with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    obtain ⟨k, hk⟩ := (h.pGroup γ hγr).exists_card_eq
    have hd : 2 ^ k ∣ 6 := hk ▸ (Subgroup.card_dvd_of_le hle).trans
      ((hnode i).resolve_left (hnp i hi))
    have hk0 : k ≠ 0 := fun h0 => h.extras.ne_bot γ hγr
      (Subgroup.eq_bot_of_card_eq _ (by rw [hk, h0, pow_zero]))
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have := (pow_dvd_pow 2 (show 2 ≤ k by omega)).trans hd
      norm_num at this
    rw [hk, show k = 1 by omega, pow_one]
  have hsq : ∀ i ∈ I, ∀ γ : Fin D.rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      ∀ z ∈ D.rootGroup γ, z ^ 2 = 1 := fun i hi γ hγ z hz => by
    have := Subgroup.orderOf_dvd_natCard _ hz
    rw [hcard2 i hi γ hγ] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  have hx1 : ∀ i ∈ I, x i ≠ 1 := fun i hi h1 => by
    have hy3 : y i ^ 3 = 1 := by simpa [h1] using hxy3 i
    have := eq_one_of_sq_eq_one_of_cube_eq_one (hsq i hi _ (Or.inr rfl) _ (hy i)) hy3
    exact hxyc i (by rw [h1, this, one_mul]; exact one_mem _)
  have hy1 : ∀ i ∈ I, y i ≠ 1 := fun i hi h1 => by
    have hx3 : x i ^ 3 = 1 := by simpa [h1] using hxy3 i
    have := eq_one_of_sq_eq_one_of_cube_eq_one (hsq i hi _ (Or.inl rfl) _ (hx i)) hx3
    exact hxyc i (by rw [h1, this, one_mul]; exact one_mem _)
  have hcart : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → D.cartan i j = 0 := by
    intro i hi j hj hij
    by_contra hA
    have hLij := sup_le (hLJ i hi) (hLJ j hj)
    rcases hL.pair i j hij hA (hnp i hi) (hnp j hj) with hp | he
    · exact hno _ hLij hp _ (Subgroup.mem_sup_left (hxyL i)) (hxy3 i) (hxyc i)
    · obtain ⟨V, hV, hVp, v, hv, hv3, hvc⟩ := hexc i j he
      exact hno V (hV.trans hLij) hVp v hv hv3 hvc
  have hAne : J.comap π' ≠ borel D H := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i₀, hi₀⟩ := negIndices_nonempty_of_ne hQ.ct hQ.extras hBA hAne
  have hi₀I : i₀ ∈ I := (hmemI i₀).2 hi₀
  have hone' : ∀ j ∈ I, j = i₀ := by
    intro j hj
    by_contra hne
    rcases hone j i₀ hne (hcart j hj i₀ hi₀I hne) with hp | hp
    · exact hnp j hj hp
    · exact hnp i₀ hi₀I hp
  have hIi : ∀ j, j ∈ negIndices D (J.comap π') ↔ j = i₀ := fun j =>
    ⟨fun hj => hone' j ((hmemI j).2 hj), fun e => e ▸ hi₀⟩
  set i := i₀ with hi
  set L := rankOne D.rootGroup i with hL
  set T₀ : Subgroup K := ⨆ k, H k with hT₀
  set Rr : Subgroup K := ⨆ j ∈ ({i} : Set (Fin D.rank))ᶜ, radical D j with hRr
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  have hRr2 : IsPGroup 2 Rr := sup_radicals_isPGroup hU2 {i}
  have hRrB : Rr ≤ borel D H :=
    iSup₂_le fun j _ => (radical_le_posUnipotent j).trans posUnipotent_le_borel
  have hJeq : J = (borel D H).map π' ⊔ L.map π' := by
    rw [eq_map_borel_sup_of_le hQ.ct hQ.extras hπ' hBJ]
    congr 1
    have : negIndices D (J.comap π') = {i} :=
      Set.ext fun j => (hIi j).trans Set.mem_singleton_iff.symm
    rw [this]
    simp
    rfl
  have hBsup : borel D H ≤ (T₀ ⊔ L) ⊔ Rr :=
    borel_le_sup_radicals_of_torus_le ({i} : Set (Fin D.rank)) (T₀ ⊔ L)
      (fun k => (le_iSup H k).trans le_sup_left)
      (fun γ hγ _ hh => (hQ.ct.le_rankOne i γ hγ fun k hk => hh k hk).trans le_sup_right)
  have hBN : borel D H ≤ Subgroup.normalizer (Rr : Set K) :=
    le_normalizer_sup_radicals ({i} : Set (Fin D.rank)) fun j _ =>
      borel_le_normalizer_radical hQ.ct hQ.extras j
  have hLN : L ≤ Subgroup.normalizer (Rr : Set K) :=
    le_normalizer_sup_radicals ({i} : Set (Fin D.rank)) fun j hj =>
      rankOne_le_normalizer_radical hQ.extras fun e => hj e.symm
  have hRJ : Rr.map π' ≤ J := (Subgroup.map_mono hRrB).trans hBJ
  have hJR : J ≤ Subgroup.normalizer ((Rr.map π' : Subgroup Y) : Set Y) := by
    rw [hJeq]
    exact sup_le ((Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map π'))
      ((Subgroup.map_mono hLN).trans (Subgroup.le_normalizer_map π'))
  have hxJ : π' (x i) ∈ J :=
    Subgroup.mem_comap.mp (hLJ i hi₀I (Subgroup.mem_sup_left (hx i)))
  have hyJ : π' (y i) ∈ J :=
    Subgroup.mem_comap.mp (hLJ i hi₀I (Subgroup.mem_sup_right (hy i)))
  have hTJ : T₀.map π' ≤ J := (Subgroup.map_mono iSup_le_borel).trans hBJ
  have hconj : ∀ γ : Fin D.rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      ∀ t ∈ T₀, ∀ z ∈ D.rootGroup γ, t * z * t⁻¹ = z := by
    intro γ hγ t ht z hz
    have hγr : γ ∈ D.roots := by rcases hγ with rfl | rfl <;> simp [hroot, hroot']
    exact conj_eq_self_of_card_two (hcard2 i hi₀I γ hγ)
      (fun w hw => (Subgroup.mem_normalizer_iff.1
        (torus_le_normalizer_rootGroup hQ.ct hγr ht) w).1 hw) hz
  have hTx : ∀ t ∈ T₀.map π', t * π' (x i) = π' (x i) * t := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    have := mul_inv_eq_iff_eq_mul.1 (hconj _ (Or.inl rfl) t₀ ht₀ _ (hx i))
    rw [← map_mul, ← map_mul, this]
  have hTy : ∀ t ∈ T₀.map π', t * π' (y i) = π' (y i) * t := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    have := mul_inv_eq_iff_eq_mul.1 (hconj _ (Or.inr rfl) t₀ ht₀ _ (hy i))
    rw [← map_mul, ← map_mul, this]
  have hTc : Nat.card (T₀.map π') ∣ 3 := by
    have : T₀.map π' = (π'.comp T₀.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [this]
    exact (Subgroup.card_range_dvd _).trans hT0
  have hLcl : L.map π' ≤ Subgroup.closure {π' (x i), π' (y i)} := by
    rw [hL, rankOne, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      rcases eq_one_or_eq_of_mem_of_card_two (hcard2 i hi₀I _ (Or.inl rfl)) (hx i) hz
        (hx1 i hi₀I) with rfl | rfl
      · rw [map_one]; exact one_mem _
      · exact Subgroup.subset_closure (Or.inl rfl)
    · rintro _ ⟨z, hz, rfl⟩
      rcases eq_one_or_eq_of_mem_of_card_two (hcard2 i hi₀I _ (Or.inr rfl)) (hy i) hz
        (hy1 i hi₀I) with rfl | rfl
      · rw [map_one]; exact one_mem _
      · exact Subgroup.subset_closure (Or.inr rfl)
  have hJle : J ≤ Rr.map π' ⊔ (T₀.map π' ⊔ Subgroup.closure {π' (x i), π' (y i)}) := by
    rw [hJeq]
    refine sup_le ?_ (hLcl.trans (le_sup_of_le_right le_sup_right))
    calc (borel D H).map π' ≤ ((T₀ ⊔ L) ⊔ Rr).map π' := Subgroup.map_mono hBsup
      _ = (T₀.map π' ⊔ L.map π') ⊔ Rr.map π' := by
          rw [Subgroup.map_sup, Subgroup.map_sup]
      _ ≤ _ := by
          refine sup_le (sup_le (le_sup_of_le_right le_sup_left)
            (hLcl.trans (le_sup_of_le_right le_sup_right))) le_sup_left
  have hx2 : π' (x i) ^ 2 = 1 := by
    rw [← map_pow, hsq i hi₀I _ (Or.inl rfl) _ (hx i), map_one]
  have hy2 : π' (y i) ^ 2 = 1 := by
    rw [← map_pow, hsq i hi₀I _ (Or.inr rfl) _ (hy i), map_one]
  have hxy3' : (π' (x i) * π' (y i)) ^ 3 = 1 := by
    rw [← map_mul, ← map_pow, hxy3 i, map_one]
  have hxy1' : π' (x i) * π' (y i) ≠ 1 := fun h1 =>
    hxyc i (hQ.ker_central _ (by rw [MonoidHom.mem_ker, map_mul]; exact h1))
  exact card_inf_threePrimeSub_eq_three hRJ hJR (hRr2.map π') hxJ hyJ hTJ hJle hTx hTy hTc hx2
    hy2 hxy3' hxy1' hEJ hE

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
