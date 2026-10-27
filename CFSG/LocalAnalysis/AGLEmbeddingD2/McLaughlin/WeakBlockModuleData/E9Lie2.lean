module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Lie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Struct
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOneNodeLie

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.AGLEmbeddingD2.McLaughlin.Lie

section Decomp

variable {K Y : Type} [Group K] [Group Y] [Finite K] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem exists_radical_decomp (h : BorelQuotient D n H π M) {J : Subgroup Y}
    (hBJ : (borel D H).map π ≤ J) (N : Set (Fin D.rank))
    (hJeq : J = (borel D H).map π ⊔ ⨆ i ∈ N, (rankOne D.rootGroup i).map π)
    (hroots : ∀ γ ∈ D.roots, 0 < ht γ → (∀ j ∉ N, γ j = 0) →
      D.rootGroup γ ≤ ⨆ i ∈ N, rankOne D.rootGroup i) :
    ∃ R : Subgroup Y, R ≤ J ∧ J ≤ Subgroup.normalizer (R : Set Y) ∧ IsPGroup 2 R ∧
      J ≤ R ⊔ ((⨆ k, H k).map π ⊔ ⨆ i ∈ N, (rankOne D.rootGroup i).map π) := by
  set Rr : Subgroup K := ⨆ j ∈ Nᶜ, radical D j with hRr
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  have hRr2 : IsPGroup 2 Rr := sup_radicals_isPGroup hU2 N
  have hRrB : Rr ≤ borel D H :=
    iSup₂_le fun j _ => (radical_le_posUnipotent j).trans posUnipotent_le_borel
  have hBN : borel D H ≤ Subgroup.normalizer (Rr : Set K) :=
    le_normalizer_sup_radicals N fun j _ => borel_le_normalizer_radical h.ct h.extras j
  have hLN : ∀ i ∈ N, rankOne D.rootGroup i ≤ Subgroup.normalizer (Rr : Set K) := fun i hi =>
    le_normalizer_sup_radicals N fun j hj =>
      rankOne_le_normalizer_radical h.extras fun e => hj (e ▸ hi)
  refine ⟨Rr.map π, (Subgroup.map_mono hRrB).trans hBJ, ?_, hRr2.map π, ?_⟩
  · rw [hJeq]
    refine sup_le ((Subgroup.map_mono hBN).trans (Subgroup.le_normalizer_map π))
      (iSup₂_le fun i hi => (Subgroup.map_mono (hLN i hi)).trans (Subgroup.le_normalizer_map π))
  · have hBsup : borel D H ≤ ((⨆ k, H k) ⊔ ⨆ i ∈ N, rankOne D.rootGroup i) ⊔ Rr :=
      borel_le_sup_radicals_of_torus_le N _ (fun k => (le_iSup H k).trans le_sup_left)
        (fun γ hγ hpos hsupp => (hroots γ hγ hpos hsupp).trans le_sup_right)
    rw [hJeq]
    refine sup_le ?_ ?_
    · calc (borel D H).map π
          ≤ (((⨆ k, H k) ⊔ ⨆ i ∈ N, rankOne D.rootGroup i) ⊔ Rr).map π := Subgroup.map_mono hBsup
        _ = ((⨆ k, H k).map π ⊔ ⨆ i ∈ N, (rankOne D.rootGroup i).map π) ⊔ Rr.map π := by
            simp only [Subgroup.map_sup, Subgroup.map_iSup]
        _ ≤ _ := le_of_eq (sup_comm _ _)
    · exact (le_sup_right : (⨆ i ∈ N, (rankOne D.rootGroup i).map π) ≤
        (⨆ k, H k).map π ⊔ ⨆ i ∈ N, (rankOne D.rootGroup i).map π).trans le_sup_right

theorem exists_separated_pair_of_threePerfect {exc : Fin D.rank → Fin D.rank → Prop}
    (h : BorelQuotient D n H π M) (hM : M ∣ 3) (hL : TwoLevi D exc)
    (hexc : ∀ i j, exc i j → ∃ V : Subgroup K,
      V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧
        ∃ v ∈ V, v ^ 3 = 1 ∧ v ∉ Subgroup.center K)
    (h3 : ∀ i, HasOrderThree D i)
    (hnode : ∀ i, ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i ∨
      Nat.card (rankOne D.rootGroup i) ∣ 6)
    (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U))
    {E : Subgroup Y} (hEJ : E ≤ J) (hE9 : Nat.card E = 9) (hsyl : ¬ 3 ∣ (E.subgroupOf J).index) :
    ∃ e₁ e₂ : ↥J, (e₁ : Y) ∈ E ∧ (e₂ : Y) ∈ E ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧
      ∀ φ : ↥J ≃* ↥J, φ e₁ ≠ e₂ := by
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
  set N : Set (Fin D.rank) := negIndices D (J.comap π') with hN
  have hJeq : J = (borel D H).map π' ⊔ ⨆ i ∈ N, (rankOne D.rootGroup i).map π' :=
    eq_map_borel_sup_of_le hQ.ct hQ.extras hπ' hBJ
  have hNI : ∀ j, j ∈ N ↔ j ∈ I := fun j => (hmemI j).symm
  have hIne : I.Nonempty := ⟨i₀, hi₀I⟩
  have hxL : ∀ i, x i ∈ rankOne D.rootGroup i := fun i => Subgroup.mem_sup_left (hx i)
  have hyL : ∀ i, y i ∈ rankOne D.rootGroup i := fun i => Subgroup.mem_sup_right (hy i)
  have hXJ : ∀ i ∈ I, π' (x i) ∈ J := fun i hi => Subgroup.mem_comap.mp (hLJ i hi (hxL i))
  have hYJ : ∀ i ∈ I, π' (y i) ∈ J := fun i hi => Subgroup.mem_comap.mp (hLJ i hi (hyL i))
  have hX2 : ∀ i ∈ I, π' (x i) * π' (x i) = 1 := fun i hi => by
    rw [← map_mul, ← sq, hsq i hi _ (Or.inl rfl) _ (hx i), map_one]
  have hY2 : ∀ i ∈ I, π' (y i) * π' (y i) = 1 := fun i hi => by
    rw [← map_mul, ← sq, hsq i hi _ (Or.inr rfl) _ (hy i), map_one]
  have hXY3 : ∀ i, (π' (x i) * π' (y i)) ^ 3 = 1 := fun i => by
    rw [← map_mul, ← map_pow, hxy3 i, map_one]
  have hXY1 : ∀ i, π' (x i) * π' (y i) ≠ 1 := fun i h1 =>
    hxyc i (hQ.ker_central _ (by rw [MonoidHom.mem_ker, map_mul]; exact h1))
  have hcomm : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ a ∈ rankOne D.rootGroup i,
      ∀ b ∈ rankOne D.rootGroup j, π' a * π' b = π' b * π' a := fun i hi j hj hij a ha b hb => by
    have := commutes_rankOne_of_cartan_eq_zero hQ.extras hij (hcart i hi j hj hij) a ha b hb
    rw [← map_mul, ← map_mul, this]
  have hcommXY : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      π' (x i) * π' (x j) = π' (x j) * π' (x i) ∧ π' (x i) * π' (y j) = π' (y j) * π' (x i) ∧
      π' (y i) * π' (x j) = π' (x j) * π' (y i) ∧ π' (y i) * π' (y j) = π' (y j) * π' (y i) :=
    fun i hi j hj hij =>
      ⟨hcomm i hi j hj hij _ (hxL i) _ (hxL j), hcomm i hi j hj hij _ (hxL i) _ (hyL j),
        hcomm i hi j hj hij _ (hyL i) _ (hxL j), hcomm i hi j hj hij _ (hyL i) _ (hyL j)⟩
  have hcommC : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      (π' (x i) * π' (y i)) * (π' (x j) * π' (y j)) =
        (π' (x j) * π' (y j)) * (π' (x i) * π' (y i)) := fun i hi j hj hij => by
    have := hcomm i hi j hj hij (x i * y i) (hxyL i) (x j * y j) (hxyL j)
    simpa only [map_mul] using this
  have hcommXC : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      π' (x i) * (π' (x j) * π' (y j)) = (π' (x j) * π' (y j)) * π' (x i) := fun i hi j hj hij => by
    have := hcomm i hi j hj hij (x i) (hxL i) (x j * y j) (hxyL j)
    simpa only [map_mul] using this
  have hinvC : ∀ i ∈ I, π' (x i) * (π' (x i) * π' (y i)) * (π' (x i))⁻¹ =
      (π' (x i) * π' (y i))⁻¹ := fun i hi => conj_c_eq_inv (hX2 i hi) (hY2 i hi)
  set T₀ : Subgroup K := ⨆ k, H k with hT₀
  have hconj : ∀ i ∈ I, ∀ γ : Fin D.rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      ∀ t ∈ T₀, ∀ z ∈ D.rootGroup γ, t * z * t⁻¹ = z := by
    intro i hi γ hγ t ht z hz
    have hγr : γ ∈ D.roots := by rcases hγ with rfl | rfl <;> simp [hroot, hroot']
    exact conj_eq_self_of_card_two (hcard2 i hi γ hγ)
      (fun w hw => (Subgroup.mem_normalizer_iff.1
        (torus_le_normalizer_rootGroup hQ.ct hγr ht) w).1 hw) hz
  have hTx : ∀ i ∈ I, ∀ t ∈ T₀.map π', t * π' (x i) = π' (x i) * t := by
    rintro i hi _ ⟨t₀, ht₀, rfl⟩
    have := mul_inv_eq_iff_eq_mul.1 (hconj i hi _ (Or.inl rfl) t₀ ht₀ _ (hx i))
    rw [← map_mul, ← map_mul, this]
  have hTy : ∀ i ∈ I, ∀ t ∈ T₀.map π', t * π' (y i) = π' (y i) * t := by
    rintro i hi _ ⟨t₀, ht₀, rfl⟩
    have := mul_inv_eq_iff_eq_mul.1 (hconj i hi _ (Or.inr rfl) t₀ ht₀ _ (hy i))
    rw [← map_mul, ← map_mul, this]
  have hT03 : ∀ t₀ ∈ T₀, t₀ ^ 3 = 1 := fun t₀ ht₀ => by
    obtain ⟨k, hk⟩ := hM
    rw [hk, pow_mul, hQ.pow_eq_one_of_mem_iSup ht₀, one_pow]
  have hT3 : ∀ t ∈ T₀.map π', t ^ 3 = 1 := by
    rintro _ ⟨t₀, ht₀, rfl⟩
    rw [← map_pow, hT03 t₀ ht₀, map_one]
  have hTJ : T₀.map π' ≤ J := (Subgroup.map_mono iSup_le_borel).trans hBJ
  have hLcl : ∀ i ∈ I, (rankOne D.rootGroup i).map π' ≤
      Subgroup.closure {π' (x i), π' (y i)} := by
    intro i hi
    rw [rankOne, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      rcases eq_one_or_eq_of_mem_of_card_two (hcard2 i hi _ (Or.inl rfl)) (hx i) hz
        (hx1 i hi) with rfl | rfl
      · rw [map_one]; exact one_mem _
      · exact Subgroup.subset_closure (Or.inl rfl)
    · rintro _ ⟨z, hz, rfl⟩
      rcases eq_one_or_eq_of_mem_of_card_two (hcard2 i hi _ (Or.inr rfl)) (hy i) hz
        (hy1 i hi) with rfl | rfl
      · rw [map_one]; exact one_mem _
      · exact Subgroup.subset_closure (Or.inr rfl)
  have hbound : ∀ V : Subgroup Y, V ≤ J → IsPGroup 3 V → Nat.card V ≤ 9 := fun V hVJ hV3 => by
    obtain ⟨g, -, hg⟩ := exists_conj_into hEJ hE9 hsyl hVJ hV3
    rw [← hE9]; exact card_le_of_conj_into hg
  have hk2 : I.card ≤ 2 := by
    by_contra hk3
    push Not at hk3
    obtain ⟨i₁, hi₁, i₂, hi₂, i₃, hi₃, h12, h13, h23⟩ := Finset.two_lt_card.1 hk3
    obtain ⟨V, hV3, hV27, hV⟩ := exists_pGroup_card_27
      (a := π' (x i₁) * π' (y i₁)) (b := π' (x i₂) * π' (y i₂)) (c := π' (x i₃) * π' (y i₃))
      (zb := π' (x i₂)) (zc := π' (x i₃)) (hcommC i₁ hi₁ i₂ hi₂ h12) (hcommC i₁ hi₁ i₃ hi₃ h13)
      (hcommC i₂ hi₂ i₃ hi₃ h23) (hXY3 i₁) (hXY3 i₂) (hXY3 i₃) (hXY1 i₁) (hXY1 i₂) (hXY1 i₃)
      (hinvC i₂ hi₂) (hcommXC i₂ hi₂ i₁ hi₁ (Ne.symm h12)) (hinvC i₃ hi₃)
      (hcommXC i₃ hi₃ i₁ hi₁ (Ne.symm h13)) (hcommXC i₃ hi₃ i₂ hi₂ (Ne.symm h23))
    have hcJ : ∀ i ∈ I, π' (x i) * π' (y i) ∈ J := fun i hi => J.mul_mem (hXJ i hi) (hYJ i hi)
    have hVJ : V ≤ J := by
      rw [hV]
      exact sup_le (sup_le ((Subgroup.zpowers_le).2 (hcJ i₁ hi₁))
        ((Subgroup.zpowers_le).2 (hcJ i₂ hi₂))) ((Subgroup.zpowers_le).2 (hcJ i₃ hi₃))
    have := hbound V hVJ hV3
    omega
  have hkpos : 0 < I.card := Finset.card_pos.2 hIne
  have hcard9J : 9 ∣ Nat.card J := hE9 ▸ Subgroup.card_dvd_of_le hEJ
  have hk12 : I.card = 1 ∨ I.card = 2 := by omega
  rcases hk12 with hk1 | hk2'
  ·
    obtain ⟨i, hI⟩ := Finset.card_eq_one.1 hk1
    have hiI : i ∈ I := hI ▸ Finset.mem_singleton_self i
    have hN1 : N = {i} := Set.ext fun j => (hNI j).trans (by rw [hI]; simp)
    have hroots : ∀ γ ∈ D.roots, 0 < ht γ → (∀ j ∉ N, γ j = 0) →
        D.rootGroup γ ≤ ⨆ i' ∈ N, rankOne D.rootGroup i' := by
      intro γ hγ _ hs
      rw [hN1, iSup_singleton]
      exact hQ.ct.le_rankOne i γ hγ fun k hk => hs k (by rw [hN1, Set.mem_singleton_iff]; exact hk)
    obtain ⟨R, hRJ, hJR, hR2, hJle⟩ := exists_radical_decomp hQ hBJ N hJeq hroots
    rw [hN1, iSup_singleton] at hJle
    have hJle' : J ≤ R ⊔ (T₀.map π' ⊔ Subgroup.closure {π' (x i), π' (y i)}) :=
      hJle.trans (sup_le_sup_left (sup_le_sup_left (hLcl i hiI) _) _)
    have ht : ∃ t ∈ T₀.map π', t ≠ 1 := by
      by_contra hno'
      push Not at hno'
      have hT1 : T₀.map π' = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hno'
      rw [hT1, bot_sup_eq] at hJle'
      exact not_nine_dvd_card_of_le_sup hRJ hJR hR2 (hXJ i hiI) (hYJ i hiI) hJle' (hX2 i hiI)
        (hY2 i hiI) (hXY3 i) (hXY1 i) hcard9J
    exact separated_pair_one hRJ hJR hR2 hTJ (hXJ i hiI) (hYJ i hiI) hJle' (hTx i hiI) (hTy i hiI)
      hT3 (hX2 i hiI) (hY2 i hiI) (hXY3 i) (hXY1 i) ht hEJ hE9 hsyl
  ·
    obtain ⟨i, j, hij, hI⟩ := Finset.card_eq_two.1 hk2'
    have hiI : i ∈ I := hI ▸ Finset.mem_insert_self i {j}
    have hjI : j ∈ I := hI ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
    have hN2 : N = {i, j} := Set.ext fun k => (hNI k).trans (by rw [hI]; simp)
    have hroots : ∀ γ ∈ D.roots, 0 < ht γ → (∀ k ∉ N, γ k = 0) →
        D.rootGroup γ ≤ ⨆ i' ∈ N, rankOne D.rootGroup i' := by
      intro γ hγ hpos hs
      rw [hN2, iSup_insert, iSup_singleton]
      exact rootGroup_le_sup_rankOne_of_orth hQ.ct (hcart i hiI j hjI hij) hγ hpos
        (fun k hki hkj => hs k (by rw [hN2]; simp [hki, hkj]))
    obtain ⟨R, hRJ, hJR, hR2, hJle⟩ := exists_radical_decomp hQ hBJ N hJeq hroots
    rw [hN2, iSup_insert, iSup_singleton] at hJle
    have hct : ∀ k ∈ I, ∀ t ∈ T₀.map π', t * (π' (x k) * π' (y k)) = (π' (x k) * π' (y k)) * t :=
      fun k hk t ht => by
        calc t * (π' (x k) * π' (y k)) = (t * π' (x k)) * π' (y k) := by group
          _ = (π' (x k) * t) * π' (y k) := by rw [hTx k hk t ht]
          _ = π' (x k) * (t * π' (y k)) := by group
          _ = π' (x k) * (π' (y k) * t) := by rw [hTy k hk t ht]
          _ = (π' (x k) * π' (y k)) * t := by group
    have hT1 : T₀.map π' = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro t ht
      by_contra ht1
      obtain ⟨V, hV3, hV27, hV⟩ := exists_pGroup_card_27
        (a := t) (b := π' (x i) * π' (y i)) (c := π' (x j) * π' (y j))
        (zb := π' (x i)) (zc := π' (x j)) (hct i hiI t ht) (hct j hjI t ht)
        (hcommC i hiI j hjI hij) (hT3 t ht) (hXY3 i) (hXY3 j) ht1 (hXY1 i) (hXY1 j)
        (hinvC i hiI) (hTx i hiI t ht).symm (hinvC j hjI) (hTx j hjI t ht).symm
        (hcommXC j hjI i hiI (Ne.symm hij))
      have hcJ : ∀ k ∈ I, π' (x k) * π' (y k) ∈ J := fun k hk => J.mul_mem (hXJ k hk) (hYJ k hk)
      have hVJ : V ≤ J := by
        rw [hV]
        exact sup_le (sup_le ((Subgroup.zpowers_le).2 (hTJ ht))
          ((Subgroup.zpowers_le).2 (hcJ i hiI))) ((Subgroup.zpowers_le).2 (hcJ j hjI))
      have := hbound V hVJ hV3
      omega
    rw [hT1, bot_sup_eq] at hJle
    have hJle' : J ≤ R ⊔ (Subgroup.closure {π' (x i), π' (y i)} ⊔
        Subgroup.closure {π' (x j), π' (y j)}) :=
      hJle.trans (sup_le_sup_left (sup_le_sup (hLcl i hiI) (hLcl j hjI)) _)
    obtain ⟨h11, h12, h21, h22⟩ := hcommXY i hiI j hjI hij
    exact separated_pair_two hRJ hJR hR2 (hXJ i hiI) (hYJ i hiI) (hXJ j hjI) (hYJ j hjI) hJle'
      h11 h12 h21 h22 (hX2 i hiI) (hY2 i hiI) (hXY3 i) (hXY1 i) (hX2 j hjI) (hY2 j hjI) (hXY3 j)
      (hXY1 j) hEJ hE9 hsyl

end Decomp

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
