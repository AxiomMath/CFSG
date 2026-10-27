module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

section Levi

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem torus_le_normalizer_rootGroup [Finite K]
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : (⨆ k, H k) ≤ Subgroup.normalizer (D.rootGroup γ : Set K) :=
  iSup_le fun k h hh => Subgroup.mem_normalizer_fintype fun x hx => hct.H_conj_mem k γ hγ h hh x hx

theorem commute_of_mem_sup_tori (hext : SteinbergExtras D n H) {a b : K} (ha : a ∈ ⨆ k, H k)
    (hb : b ∈ ⨆ k, H k) : Commute a b := by
  have hS : (⋃ k, (H k : Set K)).Pairwise Commute := by
    intro a ha b hb _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hb
    exact hext.torus_commute i j a hi b hj
  rw [Subgroup.iSup_eq_closure] at ha hb
  have := (Subgroup.isMulCommutative_closure hS).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem exists_mul_of_mem_of_borel_le
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) [Finite K] {π : K →* Y} (hπ : Function.Surjective π)
    {J : Subgroup Y} (hBJ : (borel D H).map π ≤ J) {z : Y} (hz : z ∈ J) :
    ∃ g ∈ ⨆ i ∈ negIndices D (J.comap π), (rankOne D.rootGroup i).map π,
      ∃ b ∈ (borel D H).map π, z = g * b := by
  set Λ : Subgroup Y := ⨆ i ∈ negIndices D (J.comap π), (rankOne D.rootGroup i).map π with hΛ
  have hLΛ : ∀ i ∈ negIndices D (J.comap π), (rankOne D.rootGroup i).map π ≤ Λ := fun i hi =>
    le_iSup₂_of_le (f := fun i (_ : i ∈ negIndices D (J.comap π)) =>
      (rankOne D.rootGroup i).map π) i hi le_rfl
  have hswap : ∀ g ∈ Λ, ∀ b ∈ (borel D H).map π, ∃ g' ∈ Λ, ∃ b' ∈ (borel D H).map π,
      b * g = g' * b' := by
    intro g hg
    refine iSup₂_induction (C := fun g => ∀ b ∈ (borel D H).map π, ∃ g' ∈ Λ,
      ∃ b' ∈ (borel D H).map π, b * g = g' * b') hg ?_ ?_ ?_
    · rintro i hi _ ⟨l, hl, rfl⟩ _ ⟨b, hb, rfl⟩
      obtain ⟨l', hl', b', hb', e⟩ := exists_mul_rankOne_eq hct hext i hb hl
      exact ⟨π l', hLΛ i hi ⟨l', hl', rfl⟩, π b', ⟨b', hb', rfl⟩, by
        rw [← map_mul, ← map_mul, e]⟩
    · exact fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul, mul_one]⟩
    · intro y w hy hw b hb
      obtain ⟨y', hy', b₁, hb₁, e₁⟩ := hy b hb
      obtain ⟨w', hw', b₂, hb₂, e₂⟩ := hw b₁ hb₁
      exact ⟨y' * w', mul_mem hy' hw', b₂, hb₂, by
        rw [← mul_assoc, e₁, mul_assoc, e₂, mul_assoc]⟩
  let P : Subgroup Y :=
    { carrier := {z | ∃ g ∈ Λ, ∃ b ∈ (borel D H).map π, z = g * b}
      mul_mem' := by
        rintro _ _ ⟨g₁, hg₁, b₁, hb₁, rfl⟩ ⟨g₂, hg₂, b₂, hb₂, rfl⟩
        obtain ⟨g', hg', b', hb', e⟩ := hswap g₂ hg₂ b₁ hb₁
        exact ⟨g₁ * g', mul_mem hg₁ hg', b' * b₂, mul_mem hb' hb₂, by
          rw [mul_assoc, ← mul_assoc b₁, e]
          group⟩
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨g, hg, b, hb, rfl⟩
        obtain ⟨g', hg', b', hb', e⟩ := hswap g⁻¹ (inv_mem hg) b⁻¹ (inv_mem hb)
        exact ⟨g', hg', b', hb', by rw [mul_inv_rev, e]⟩ }
  have hJP : J ≤ P := by
    rw [eq_map_borel_sup_of_le hct hext hπ hBJ]
    refine sup_le (fun b hb => ⟨1, one_mem _, b, hb, by rw [one_mul]⟩) ?_
    exact iSup₂_le fun i hi x hx => ⟨x, hLΛ i hi hx, 1, one_mem _, by
      rw [mul_one]⟩
  exact hJP hz

end Levi

section Three

variable {K Y : Type*} [Group K] [Group Y] [Finite K] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem BorelQuotient.isElemAbelian_of_threePerfect {exc : Fin D.rank → Fin D.rank → Prop}
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
    (hperf : ∀ U : Subgroup Y, U ≤ J → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U)) :
    ∀ U : Subgroup Y, U ≤ J → IsPGroup 3 U → IsElemAbelian 3 U := by
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
  set T₀ : Subgroup K := ⨆ k, H k with hT₀
  have hconj : ∀ i ∈ I, ∀ γ : Fin D.rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
      ∀ t ∈ T₀, ∀ z ∈ D.rootGroup γ, t * z * t⁻¹ = z := by
    intro i hi γ hγ t ht z hz
    have hγr : γ ∈ D.roots := by rcases hγ with rfl | rfl <;> simp [hroot, hroot']
    exact conj_eq_self_of_card_two (hcard2 i hi γ hγ)
      (fun w hw => (Subgroup.mem_normalizer_iff.1
        (torus_le_normalizer_rootGroup hQ.ct hγr ht) w).1 hw) hz
  have hcx : ∀ i ∈ I, ∀ t ∈ T₀, Commute t (x i) := fun i hi t ht => by
    have := hconj i hi _ (Or.inl rfl) t ht _ (hx i)
    exact (mul_inv_eq_iff_eq_mul.1 this)
  have hcy : ∀ i ∈ I, ∀ t ∈ T₀, Commute t (y i) := fun i hi t ht => by
    have := hconj i hi _ (Or.inr rfl) t ht _ (hy i)
    exact (mul_inv_eq_iff_eq_mul.1 this)
  have hT3 : ∀ t ∈ T₀, t ^ 3 = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hM
    rw [hk, pow_mul, hQ.pow_eq_one_of_mem_iSup ht, one_pow]
  set S : Set Y := (T₀.map π' : Set Y) ∪ (fun i => π' (x i * y i)) '' (I : Set (Fin D.rank))
    with hS
  set E : Subgroup Y := Subgroup.closure S with hE
  have hcommS : S.Pairwise Commute := by
    have key : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
      have tt : ∀ a ∈ T₀.map π', ∀ b ∈ T₀.map π', Commute a b := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact (commute_of_mem_sup_tori hQ.extras ha hb).map π'
      have tc : ∀ a ∈ T₀.map π', ∀ i ∈ I, Commute a (π' (x i * y i)) := by
        rintro _ ⟨a, ha, rfl⟩ i hi
        exact (((hcx i hi a ha).mul_right (hcy i hi a ha))).map π'
      have cc : ∀ i ∈ I, ∀ j ∈ I, Commute (π' (x i * y i)) (π' (x j * y j)) := by
        intro i hi j hj
        by_cases hij : i = j
        · rw [hij]
        · exact Commute.map (commutes_rankOne_of_cartan_eq_zero hQ.extras hij
            (hcart i hi j hj hij) _ (hxyL i) _ (hxyL j)) π'
      rintro a (ha | ⟨i, hi, rfl⟩) b (hb | ⟨j, hj, rfl⟩)
      · exact tt a ha b hb
      · exact tc a ha j hj
      · exact (tc b hb i hi).symm
      · exact cc i hi j hj
    exact fun a ha b hb _ => key a ha b hb
  have h3S : ∀ s ∈ S, s ^ 3 = 1 := by
    rintro _ (⟨t, ht, rfl⟩ | ⟨i, -, rfl⟩)
    · rw [← map_pow, hT3 t ht, map_one]
    · rw [← map_pow, hxy3 i, map_one]
  have hEelem : IsElemAbelian 3 E := isElemAbelian_three_closure_of_pairwise hcommS h3S
  have hEJ : E ≤ J := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (⟨t, ht, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact hBJ ⟨t, iSup_le_borel ht, rfl⟩
    · exact hLJ i hi (hxyL i)
  set Wx : Subgroup Y := Subgroup.closure ((fun i => π' (x i)) '' (I : Set (Fin D.rank)))
    with hWx
  have hxU : ∀ i, x i ∈ posUnipotent D := fun i =>
    rootGroup_le_posUnipotent (hroot i) (ht_single_pos i) (hx i)
  have hWxU : Wx ≤ (posUnipotent D).map π' := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, -, rfl⟩
    exact ⟨x i, hxU i, rfl⟩
  have hU2 : IsPGroup 2 ((posUnipotent D).map π') := (isPGroup_iSup_pos h.extras h.pGroup).map π'
  have hWxN : Wx ≤ Subgroup.normalizer (E : Set Y) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    refine mem_normalizer_closure_of_forall_conj_mem ?_
    rintro _ (⟨t, ht, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine Subgroup.subset_closure (Or.inl ⟨t, ht, ?_⟩)
      rw [← map_inv, ← map_mul, ← map_mul, ((hcx i hi t ht).symm.eq), mul_inv_cancel_right]
    · by_cases hij : i = j
      · subst hij
        have hx2 := hsq i hi _ (Or.inl rfl) _ (hx i)
        have hy2 := hsq i hi _ (Or.inr rfl) _ (hy i)
        have hxi : (x i)⁻¹ = x i := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
        have hyi : (y i)⁻¹ = y i := inv_eq_of_mul_eq_one_right (by rw [← sq, hy2])
        have e : π' (x i) * π' (x i * y i) * (π' (x i))⁻¹ = (π' (x i * y i))⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
          congr 1
          rw [mul_inv_rev, hxi, hyi]
          calc x i * (x i * y i) * x i = x i ^ 2 * y i * x i := by simp only [sq, mul_assoc]
            _ = y i * x i := by rw [hx2, one_mul]
        rw [e]
        exact inv_mem (Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩))
      · refine Subgroup.subset_closure (Or.inr ⟨j, hj, ?_⟩)
        have hcomm := commutes_rankOne_of_cartan_eq_zero hQ.extras hij (hcart i hi j hj hij) _
          (Subgroup.mem_sup_left (hx i)) _ (hxyL j)
        rw [← map_inv, ← map_mul, ← map_mul, hcomm, mul_inv_cancel_right]
  have hΛ : ∀ i ∈ negIndices D (J.comap π'), (rankOne D.rootGroup i).map π' ≤ E ⊔ Wx := by
    intro i hi
    have hiI : i ∈ I := (hmemI i).2 hi
    rw [rankOne, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      rcases eq_one_or_eq_of_mem_of_card_two (hcard2 i hiI _ (Or.inl rfl)) (hx i) hz (hx1 i hiI)
        with rfl | rfl
      · rw [map_one]
        exact one_mem _
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hiI, rfl⟩)
    · rintro _ ⟨z, hz, rfl⟩
      rcases eq_one_or_eq_of_mem_of_card_two (hcard2 i hiI _ (Or.inr rfl)) (hy i) hz (hy1 i hiI)
        with rfl | rfl
      · rw [map_one]
        exact one_mem _
      · have e : π' (y i) = (π' (x i))⁻¹ * π' (x i * y i) := by
          rw [map_mul, inv_mul_cancel_left]
        rw [e]
        exact mul_mem (inv_mem (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hiI, rfl⟩)))
          (Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr ⟨i, hiI, rfl⟩)))
  have hAne : J.comap π' ≠ borel D H := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i₀, -⟩ := negIndices_nonempty_of_ne hQ.ct hQ.extras hBA hAne
  have hEWJ : E ⊔ Wx ≤ J := sup_le hEJ (hWxU.trans ((Subgroup.map_mono posUnipotent_le_borel).trans
    hBJ))
  have hUJ : (posUnipotent D).map π' ≤ J := (Subgroup.map_mono posUnipotent_le_borel).trans hBJ
  have hprod : ∀ z ∈ J, ∃ a ∈ E ⊔ Wx, ∃ b ∈ (posUnipotent D).map π', z = a * b := by
    intro z hz
    obtain ⟨g, hg, b, ⟨b₀, hb₀, rfl⟩, rfl⟩ := exists_mul_of_mem_of_borel_le hQ.ct hQ.extras hπ'
      hBJ hz
    obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := exists_eq_mul_mul_of_mem_borel hQ.ct hQ.extras i₀ hb₀
    refine ⟨g * π' t, mul_mem (iSup₂_le hΛ hg)
      (Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl ⟨t, ht, rfl⟩))), π' (u * w),
      ⟨u * w, mul_mem (posUnipotentExcept_le_posUnipotent i₀ hu)
        (rootGroup_le_posUnipotent (hroot i₀) (ht_single_pos i₀) hw), rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_mul, mul_assoc, mul_assoc]
  have hdvd1 := card_dvd_mul_of_forall_mem_mul hEWJ hUJ hprod
  have hdvd2 : Nat.card ↥(E ⊔ Wx) ∣ Nat.card Wx * Nat.card E := by
    rw [sup_comm]
    exact card_sup_dvd_mul Wx E hWxN
  obtain ⟨a, ha⟩ := (hU2.to_le hWxU).exists_card_eq
  obtain ⟨b, hb⟩ := hU2.exists_card_eq
  refine isElemAbelian_of_le_of_card_dvd hEJ hEelem (a := a + b) ?_
  refine hdvd1.trans ((Nat.mul_dvd_mul_right hdvd2 _).trans ?_)
  rw [ha, hb, pow_add]
  exact dvd_of_eq (by ring)

end Three

end CFSG.AGLEmbedding.ParabHub
