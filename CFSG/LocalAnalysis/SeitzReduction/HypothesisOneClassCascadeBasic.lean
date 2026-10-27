module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassDescent
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassKillBasic

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem cascade_symmetrizer_pos (j : Fin τ.rank) : 0 < τ.symmetrizer j j := by
  revert j
  cases τ <;> decide

theorem cascade_symmetrizer_eq_one (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (j : Fin τ.rank) : τ.symmetrizer j j = 1 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> simp [Tag.symmetrizer]

theorem cascade_reflect_eq (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ j v = v - classKillPair j v • Pi.single j 1 :=
  rfl

theorem cascade_height_reflect (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    height (reflect τ j v) = height v - classKillPair j v := by
  simp only [height, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib]
  simp [Pi.single_apply, classKillPair]


theorem cascade_iform_single_right (x : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    iform x (Pi.single j 1) = τ.symmetrizer j j * classKillPair j x :=
  iform_single_right x j

theorem cascade_iform_single_left (j : Fin τ.rank) (x : Fin τ.rank → ℤ) :
    iform (Pi.single j 1) x = τ.symmetrizer j j * classKillPair j x :=
  iform_single_left j x

theorem cascade_iform_eq_sum (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ j, τ.symmetrizer j j * classKillPair j x * y j := by
  have h : ∀ j, iform x (Pi.single j 1) = ∑ i, x i * τ.symmetrizedCartan i j := fun j => by
    simp [iform, Pi.single_apply]
  calc iform x y = ∑ j, (∑ i, x i * τ.symmetrizedCartan i j) * y j := by
        rw [iform, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ = ∑ j, τ.symmetrizer j j * classKillPair j x * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← h, cascade_iform_single_right]

theorem cascade_iform_self (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj, cascade_symmetrizer_eq_one hτ, mul_one]

theorem cascade_not_isRoot_of_iform_eq_zero (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (h0 : iform γ δ = 0) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬ IsRoot τ (a • γ + b • δ) := by
  intro a b ha hb hr
  have h := cascade_iform_self hτ hr
  have e : (a • γ + b • δ : Fin τ.rank → ℤ) = (a : ℤ) • γ + (b : ℤ) • δ := by
    rw [natCast_zsmul, natCast_zsmul]
  rw [e] at h
  simp only [iform_add_left, iform_add_right, iform_smul_left, iform_smul_right] at h
  rw [cascade_iform_self hτ hγ, cascade_iform_self hτ hδ, iform_comm δ γ, h0] at h
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith

@[expose] def cascPerp (τ : Tag) (J : Set (Fin τ.rank)) (γ : Fin τ.rank → ℤ) :
    Set (Fin τ.rank → ℤ) :=
  {δ | δ ∈ parabolicPosRoots τ J ∧ iform γ δ = 0}

@[expose] def cascNext (J : Set (Fin τ.rank)) (γ : Fin τ.rank → ℤ) : Set (Fin τ.rank) :=
  {j | j ∈ J ∧ classKillPair j γ = 0}

theorem classKillPerp_eq_cascPerp (J : Set (Fin τ.rank)) (i : Fin τ.rank) :
    classKillPerp τ J i = cascPerp τ J (Pi.single i 1) := by
  ext δ
  simp only [classKillPerp, cascPerp, Set.mem_ofPred_eq, cascade_iform_single_left]
  refine and_congr_right fun _ => ⟨fun h => by rw [h, mul_zero], fun h => ?_⟩
  exact (mul_eq_zero.1 h).resolve_left (cascade_symmetrizer_pos i).ne'

theorem cascade_iform_eq_zero_of_mem {J : Set (Fin τ.rank)} {θ δ : Fin τ.rank → ℤ}
    (hθ : ∀ j ∈ J, classKillPair j θ = 0) (hδ : δ ∈ parabolicPosRoots τ J) :
    iform θ δ = 0 := by
  rw [cascade_iform_eq_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j ∈ J
  · rw [hθ j hj, mul_zero, zero_mul]
  · rw [hδ.1.2 j hj, mul_zero]

theorem cascPerp_subset_of_dominant {J : Set (Fin τ.rank)} {γ : Fin τ.rank → ℤ}
    (hdom : ∀ j ∈ J, 0 ≤ classKillPair j γ) :
    cascPerp τ J γ ⊆ parabolicPosRoots τ (cascNext J γ) := by
  rintro δ ⟨hδ, h0⟩
  have hnn := (IsRoot.height_pos_iff hδ.2.1).1 hδ.2.2
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin τ.rank)),
      0 ≤ τ.symmetrizer j j * classKillPair j γ * δ j := by
    intro j _
    by_cases hj : j ∈ J
    · exact mul_nonneg (mul_nonneg (cascade_symmetrizer_pos j).le (hdom j hj)) (hnn j)
    · rw [hδ.1.2 j hj, mul_zero]
  rw [cascade_iform_eq_sum] at h0
  refine ⟨⟨hδ.1.1, fun l hl => ?_⟩, hδ.2⟩
  by_cases hlJ : l ∈ J
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 h0 l (Finset.mem_univ l)
    have hpos : 0 < classKillPair l γ := lt_of_le_of_ne (hdom l hlJ) fun h => hl ⟨hlJ, h.symm⟩
    exact (mul_eq_zero.1 hz).resolve_left (mul_pos (cascade_symmetrizer_pos l) hpos).ne'
  · exact hδ.1.2 l hlJ

theorem cascade_not_mem_cascNext (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {J : Set (Fin τ.rank)} {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    γ ∉ parabolicPosRoots τ (cascNext J γ) := fun h => by
  have := cascade_iform_eq_zero_of_mem (fun j hj => hj.2) h
  rw [cascade_iform_self hτ hγ] at this
  exact two_ne_zero this

theorem cascade_reflect_mem_of_neg {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ parabolicPosRoots τ J) (hneg : classKillPair j γ < 0) :
    reflect τ j γ ∈ parabolicPosRoots τ J ∧ height γ < height (reflect τ j γ) := by
  have hht := cascade_height_reflect j γ
  have hr : IsRoot τ (reflect τ j γ) := IsRoot.reflect j hγ.1.1
  refine ⟨⟨⟨hr, fun l hl => ?_⟩, hr, by linarith [hγ.2.2]⟩, by linarith⟩
  rw [reflect_apply_of_ne j (by rintro rfl; exact hl hj)]
  exact hγ.1.2 l hl

theorem cascade_reflect_mem_cascPerp {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J)
    {γ : Fin τ.rank → ℤ} (hγj : classKillPair j γ ≠ 0) {δ : Fin τ.rank → ℤ}
    (hδ : δ ∈ cascPerp τ J γ) : reflect τ j δ ∈ cascPerp τ J (reflect τ j γ) := by
  obtain ⟨⟨⟨hδr, hδs⟩, -, hδp⟩, h0⟩ := hδ
  have hne : δ ≠ Pi.single j 1 := by
    rintro rfl
    rw [cascade_iform_single_right] at h0
    exact hγj ((mul_eq_zero.1 h0).resolve_left (cascade_symmetrizer_pos j).ne')
  refine ⟨⟨⟨IsRoot.reflect j hδr, fun l hl => ?_⟩, IsRoot.reflect j hδr,
    height_reflect_pos hδr hδp hne⟩, ?_⟩
  · rw [reflect_apply_of_ne j (by rintro rfl; exact hl hj)]
    exact hδs l hl
  · rw [iform_reflect]
    exact h0

theorem cascade_exists_height_bound (τ : Tag) : ∃ M : ℕ, ∀ α, IsRoot τ α → height α ≤ M := by
  obtain ⟨M, hM⟩ := ((finite_setOf_isRoot τ).image height).bddAbove
  refine ⟨M.toNat, fun α hα => ?_⟩
  have h1 : height α ≤ M := hM ⟨α, hα, rfl⟩
  have h2 := Int.self_le_toNat M
  omega

variable {K : Type} [Field K]

@[expose] noncomputable def cascadeConjGroup (τ : Tag) (K : Type) [Field K]
    (J : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  rootSpan τ K (parabolicPosRoots τ J) ⊔ Subgroup.closure {g | ∃ j ∈ J, g = weylElt τ K j 1}

theorem rootSpan_le_cascadeConjGroup (J : Set (Fin τ.rank)) :
    rootSpan τ K (parabolicPosRoots τ J) ≤ cascadeConjGroup τ K J :=
  le_sup_left

theorem prod_weylElt_mem_cascadeConjGroup {J : Set (Fin τ.rank)} {ω : List (Fin τ.rank)}
    (hω : ∀ j ∈ ω, j ∈ J) : (ω.map fun j => weylElt τ K j 1).prod ∈ cascadeConjGroup τ K J := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
  exact (le_sup_right : Subgroup.closure {g | ∃ j ∈ J, g = weylElt τ K j 1} ≤ _)
    (Subgroup.subset_closure ⟨j, hω j hj, rfl⟩)

theorem cascadeConjGroup_mono {J J' : Set (Fin τ.rank)} (h : J' ⊆ J) :
    cascadeConjGroup τ K J' ≤ cascadeConjGroup τ K J := by
  refine sup_le_sup (classDescent_rootSpan_mono ?_) (Subgroup.closure_mono ?_)
  · rintro α ⟨⟨hα, hs⟩, hp⟩
    exact ⟨⟨hα, fun l hl => hs l fun h' => hl (h h')⟩, hp⟩
  · rintro g ⟨j, hj, rfl⟩
    exact ⟨j, h hj, rfl⟩

theorem cascadeConjGroup_le_adjointGroup (J : Set (Fin τ.rank)) :
    cascadeConjGroup τ K J ≤ adjointGroup τ K := by
  refine sup_le (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, -, rfl⟩
  exact weylElt_mem_adjointGroup j 1



theorem cascade_conj_weylElt_mem_rootSpan {S S' : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) (j : Fin τ.rank) (hSS' : ∀ α ∈ S, reflect τ j α ∈ S')
    {z : ModGL τ K} (hz : z ∈ rootSpan τ K S) :
    weylElt τ K j 1 * z * (weylElt τ K j 1)⁻¹ ∈ rootSpan τ K S' := by
  have hle : (rootSpan τ K S).map (MulAut.conj (weylElt τ K j 1)).toMonoidHom ≤
      rootSpan τ K S' := by
    simp only [rootSpan, Subgroup.map_iSup]
    refine iSup₂_le fun α hα => ?_
    rw [map_conj_weylElt_rootSubgroup K j (hS α hα)]
    exact le_iSup₂_of_le (reflect τ j α) (hSS' α hα) le_rfl
  exact hle ⟨z, hz, rfl⟩

theorem cascade_exists_word_dominant (J : Set (Fin τ.rank)) (N : ℕ) :
    ∀ γ ∈ parabolicPosRoots τ J, (∀ α, IsRoot τ α → height α ≤ height γ + N) →
      ∀ (c : K) (z : ModGL τ K), z ∈ rootSpan τ K (cascPerp τ J γ) →
        ∃ ω : List (Fin τ.rank), (∀ j ∈ ω, j ∈ J) ∧ ∃ γ' ∈ parabolicPosRoots τ J,
          (∀ j ∈ J, 0 ≤ classKillPair j γ') ∧ ∃ ε : K, ε * ε = 1 ∧
            ∃ z' ∈ rootSpan τ K (cascPerp τ J γ'),
              (ω.map fun j => weylElt τ K j 1).prod * (pinnedX τ K γ c * z) *
                  ((ω.map fun j => weylElt τ K j 1).prod)⁻¹ = pinnedX τ K γ' (ε * c) * z' := by
  induction N with
  | zero =>
    intro γ hγ hN c z hz
    refine ⟨[], by simp, γ, hγ, fun j hj => ?_, 1, one_mul 1, z, hz, by simp⟩
    by_contra hneg
    push Not at hneg
    have h1 := (cascade_reflect_mem_of_neg hj hγ hneg).2
    have h2 := hN _ (IsRoot.reflect j hγ.1.1)
    push_cast at h2
    linarith
  | succ N ih =>
    intro γ hγ hN c z hz
    by_cases hdom : ∀ j ∈ J, 0 ≤ classKillPair j γ
    · exact ⟨[], by simp, γ, hγ, hdom, 1, one_mul 1, z, hz, by simp⟩
    push Not at hdom
    obtain ⟨j, hj, hneg⟩ := hdom
    obtain ⟨hγ₁, hlt⟩ := cascade_reflect_mem_of_neg hj hγ hneg
    have hN₁ : ∀ α, IsRoot τ α → height α ≤ height (reflect τ j γ) + N := by
      intro α hα
      have := hN α hα
      push_cast at this ⊢
      linarith
    obtain ⟨ε₁, hε₁, hx⟩ := weylElt_mul_pinnedX_mul_inv K j hγ.1.1
    have hz₁ := cascade_conj_weylElt_mem_rootSpan (fun α hα => hα.1.1.1) j
      (fun α hα => cascade_reflect_mem_cascPerp hj hneg.ne hα) hz
    obtain ⟨ω, hω, γ', hγ', hdom', ε, hε, z', hz', he⟩ := ih _ hγ₁ hN₁ (ε₁ * c) _ hz₁
    refine ⟨ω ++ [j], fun j' hj' => ?_, γ', hγ', hdom', ε * ε₁, ?_, z', hz', ?_⟩
    · rcases List.mem_append.1 hj' with h | h
      · exact hω j' h
      · rw [List.mem_singleton.1 h]
        exact hj
    · linear_combination (ε₁ * ε₁) * hε + hε₁
    · rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
        mul_assoc ε, ← he, ← hx c]
      group

theorem exists_prod_weylElt_conj_eq_dominant (J : Set (Fin τ.rank)) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ parabolicPosRoots τ J) (c : K) {z : ModGL τ K}
    (hz : z ∈ rootSpan τ K (cascPerp τ J γ)) :
    ∃ ω : List (Fin τ.rank), (∀ j ∈ ω, j ∈ J) ∧ ∃ γ' ∈ parabolicPosRoots τ J,
      (∀ j ∈ J, 0 ≤ classKillPair j γ') ∧ ∃ ε : K, ε * ε = 1 ∧
        ∃ z' ∈ rootSpan τ K (cascPerp τ J γ'),
          (ω.map fun j => weylElt τ K j 1).prod * (pinnedX τ K γ c * z) *
              ((ω.map fun j => weylElt τ K j 1).prod)⁻¹ = pinnedX τ K γ' (ε * c) * z' := by
  obtain ⟨M, hM⟩ := cascade_exists_height_bound τ
  exact cascade_exists_word_dominant J M γ hγ (fun α hα => by linarith [hM α hα, hγ.2.2]) c z hz

theorem cascade_weylElt_conj_pinnedX [CharP K 2] {j : Fin τ.rank} {θ : Fin τ.rank → ℤ}
    (hθ : IsRoot τ θ) (h0 : classKillPair j θ = 0) (c : K) :
    weylElt τ K j 1 * pinnedX τ K θ c * (weylElt τ K j 1)⁻¹ = pinnedX τ K θ c := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K j hθ
  have hr : reflect τ j θ = θ := by rw [cascade_reflect_eq, h0, zero_smul, sub_zero]
  have hε1 : ε = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  rw [h, hr, hε1, one_mul]



theorem cascade_commute_pinnedX (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγp : 0 < height γ) (hδ : IsRoot τ δ)
    (hδp : 0 < height δ) (h0 : iform γ δ = 0) (c d : K) :
    Commute (pinnedX τ K γ c) (pinnedX τ K δ d) := by
  have hne : γ ≠ δ := by
    rintro rfl
    rw [cascade_iform_self hτ hγ] at h0
    exact two_ne_zero h0
  have hle := commutator_rootSubgroup_le K hγ hδ hγp hδp hne
  have hbot : (⨆ (η : Fin τ.rank → ℤ) (_ : IsRoot τ η ∧
      ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ η = a • γ + b • δ), rootSubgroup τ K η) = ⊥ :=
    iSup₂_eq_bot.2 fun η ⟨hη, a, b, ha, hb, hηe⟩ =>
      absurd (hηe ▸ hη) (cascade_not_isRoot_of_iform_eq_zero hτ hγ hδ h0 a b ha hb)
  rw [hbot] at hle
  have hmem := hle (Subgroup.commutator_mem_commutator (Subgroup.subset_closure ⟨c, rfl⟩)
    (Subgroup.subset_closure ⟨d, rfl⟩))
  exact commutatorElement_eq_one_iff_commute.1 ((Subgroup.mem_bot).1 hmem)

theorem cascadeConjGroup_le_centralizer [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {J : Set (Fin τ.rank)}
    {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (hθp : 0 < height θ)
    (hθJ : ∀ j ∈ J, classKillPair j θ = 0) (c : K) :
    cascadeConjGroup τ K J ≤ Subgroup.centralizer {pinnedX τ K θ c} := by
  refine sup_le (iSup₂_le fun δ hδ => (Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨d, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (cascade_commute_pinnedX hτ hθ hθp hδ.2.1 hδ.2.2
      (cascade_iform_eq_zero_of_mem hθJ hδ) c d).eq.symm
  · rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h := cascade_weylElt_conj_pinnedX hθ (hθJ j hj) c
    calc weylElt τ K j 1 * pinnedX τ K θ c
        = weylElt τ K j 1 * pinnedX τ K θ c * (weylElt τ K j 1)⁻¹ * weylElt τ K j 1 := by group
      _ = pinnedX τ K θ c * weylElt τ K j 1 := by rw [h]


theorem cascade_exists_conj_mem_posUnipotent [Finite K] [CharP K 2] {t : adjointGroup τ K}
    (ht : t ^ 2 = 1) :
    ∃ g : adjointGroup τ K, ((g * t * g⁻¹ : adjointGroup τ K) : ModGL τ K) ∈ posUnipotent τ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := τ) (K := K)
  have hUC : posUnipotent τ K ≤ adjointGroup τ K :=
    iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α
  obtain ⟨hp, hi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hto : orderOf t ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one ht
  obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hto
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := l) (by rw [Nat.card_zpowers, hl])
  obtain ⟨Q, hQ⟩ := htp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (adjointGroup τ K) (hp.toSylow hi) Q
  have htQ : t ∈ (Q : Subgroup (adjointGroup τ K)) := hQ (Subgroup.mem_zpowers t)
  rw [← ha, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    IsPGroup.toSylow_coe, MulAut.smul_def, MulAut.conj_inv_apply] at htQ
  exact ⟨a⁻¹, by simpa [Subgroup.mem_subgroupOf] using htQ⟩

end CFSG.SeitzReduction
