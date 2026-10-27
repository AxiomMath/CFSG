module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassCascadeBasic
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassKill

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

@[expose] def cascPairL (τ : Tag) (j : Fin τ.rank) (v : Fin τ.rank → ℤ) : ℤ :=
  ((List.finRange τ.rank).map fun l => τ.cartan j l * v l).sum

@[expose] def cascCandB (τ : Tag) (J : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) : Bool :=
  (List.finRange τ.rank).all (fun l => J.contains l || decide (v l = 0)) &&
    decide (0 < ((List.finRange τ.rank).map v).sum) &&
      J.all fun j => decide (0 ≤ cascPairL τ j v)

@[expose] def cascNextL (τ : Tag) (J : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ) :
    List (Fin τ.rank) :=
  J.filter fun j => cascPairL τ j γ == 0

@[expose] def cascadeCheck (τ : Tag) (casc : List (Fin τ.rank → ℤ)) :
    ℕ → List (Fin τ.rank) → Bool
  | 0, _ => false
  | n + 1, J => τ.rootCertificate.roots.all fun code =>
      !cascCandB τ J (decodeVec code) ||
        (casc.any (fun σ => List.ofFn σ == List.ofFn (decodeVec (τ := τ) code)) &&
          cascadeCheck τ casc n (cascNextL τ J (decodeVec code)))

@[expose] def cascadeRoots : (τ : Tag) → List (Fin τ.rank → ℤ)
  | .D4 => [(![1, 1, 2, 1] : Fin 4 → ℤ), ![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 0, 1]]
  | .E6 => [(![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ), ![1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0],
      ![0, 0, 0, 1, 0, 0]]
  | .E7 => [(![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ), ![0, 1, 1, 2, 2, 2, 1], ![0, 1, 1, 2, 1, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0]]
  | .E8 => [(![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ), ![2, 2, 3, 4, 3, 2, 1, 0],
      ![0, 1, 1, 2, 2, 2, 1, 0], ![0, 1, 1, 2, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0],
      ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0]]
  | .G2 => []
  | .F4 => []

theorem cascadeCheck_cascadeRoots (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    cascadeCheck τ (cascadeRoots τ) (τ.rank + 1) (List.finRange τ.rank) = true := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem cascadeRoots_nodup (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    (cascadeRoots τ).Nodup := by
  have h : ((cascadeRoots τ).map List.ofFn).Nodup := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel
  exact h.of_map _

theorem cascPairL_eq (j : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    cascPairL τ j v = classKillPair j v := by
  rw [cascPairL, classKillPair, Fin.sum_univ_def]

theorem mem_cascNextL {J : List (Fin τ.rank)} {γ : Fin τ.rank → ℤ} {j : Fin τ.rank} :
    j ∈ cascNextL τ J γ ↔ j ∈ J ∧ classKillPair j γ = 0 := by
  simp [cascNextL, cascPairL_eq]

theorem setOf_mem_cascNextL (J : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ) :
    {j | j ∈ cascNextL τ J γ} = cascNext {j | j ∈ J} γ := by
  ext j
  exact mem_cascNextL

theorem cascCandB_eq_true {J : List (Fin τ.rank)} {v : Fin τ.rank → ℤ}
    (hv : v ∈ parabolicPosRoots τ {j | j ∈ J}) (hdom : ∀ j ∈ J, 0 ≤ classKillPair j v) :
    cascCandB τ J v = true := by
  simp only [cascCandB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq]
  refine ⟨⟨fun l => ?_, ?_⟩, fun j hj => ?_⟩
  · by_cases hl : l ∈ J
    · exact Or.inl hl
    · exact Or.inr (hv.1.2 l hl)
  · rw [← Fin.sum_univ_def]
    exact hv.2.2
  · rw [cascPairL_eq]
    exact hdom j hj

theorem cascade_parabolicPosRoots_finRange :
    parabolicPosRoots τ {j | j ∈ List.finRange τ.rank} = {α | IsRoot τ α ∧ 0 < height α} := by
  ext α
  simp only [parabolicPosRoots, parabolicRoots, Set.mem_inter_iff, Set.mem_ofPred_eq,
    List.mem_finRange, not_true_eq_false, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩


theorem cascadeCheck_sound {casc : List (Fin τ.rank → ℤ)} {n : ℕ} {J : List (Fin τ.rank)}
    (h : cascadeCheck τ casc (n + 1) J = true) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ parabolicPosRoots τ {j | j ∈ J}) (hdom : ∀ j ∈ J, 0 ≤ classKillPair j γ) :
    γ ∈ casc ∧ cascadeCheck τ casc n (cascNextL τ J γ) = true := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hγ.1.1
  have hmem : τ.rootCertificate.roots.getD k 0 ∈ τ.rootCertificate.roots := by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  simp only [cascadeCheck, List.all_eq_true] at h
  have h1 := h _ hmem
  have hc : cascCandB τ J (decodeVec (τ.rootCertificate.roots.getD k 0)) = true :=
    cascCandB_eq_true hγ hdom
  rw [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.any_eq_true] at h1
  obtain ⟨⟨σ, hσ, hσe⟩, h2⟩ := h1
  refine ⟨?_, h2⟩
  have e : σ = τ.rootCertificate.root k := RootCertificate.eq_of_ofFn_beq hσe
  exact e ▸ hσ

variable {K : Type} [Field K]


theorem cascade_exists_conj_of_check [CharP K 2] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (casc : List (Fin τ.rank → ℤ)) (n : ℕ) :
    ∀ J : List (Fin τ.rank), cascadeCheck τ casc n J = true →
      ∀ ℓ ∈ rootSpan τ K (parabolicPosRoots τ {j | j ∈ J}), ℓ ^ 2 = 1 →
        ∃ g ∈ cascadeConjGroup τ K {j | j ∈ J}, ∃ S : List (Fin τ.rank → ℤ), S.Nodup ∧
          (∀ σ ∈ S, σ ∈ casc ∧ σ ∈ parabolicPosRoots τ {j | j ∈ J}) ∧
          S.Pairwise (fun σ σ' => iform σ σ' = 0) ∧
          ∃ c : (Fin τ.rank → ℤ) → K, (∀ σ ∈ S, c σ ≠ 0) ∧
            g * ℓ * g⁻¹ = (S.map fun σ => pinnedX τ K σ (c σ)).prod := by
  induction n with
  | zero =>
    intro J hJ
    simp [cascadeCheck] at hJ
  | succ n ih =>
    intro J hJ ℓ hℓ h2
    by_cases hℓ1 : ℓ = 1
    · refine ⟨1, one_mem _, [], List.nodup_nil, by simp, List.Pairwise.nil, fun _ => 0,
        by simp, ?_⟩
      simp [hℓ1]
    obtain ⟨ω₁, hω₁, i, hi, c, hc, u, hu, he₁⟩ :=
      exists_prod_weylElt_conj_eq_pinnedX_simple_mul {j | j ∈ J} hℓ hℓ1
    set P₁ := (ω₁.map fun j => weylElt τ K j 1).prod with hP₁
    have h2₁ : (pinnedX τ K (Pi.single i 1) c * u) ^ 2 = 1 := by
      rw [← he₁, conj_pow, h2, mul_one, mul_inv_cancel]
    obtain ⟨p, hp, u'', hu'', -, he₂⟩ := exists_conj_eq_mul_of_classKillPerp_longSimple
      {j | j ∈ J} hi (mem_classKillLongSimple_of_simplyLaced hτ i) hc hu h2₁
    rw [classKillPerp_eq_cascPerp] at hu''
    have hiJ : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicPosRoots τ {j | j ∈ J} :=
      ⟨⟨isRoot_single τ i, fun l hl => Pi.single_eq_of_ne (by rintro rfl; exact hl hi) 1⟩,
        isRoot_single τ i, by rw [height_single]; exact one_pos⟩
    obtain ⟨ω₂, hω₂, γ, hγ, hdom, ε, hε, z, hz, he₃⟩ :=
      exists_prod_weylElt_conj_eq_dominant {j | j ∈ J} hiJ c hu''
    set P₂ := (ω₂.map fun j => weylElt τ K j 1).prod with hP₂
    obtain ⟨hγc, hJ'⟩ := cascadeCheck_sound hJ hγ hdom
    have hzJ' : z ∈ rootSpan τ K (parabolicPosRoots τ {j | j ∈ cascNextL τ J γ}) := by
      rw [setOf_mem_cascNextL]
      exact classDescent_rootSpan_mono (cascPerp_subset_of_dominant hdom) hz
    have hθ : ∀ j ∈ {j | j ∈ cascNextL τ J γ}, classKillPair j γ = 0 := fun j hj =>
      (mem_cascNextL.1 hj).2
    have hmono : {j | j ∈ cascNextL τ J γ} ⊆ {j | j ∈ J} := fun j hj => (mem_cascNextL.1 hj).1
    have hcen := cascadeConjGroup_le_centralizer (K := K) hτ hγ.1.1 hγ.2.2 hθ (ε * c)
    have hcomm : z * pinnedX τ K γ (ε * c) = pinnedX τ K γ (ε * c) * z :=
      Subgroup.mem_centralizer_singleton_iff.1 (hcen (rootSpan_le_cascadeConjGroup _ hzJ'))
    have hconj : pinnedX τ K γ (ε * c) * z = (P₂ * p * P₁) * ℓ * (P₂ * p * P₁)⁻¹ := by
      rw [← he₃, ← he₂, ← he₁]
      group
    have hz2 : z ^ 2 = 1 := by
      have hx2 : (pinnedX τ K γ (ε * c) * z) ^ 2 = 1 := by
        rw [hconj, conj_pow, h2, mul_one, mul_inv_cancel]
      have hxx := classKill_pinnedX_mul_self γ (ε * c)
      calc z ^ 2 = pinnedX τ K γ (ε * c) * pinnedX τ K γ (ε * c) * (z * z) := by
            rw [hxx, one_mul, sq]
        _ = pinnedX τ K γ (ε * c) * (pinnedX τ K γ (ε * c) * z) * z := by group
        _ = pinnedX τ K γ (ε * c) * (z * pinnedX τ K γ (ε * c)) * z := by rw [hcomm]
        _ = (pinnedX τ K γ (ε * c) * z) ^ 2 := by rw [sq]; group
        _ = 1 := hx2
    obtain ⟨g', hg', S', hS'nd, hS', hS'o, c', hc', he₄⟩ := ih _ hJ' z hzJ' hz2
    have hγS' : ∀ σ ∈ S', σ ≠ γ := by
      intro σ hσ hσγ
      have h := (hS' σ hσ).2
      rw [hσγ, setOf_mem_cascNextL] at h
      exact cascade_not_mem_cascNext hτ hγ.1.1 h
    have hg'x : g' * pinnedX τ K γ (ε * c) * g'⁻¹ = pinnedX τ K γ (ε * c) := by
      have h := Subgroup.mem_centralizer_singleton_iff.1 (hcen hg')
      rw [h]
      group
    refine ⟨g' * P₂ * p * P₁, ?_, γ :: S', List.nodup_cons.2 ⟨fun h => hγS' γ h rfl, hS'nd⟩,
      fun σ hσ => ?_, List.pairwise_cons.2 ⟨fun σ hσ => ?_, hS'o⟩,
      Function.update c' γ (ε * c), fun σ hσ => ?_, ?_⟩
    · exact mul_mem (mul_mem (mul_mem (cascadeConjGroup_mono hmono hg')
        (prod_weylElt_mem_cascadeConjGroup hω₂))
        (rootSpan_le_cascadeConjGroup _ (classDescent_rootSpan_mono Set.sdiff_subset hp)))
        (prod_weylElt_mem_cascadeConjGroup hω₁)
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · exact ⟨hγc, hγ⟩
      · obtain ⟨hσc, ⟨hσr, hσs⟩, hσp⟩ := hS' σ hσ
        exact ⟨hσc, ⟨hσr, fun l hl => hσs l fun h => hl (hmono h)⟩, hσp⟩
    · exact cascade_iform_eq_zero_of_mem hθ (hS' σ hσ).2
    · rcases List.mem_cons.1 hσ with rfl | hσ
      · rw [Function.update_self]
        exact mul_ne_zero (left_ne_zero_of_mul_eq_one hε) hc
      · rw [Function.update_of_ne (hγS' σ hσ)]
        exact hc' σ hσ
    · have hmap : (S'.map fun σ => pinnedX τ K σ (Function.update c' γ (ε * c) σ)) =
          S'.map fun σ => pinnedX τ K σ (c' σ) :=
        List.map_congr_left fun σ hσ => by rw [Function.update_of_ne (hγS' σ hσ)]
      rw [List.map_cons, List.prod_cons, Function.update_self, hmap, ← he₄]
      calc g' * P₂ * p * P₁ * ℓ * (g' * P₂ * p * P₁)⁻¹
          = g' * (P₂ * p * P₁ * ℓ * (P₂ * p * P₁)⁻¹) * g'⁻¹ := by group
        _ = g' * (pinnedX τ K γ (ε * c) * z) * g'⁻¹ := by rw [← hconj]
        _ = (g' * pinnedX τ K γ (ε * c) * g'⁻¹) * (g' * z * g'⁻¹) := by group
        _ = pinnedX τ K γ (ε * c) * (g' * z * g'⁻¹) := by rw [hg'x]

theorem cascade_list_prod_eq_filter (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {S : List (Fin τ.rank → ℤ)} (hSnd : S.Nodup)
    (hS : ∀ σ ∈ S, σ ∈ cascadeRoots τ ∧ IsRoot τ σ ∧ 0 < height σ)
    (hSo : S.Pairwise (fun σ σ' => iform σ σ' = 0)) (c : (Fin τ.rank → ℤ) → K) :
    (S.map fun σ => pinnedX τ K σ (c σ)).prod =
      (((cascadeRoots τ).filter fun σ => decide (σ ∈ S)).map
        fun σ => pinnedX τ K σ (c σ)).prod := by
  have hperm : S.Perm ((cascadeRoots τ).filter fun σ => decide (σ ∈ S)) :=
    (List.perm_ext_iff_of_nodup hSnd ((cascadeRoots_nodup hτ).filter _)).2 fun σ => by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => ⟨(hS σ h).1, h⟩, fun h => h.2⟩
  refine (hperm.map _).prod_eq' (List.pairwise_map.2 (hSo.imp_of_mem fun ha hb h => ?_))
  exact cascade_commute_pinnedX hτ (hS _ ha).2.1 (hS _ ha).2.2 (hS _ hb).2.1 (hS _ hb).2.2 h _ _

theorem exists_mem_cascadeConjGroup_conj_eq_cascade_prod [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ : ModGL τ K}
    (hℓ : ℓ ∈ posUnipotent τ K) (h2 : ℓ ^ 2 = 1) :
    ∃ g ∈ cascadeConjGroup τ K Set.univ, ∃ S : List (Fin τ.rank → ℤ), S.Nodup ∧
      (∀ σ ∈ S, σ ∈ cascadeRoots τ ∧ IsRoot τ σ ∧ 0 < height σ) ∧
      S.Pairwise (fun σ σ' => iform σ σ' = 0) ∧
      ∃ c : (Fin τ.rank → ℤ) → K, (∀ σ ∈ S, c σ ≠ 0) ∧
        g * ℓ * g⁻¹ = (S.map fun σ => pinnedX τ K σ (c σ)).prod := by
  have huniv : {j | j ∈ List.finRange τ.rank} = (Set.univ : Set (Fin τ.rank)) := by
    ext j
    simp
  obtain ⟨g, hg, S, hSnd, hS, hSo, c, hc, he⟩ := cascade_exists_conj_of_check hτ
    (cascadeRoots τ) _ _ (cascadeCheck_cascadeRoots hτ) ℓ
    (by rw [cascade_parabolicPosRoots_finRange]; exact hℓ) h2
  rw [huniv] at hg
  exact ⟨g, hg, S, hSnd, fun σ hσ => ⟨(hS σ hσ).1, (hS σ hσ).2.2.1, (hS σ hσ).2.2.2⟩, hSo, c,
    hc, he⟩

theorem exists_mem_cascadeConjGroup_conj_eq_cascade_sublist_prod [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ : ModGL τ K}
    (hℓ : ℓ ∈ posUnipotent τ K) (h2 : ℓ ^ 2 = 1) :
    ∃ g ∈ cascadeConjGroup τ K Set.univ, ∃ S : List (Fin τ.rank → ℤ),
      S.Sublist (cascadeRoots τ) ∧ ∃ c : (Fin τ.rank → ℤ) → K, (∀ σ ∈ S, c σ ≠ 0) ∧
        g * ℓ * g⁻¹ = (S.map fun σ => pinnedX τ K σ (c σ)).prod := by
  obtain ⟨g, hg, S, hSnd, hS, hSo, c, hc, he⟩ :=
    exists_mem_cascadeConjGroup_conj_eq_cascade_prod hτ hℓ h2
  refine ⟨g, hg, (cascadeRoots τ).filter fun σ => decide (σ ∈ S), List.filter_sublist, c,
    fun σ hσ => hc σ (by simpa using (List.mem_filter.1 hσ).2), ?_⟩
  rw [he]
  exact cascade_list_prod_eq_filter hτ hSnd hS hSo c

theorem exists_conj_eq_cascade_prod_of_pairwise [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {t : adjointGroup τ K} (ht : t ^ 2 = 1) :
    ∃ g : adjointGroup τ K, ∃ S : List (Fin τ.rank → ℤ), S.Nodup ∧
      (∀ σ ∈ S, σ ∈ cascadeRoots τ ∧ IsRoot τ σ ∧ 0 < height σ) ∧
      S.Pairwise (fun σ σ' => iform σ σ' = 0) ∧
      ∃ c : (Fin τ.rank → ℤ) → K, (∀ σ ∈ S, c σ ≠ 0) ∧
        ((g * t * g⁻¹ : adjointGroup τ K) : ModGL τ K) =
          (S.map fun σ => pinnedX τ K σ (c σ)).prod := by
  obtain ⟨g₁, hg₁⟩ := cascade_exists_conj_mem_posUnipotent ht
  have h2 : ((g₁ * t * g₁⁻¹ : adjointGroup τ K) : ModGL τ K) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, conj_pow, ht, mul_one, mul_inv_cancel, Subgroup.coe_one]
  obtain ⟨g₂, hg₂, S, hSnd, hS, hSo, c, hc, he⟩ :=
    exists_mem_cascadeConjGroup_conj_eq_cascade_prod hτ hg₁ h2
  refine ⟨⟨g₂, cascadeConjGroup_le_adjointGroup _ hg₂⟩ * g₁, S, hSnd, hS, hSo, c, hc, ?_⟩
  rw [← he]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
  group

theorem exists_conj_eq_cascade_prod [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {t : adjointGroup τ K} (ht : t ^ 2 = 1) :
    ∃ g : adjointGroup τ K, ∃ S : List (Fin τ.rank → ℤ), S.Sublist (cascadeRoots τ) ∧
      ∃ c : (Fin τ.rank → ℤ) → K, (∀ σ ∈ S, c σ ≠ 0) ∧
        ((g * t * g⁻¹ : adjointGroup τ K) : ModGL τ K) =
          (S.map fun σ => pinnedX τ K σ (c σ)).prod := by
  obtain ⟨g, S, hSnd, hS, hSo, c, hc, he⟩ := exists_conj_eq_cascade_prod_of_pairwise hτ ht
  refine ⟨g, (cascadeRoots τ).filter fun σ => decide (σ ∈ S), List.filter_sublist, c,
    fun σ hσ => hc σ (by simpa using (List.mem_filter.1 hσ).2), ?_⟩
  rw [he]
  exact cascade_list_prod_eq_filter hτ hSnd hS hSo c

theorem exists_conj_eq_prod_cascadeRoots [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {t : adjointGroup τ K} (ht : t ^ 2 = 1) :
    ∃ g : adjointGroup τ K, ∃ c : (Fin τ.rank → ℤ) → K,
      ((g * t * g⁻¹ : adjointGroup τ K) : ModGL τ K) =
        ((cascadeRoots τ).map fun σ => pinnedX τ K σ (c σ)).prod := by
  classical
  obtain ⟨g, S, hSnd, hS, hSo, c, -, he⟩ := exists_conj_eq_cascade_prod_of_pairwise hτ ht
  set c' : (Fin τ.rank → ℤ) → K := fun σ => if σ ∈ S then c σ else 0 with hc'
  refine ⟨g, c', ?_⟩
  rw [he, cascade_list_prod_eq_filter hτ hSnd hS hSo c,
    ← classDescent_prod_map_filter (cascadeRoots τ) (fun σ => decide (σ ∈ S))
      (fun σ => pinnedX τ K σ (c' σ)) fun σ _ h => ?_]
  · refine congrArg List.prod (List.map_congr_left fun σ hσ => ?_)
    have h : σ ∈ S := by simpa using (List.mem_filter.1 hσ).2
    simp [hc', h]
  · have h' : σ ∉ S := by simpa using h
    simp [hc', h', pinnedX_zero]

end CFSG.SeitzReduction
