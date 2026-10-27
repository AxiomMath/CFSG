module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem classDescent_prod_map_filter {G ι : Type*} [Monoid G] (l : List ι) (p : ι → Bool)
    (g : ι → G) (h : ∀ x ∈ l, p x = false → g x = 1) :
    ((l.filter p).map g).prod = (l.map g).prod := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih' := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    by_cases hx : p x
    · rw [List.filter_cons_of_pos hx, List.map_cons, List.prod_cons, List.map_cons,
        List.prod_cons, ih']
    · rw [List.filter_cons_of_neg hx, List.map_cons, List.prod_cons,
        h x List.mem_cons_self (by simpa using hx), one_mul, ih']

theorem classDescent_rootSpan_mono
    {τ : Tag} {S T : Set (Fin τ.rank → ℤ)} (h : S ⊆ T) : rootSpan τ K S ≤ rootSpan τ K T :=
  iSup₂_le fun α hα => le_iSup₂_of_le α (h hα) le_rfl

theorem classDescent_list_prod_mem_rootSpan
    {τ : Tag} {S : Set (Fin τ.rank → ℤ)}
    (L : List (Fin τ.rank → ℤ)) (hL : ∀ α ∈ L, α ∈ S) (c : (Fin τ.rank → ℤ) → K) :
    (L.map fun α => pinnedX τ K α (c α)).prod ∈ rootSpan τ K S := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hx
  exact (le_iSup₂_of_le α (hL α hα) le_rfl : rootSubgroup τ K α ≤ rootSpan τ K S)
    (Subgroup.subset_closure ⟨c α, rfl⟩)

theorem classDescent_eq_single_of_height_eq_one
    {τ : Tag} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h1 : height α = 1) : ∃ j, α = Pi.single j 1 := by
  classical
  have hnn := (IsRoot.height_pos_iff hα).1 (by omega)
  obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
    by_contra h
    push Not at h
    exact IsRoot.ne_zero hα (funext h)
  have hsum : height α = ∑ k, α k := rfl
  have hle : ∀ k, α k ≤ height α := fun k =>
    Finset.single_le_sum (fun k _ => hnn k) (Finset.mem_univ k)
  have hj1 : α j = 1 := by have := hle j; have := hnn j; omega
  refine ⟨j, funext fun k => ?_⟩
  by_cases hkj : k = j
  · subst hkj
    rw [hj1, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hkj]
    have hpair : α j + α k ≤ height α := by
      rw [hsum, ← Finset.sum_pair (f := α) (Ne.symm hkj)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun l _ _ => hnn l
    have := hnn k
    omega

theorem classDescent_parabolicPosRoots_closed {τ : Tag} (J : Set (Fin τ.rank)) :
    ∀ α ∈ parabolicPosRoots τ J, ∀ β ∈ parabolicPosRoots τ J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ parabolicPosRoots τ J := by
  intro α hα β hβ a b ha hb hr
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  refine ⟨⟨hr, fun l hl => ?_⟩, hr, ?_⟩
  · simp [hα.1.2 l hl, hβ.1.2 l hl]
  · rw [height_nsmul_add_nsmul]
    nlinarith [hα.2.2, hβ.2.2]

theorem classDescent_wordProd_mem_closure {τ : Tag} {J : Set (Fin τ.rank)}
    {ω : List (Fin τ.rank)} (hω : ∀ j ∈ ω, j ∈ J) :
    (coxeterSystem τ).wordProd ω ∈ Subgroup.closure ((simple τ) '' J) := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil]; exact one_mem _
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons]
    exact mul_mem (Subgroup.subset_closure ⟨j, hω j List.mem_cons_self, rfl⟩)
      (ih fun j' hj' => hω j' (List.mem_cons_of_mem _ hj'))

theorem classDescent_prod_weylElt_eq_mul_canonicalRep
    {τ : Tag} (ω : List (Fin τ.rank)) :
    ∃ k ∈ torusGroup τ K, (ω.map fun j => weylElt τ K j 1).prod =
      k * canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) := by
  induction ω with
  | nil =>
    exact ⟨1, one_mem _, by
      rw [List.map_nil, List.prod_nil, CoxeterSystem.wordProd_nil, canonicalRep_one, one_mul]⟩
  | cons j ω ih =>
    obtain ⟨k, hk, he⟩ := ih
    obtain ⟨k', hk', he'⟩ := canonicalRep_mul_mem (R := K) ((coxeterSystem τ).simple j)
      ((coxeterSystem τ).wordProd ω)
    have hconj : weylElt τ K j 1 * k * (weylElt τ K j 1)⁻¹ ∈ torusGroup τ K :=
      (Subgroup.mem_normalizer_iff.1 (weylElt_mem_normalizer_torus τ K j 1) k).1 hk
    refine ⟨weylElt τ K j 1 * k * (weylElt τ K j 1)⁻¹ * k', mul_mem hconj hk', ?_⟩
    rw [List.map_cons, List.prod_cons, he, (coxeterSystem τ).wordProd_cons, mul_assoc _ k',
      ← he', canonicalRep_simple]
    group


theorem classDescent_coeff_eq_zero_of_mem_rootSpan {τ : Tag} {T : Set (Fin τ.rank → ℤ)}
    (hT : ∀ β ∈ T, IsRoot τ β ∧ 0 < height β)
    (habs : ∀ α, IsRoot τ α ∧ 0 < height α → ∀ β ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) → a • α + b • β ∈ T)
    {L : List (Fin τ.rank → ℤ)} (hnd : L.Nodup) (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 < height α)
    (c : (Fin τ.rank → ℤ) → K)
    (hmem : (L.map fun α => pinnedX τ K α (c α)).prod ∈ rootSpan τ K T) :
    ∀ α ∈ L, α ∉ T → c α = 0 := by
  classical
  have hN : ∀ g ∈ posUnipotent τ K, ∀ u ∈ rootSpan τ K T, g * u * g⁻¹ ∈ rootSpan τ K T := by
    obtain ⟨hle, hnorm⟩ := positive_root_ideal_normality τ K (J := T)
      (S := {α | IsRoot τ α ∧ 0 < height α}) (fun α hα => hT α hα) (fun α hα => hα)
      (fun α hα β hβ a b ha hb hr => habs α hα β hβ a b ha hb hr)
    have hnz := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnorm
    intro g hg u hu
    exact (Subgroup.mem_normalizer_iff.1 (hnz hg) u).1 hu
  have hxT : ∀ β ∈ T, ∀ d : K, pinnedX τ K β d ∈ rootSpan τ K T := fun β hβ d =>
    (le_iSup₂_of_le β hβ le_rfl : rootSubgroup τ K β ≤ rootSpan τ K T)
      (Subgroup.subset_closure ⟨d, rfl⟩)
  have hsplit : ∀ L : List (Fin τ.rank → ℤ), (∀ α ∈ L, IsRoot τ α ∧ 0 < height α) →
      ∃ u ∈ rootSpan τ K T, (L.map fun α => pinnedX τ K α (c α)).prod =
        ((L.filter fun α => α ∉ T).map fun α => pinnedX τ K α (c α)).prod * u := by
    intro L hL
    induction L with
    | nil => exact ⟨1, one_mem _, by simp⟩
    | cons α L ih =>
      obtain ⟨u, hu, he⟩ := ih fun β hβ => hL β (List.mem_cons_of_mem _ hβ)
      set P₁ := ((L.filter fun α => α ∉ T).map fun α => pinnedX τ K α (c α)).prod with hP₁
      by_cases hαT : α ∈ T
      · have hP₁U : P₁ ∈ posUnipotent τ K := pinnedX_list_prod_mem_posUnipotent _
          (fun β hβ => hL β (List.mem_cons_of_mem _ (List.mem_of_mem_filter hβ))) c
        refine ⟨P₁⁻¹ * pinnedX τ K α (c α) * P₁ * u, mul_mem ?_ hu, ?_⟩
        · simpa using hN P₁⁻¹ (inv_mem hP₁U) _ (hxT α hαT (c α))
        · rw [List.map_cons, List.prod_cons, he,
            List.filter_cons_of_neg (by simpa using hαT), ← hP₁]
          group
      · refine ⟨u, hu, ?_⟩
        rw [List.map_cons, List.prod_cons, he, List.filter_cons_of_pos (by simpa using hαT),
          List.map_cons, List.prod_cons, mul_assoc]
  obtain ⟨u, hu, he⟩ := hsplit L hL
  set L₁ := L.filter fun α => α ∉ T with hL₁def
  have hP₁ : (L₁.map fun α => pinnedX τ K α (c α)).prod ∈ rootSpan τ K T := by
    have h := mul_mem hmem (inv_mem hu)
    rwa [he, mul_inv_cancel_right] at h
  have hTc : ∀ α ∈ T, ∀ β ∈ T, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ T := fun α hα β hβ a b ha hb hr => habs α (hT α hα) β hβ a b ha hb hr
  obtain ⟨k, γ, hγ⟩ := ((finite_setOf_isRoot τ).subset fun β hβ => (hT β hβ).1).fin_embedding
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K hT hTc γ γ.injective hγ).surjOn hP₁
  set d' : (Fin τ.rank → ℤ) → K := Function.extend γ d 0 with hd'
  set LT := List.ofFn γ with hLTdef
  have hdT : (LT.map fun β => pinnedX τ K β (d' β)).prod =
      (L₁.map fun α => pinnedX τ K α (c α)).prod := by
    rw [← hd]
    simp only [hLTdef, List.map_ofFn, Function.comp_def, hd', γ.injective.extend_apply]
  have hL₁T : ∀ β ∈ L₁, β ∉ T := fun β hβ => by simpa using (List.mem_filter.1 hβ).2
  have hLTT : ∀ β ∈ LT, β ∈ T := fun β hβ => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hβ
    exact hγ ▸ Set.mem_range_self i
  have hnd' : (L₁ ++ LT).Nodup := List.nodup_append.2 ⟨hnd.filter _,
    List.nodup_ofFn.2 γ.injective, fun a ha b hb hab => hL₁T a ha (hab ▸ hLTT b hb)⟩
  have hpos' : ∀ β ∈ L₁ ++ LT, IsRoot τ β ∧ 0 < height β := fun β hβ => by
    rcases List.mem_append.1 hβ with h | h
    · exact hL β (List.mem_of_mem_filter h)
    · exact hT β (hLTT β h)
  set c₁ : (Fin τ.rank → ℤ) → K := fun β => if β ∈ T then 0 else c β with hc₁
  set c₂ : (Fin τ.rank → ℤ) → K := fun β => if β ∈ T then d' β else 0 with hc₂
  have e₁ : ((L₁ ++ LT).map fun β => pinnedX τ K β (c₁ β)).prod =
      (L₁.map fun α => pinnedX τ K α (c α)).prod := by
    rw [List.map_append, List.prod_append]
    have h1 : (L₁.map fun β => pinnedX τ K β (c₁ β)) = L₁.map fun β => pinnedX τ K β (c β) :=
      List.map_congr_left fun β hβ => by simp [hc₁, hL₁T β hβ]
    have h2 : (LT.map fun β => pinnedX τ K β (c₁ β)).prod = 1 := List.prod_eq_one fun x hx => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      simp [hc₁, hLTT β hβ, pinnedX_zero]
    rw [h1, h2, mul_one]
  have e₂ : ((L₁ ++ LT).map fun β => pinnedX τ K β (c₂ β)).prod =
      (LT.map fun β => pinnedX τ K β (d' β)).prod := by
    rw [List.map_append, List.prod_append]
    have h1 : (L₁.map fun β => pinnedX τ K β (c₂ β)).prod = 1 := List.prod_eq_one fun x hx => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.1 hx
      simp [hc₂, hL₁T β hβ, pinnedX_zero]
    have h2 : (LT.map fun β => pinnedX τ K β (c₂ β)) = LT.map fun β => pinnedX τ K β (d' β) :=
      List.map_congr_left fun β hβ => by simp [hc₂, hLTT β hβ]
    rw [h1, h2, one_mul]
  have hinj := pinnedX_list_prod_injective (L₁ ++ LT) hnd' hpos' c₁ c₂
    (e₁.trans (hdT.symm.trans e₂.symm))
  intro α hα hαT
  have h := hinj α (List.mem_append_left _ (List.mem_filter.2 ⟨hα, by simpa using hαT⟩))
  simpa [hc₁, hc₂, hαT] using h

theorem classDescent_list_prod_not_mem_rootSpan_ne_single {τ : Tag} {i : Fin τ.rank}
    {L : List (Fin τ.rank → ℤ)} (hnd : L.Nodup) (hL : ∀ α ∈ L, IsRoot τ α ∧ 0 < height α)
    {c : (Fin τ.rank → ℤ) → K} (hi : Pi.single i 1 ∈ L) (hc : c (Pi.single i 1) ≠ 0) :
    (L.map fun α => pinnedX τ K α (c α)).prod ∉
      rootSpan τ K {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1} := by
  intro hmem
  refine hc (classDescent_coeff_eq_zero_of_mem_rootSpan (fun β hβ => ⟨hβ.1, hβ.2.1⟩)
    (fun α hα β hβ a b ha hb hr => ?_) hnd hL c hmem _ hi fun h => h.2.2 rfl)
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hht : height (a • α + b • β) = a * height α + b * height β := height_nsmul_add_nsmul a b α β
  have h2 : 2 ≤ height (a • α + b • β) := by rw [hht]; nlinarith [hα.2, hβ.2.1]
  refine ⟨hr, by omega, fun h => ?_⟩
  rw [h, height_single] at h2
  omega

theorem classDescent_exists_list_of_mem {τ : Tag} {J : Set (Fin τ.rank)} {t : ModGL τ K}
    (ht : t ∈ rootSpan τ K (parabolicPosRoots τ J)) :
    ∃ (L : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → K), L.Nodup ∧
      (∀ α ∈ L, α ∈ parabolicPosRoots τ J ∧ c α ≠ 0) ∧
      t = (L.map fun α => pinnedX τ K α (c α)).prod := by
  classical
  have hS : ∀ α ∈ parabolicPosRoots τ J, IsRoot τ α ∧ 0 < height α := fun α hα => hα.2
  obtain ⟨k, γ, hγ⟩ := ((finite_setOf_isRoot τ).subset fun β hβ => (hS β hβ).1).fin_embedding
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K hS (classDescent_parabolicPosRoots_closed J) γ
    γ.injective hγ).surjOn ht
  set d' : (Fin τ.rank → ℤ) → K := Function.extend γ d 0 with hd'
  refine ⟨(List.ofFn γ).filter fun α => d' α ≠ 0, d',
    (List.nodup_ofFn.2 γ.injective).filter _, fun α hα => ?_, ?_⟩
  · obtain ⟨hα1, hα2⟩ := List.mem_filter.1 hα
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hα1
    exact ⟨hγ ▸ Set.mem_range_self i, by simpa using hα2⟩
  · rw [classDescent_prod_map_filter _ _ _ fun α _ h => by
      rw [show d' α = 0 by simpa using h, pinnedX_zero], ← hd, List.map_ofFn]
    simp only [Function.comp_def, hd', γ.injective.extend_apply]

theorem classDescent_exists_sign_conj_list_prod {τ : Tag} (j : Fin τ.rank) :
    ∃ η : (Fin τ.rank → ℤ) → K, (∀ α, IsRoot τ α → η α * η α = 1) ∧
      ∀ (c : (Fin τ.rank → ℤ) → K) (L : List (Fin τ.rank → ℤ)), (∀ α ∈ L, IsRoot τ α) →
        weylElt τ K j 1 * (L.map fun α => pinnedX τ K α (c α)).prod * (weylElt τ K j 1)⁻¹ =
          (L.map fun α => pinnedX τ K (reflect τ j α) (η α * c α)).prod := by
  classical
  have h : ∀ α : Fin τ.rank → ℤ, ∃ ε : K, IsRoot τ α → ε * ε = 1 ∧ ∀ c : K,
      weylElt τ K j 1 * pinnedX τ K α c * (weylElt τ K j 1)⁻¹ =
        pinnedX τ K (reflect τ j α) (ε * c) := by
    intro α
    by_cases hα : IsRoot τ α
    · obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K j hα
      exact ⟨ε, fun _ => ⟨hε, h⟩⟩
    · exact ⟨1, fun h' => absurd h' hα⟩
  choose η hη using h
  refine ⟨η, fun α hα => (hη α hα).1, fun c L hL => ?_⟩
  induction L with
  | nil => simp
  | cons α L ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
      ← (hη α (hL α List.mem_cons_self)).2 (c α), ← ih fun β hβ => hL β (List.mem_cons_of_mem _ hβ)]
    group

theorem classDescent_exists_word_list {τ : Tag} (J : Set (Fin τ.rank)) (n : ℕ) :
    ∀ (L : List (Fin τ.rank → ℤ)) (c : (Fin τ.rank → ℤ) → K), L.Nodup →
      (∀ α ∈ L, α ∈ parabolicPosRoots τ J ∧ c α ≠ 0) → (∃ α ∈ L, height α ≤ n) →
      ∃ ω : List (Fin τ.rank), (∀ j ∈ ω, j ∈ J) ∧
        ∃ (L' : List (Fin τ.rank → ℤ)) (c' : (Fin τ.rank → ℤ) → K), L'.Nodup ∧
          (∀ α ∈ L', α ∈ parabolicPosRoots τ J ∧ c' α ≠ 0) ∧ (∃ i ∈ J, Pi.single i 1 ∈ L') ∧
          (ω.map fun j => weylElt τ K j 1).prod * (L.map fun α => pinnedX τ K α (c α)).prod *
              ((ω.map fun j => weylElt τ K j 1).prod)⁻¹ =
            (L'.map fun α => pinnedX τ K α (c' α)).prod := by
  induction n with
  | zero =>
    rintro L c - hL ⟨α, hα, hle⟩
    have := (hL α hα).1.2.2
    push_cast at hle
    omega
  | succ n ih =>
    rintro L c hnd hL ⟨α₀, hα₀, hle⟩
    by_cases hlow : ∃ α ∈ L, height α ≤ n
    · exact ih L c hnd hL hlow
    push Not at hlow
    have hα₀h : height α₀ = n + 1 := by have := hlow α₀ hα₀; push_cast at hle ⊢; omega
    obtain ⟨⟨hα₀r, hα₀s⟩, -, hα₀p⟩ := (hL α₀ hα₀).1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      obtain ⟨i, hi⟩ := classDescent_eq_single_of_height_eq_one hα₀r (by simpa using hα₀h)
      have hiJ : i ∈ J := by
        by_contra hiJ
        have := hα₀s i hiJ
        rw [hi, Pi.single_eq_same] at this
        exact one_ne_zero this
      exact ⟨[], by simp, L, c, hnd, hL, ⟨i, hiJ, hi ▸ hα₀⟩, by simp⟩
    ·
      have hnn := (IsRoot.height_pos_iff hα₀r).1 hα₀p
      obtain ⟨j, hj0, hjc⟩ := exists_cartan_pos hα₀r.ne_zero hnn
      have hjJ : j ∈ J := by
        by_contra hjJ
        have := hα₀s j hjJ
        omega
      have hht : height (reflect τ j α₀) = height α₀ - ∑ l, τ.cartan j l * α₀ l := by
        simp only [height, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_sub_distrib]
        simp [Pi.single_apply]
      have hne : ∀ α ∈ L, α ≠ Pi.single j 1 := fun α hα h => by
        have := hlow α hα
        rw [h, height_single] at this
        omega
      obtain ⟨η, hη1, hηc⟩ := classDescent_exists_sign_conj_list_prod (K := K) j
      set c₂ : (Fin τ.rank → ℤ) → K := fun β => η (reflect τ j β) * c (reflect τ j β) with hc₂
      have hinj : Function.Injective (reflect τ j) :=
        Function.LeftInverse.injective (g := reflect τ j) fun v => reflect_reflect τ j v
      have hL₂ : ∀ β ∈ L.map (reflect τ j), β ∈ parabolicPosRoots τ J ∧ c₂ β ≠ 0 := by
        intro β hβ
        obtain ⟨α, hα, rfl⟩ := List.mem_map.1 hβ
        obtain ⟨⟨hαr, hαs⟩, -, hαp⟩ := (hL α hα).1
        refine ⟨⟨⟨IsRoot.reflect j hαr, fun l hl => ?_⟩, IsRoot.reflect j hαr,
          height_reflect_pos hαr hαp (hne α hα)⟩, ?_⟩
        · rw [reflect_apply_of_ne j (by rintro rfl; exact hl hjJ)]
          exact hαs l hl
        · simp only [hc₂, reflect_reflect]
          refine mul_ne_zero (fun h => ?_) (hL α hα).2
          have := hη1 α hαr
          rw [h, zero_mul] at this
          exact zero_ne_one this
      have hlow₂ : ∃ β ∈ L.map (reflect τ j), height β ≤ (n : ℤ) :=
        ⟨reflect τ j α₀, List.mem_map_of_mem hα₀, by omega⟩
      obtain ⟨ω, hωJ, L', c', hnd', hL', hsimple, hconj⟩ :=
        ih _ c₂ (hnd.map hinj) hL₂ hlow₂
      refine ⟨ω ++ [j], fun j' hj' => ?_, L', c', hnd', hL', hsimple, ?_⟩
      · rcases List.mem_append.1 hj' with h | h
        · exact hωJ j' h
        · rw [List.mem_singleton.1 h]
          exact hjJ
      · have htr := hηc c L fun α hα => (hL α hα).1.1.1
        have e : ((L.map (reflect τ j)).map fun β => pinnedX τ K β (c₂ β)) =
            L.map fun α => pinnedX τ K (reflect τ j α) (η α * c α) := by
          rw [List.map_map]
          refine List.map_congr_left fun α _ => ?_
          simp [hc₂, reflect_reflect]
        rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, ← hconj,
          e, ← htr]
        group

theorem exists_prod_weylElt_conj_not_mem_simpleRadical {τ : Tag} (J : Set (Fin τ.rank))
    {t : ModGL τ K} (ht : t ∈ rootSpan τ K (parabolicPosRoots τ J)) (ht1 : t ≠ 1) :
    ∃ ω : List (Fin τ.rank), (∀ j ∈ ω, j ∈ J) ∧ ∃ i ∈ J,
      (ω.map fun j => weylElt τ K j 1).prod * t * ((ω.map fun j => weylElt τ K j 1).prod)⁻¹ ∈
        rootSpan τ K (parabolicPosRoots τ J) ∧
      (ω.map fun j => weylElt τ K j 1).prod * t * ((ω.map fun j => weylElt τ K j 1).prod)⁻¹ ∉
        rootSpan τ K {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1} := by
  obtain ⟨L, c, hnd, hL, rfl⟩ := classDescent_exists_list_of_mem ht
  obtain ⟨α, hα⟩ : ∃ α, α ∈ L := by
    cases L with
    | nil => exact absurd (by simp) ht1
    | cons α L => exact ⟨α, List.mem_cons_self⟩
  obtain ⟨ω, hωJ, L', c', hnd', hL', ⟨i, hiJ, hi⟩, hconj⟩ :=
    classDescent_exists_word_list (K := K) J (height α).toNat L c hnd hL
      ⟨α, hα, Int.self_le_toNat _⟩
  refine ⟨ω, hωJ, i, hiJ, ?_, ?_⟩
  · rw [hconj]
    exact classDescent_list_prod_mem_rootSpan L' (fun β hβ => (hL' β hβ).1) c'
  · rw [hconj]
    exact classDescent_list_prod_not_mem_rootSpan_ne_single hnd' (fun β hβ => (hL' β hβ).1.2) hi
      (hL' _ hi).2

theorem exists_canonicalRep_conj_not_mem_rootSpan_ne_single {τ : Tag} (J : Set (Fin τ.rank))
    {t : ModGL τ K} (ht : t ∈ rootSpan τ K (parabolicPosRoots τ J)) (ht1 : t ≠ 1) :
    ∃ w ∈ Subgroup.closure ((simple τ) '' J), ∃ i ∈ J,
      canonicalRep (coxeterSystem τ) K w * t * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
        rootSpan τ K (parabolicPosRoots τ J) ∧
      canonicalRep (coxeterSystem τ) K w * t * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∉
        rootSpan τ K {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1} := by
  obtain ⟨ω, hωJ, i, hiJ, hmem, hnot⟩ := exists_prod_weylElt_conj_not_mem_simpleRadical J ht ht1
  obtain ⟨k, hk, he⟩ := classDescent_prod_weylElt_eq_mul_canonicalRep (K := K) ω
  set P := (ω.map fun j => weylElt τ K j 1).prod with hP
  set n := canonicalRep (coxeterSystem τ) K ((coxeterSystem τ).wordProd ω) with hn
  have hconj : n * t * n⁻¹ = k⁻¹ * (P * t * P⁻¹) * k := by rw [he]; group
  have hT1 := torusGroup_le_normalizer_rootSpan (K := K) (S := parabolicPosRoots τ J)
    fun α hα => hα.2.1
  have hT2 := torusGroup_le_normalizer_rootSpan (K := K)
    (S := {α | IsRoot τ α ∧ 0 < height α ∧ α ≠ Pi.single i 1}) fun α hα => hα.1
  refine ⟨(coxeterSystem τ).wordProd ω, classDescent_wordProd_mem_closure hωJ, i, hiJ, ?_, ?_⟩
  · rw [hconj]
    simpa using (Subgroup.mem_normalizer_iff.1 (hT1 (inv_mem hk)) _).1 hmem
  · rw [hconj]
    intro hcon
    refine hnot ?_
    have h := (Subgroup.mem_normalizer_iff.1 (hT2 hk) _).1 hcon
    simpa [mul_assoc] using h

theorem exists_canonicalRep_conj_not_mem_simpleRadical {τ : Tag} (J : Set (Fin τ.rank))
    {t : ModGL τ K} (ht : t ∈ rootSpan τ K (parabolicPosRoots τ J)) (ht1 : t ≠ 1) :
    ∃ w ∈ Subgroup.closure ((simple τ) '' J), ∃ i ∈ J,
      canonicalRep (coxeterSystem τ) K w * t * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
        rootSpan τ K (parabolicPosRoots τ J) ∧
      canonicalRep (coxeterSystem τ) K w * t * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∉
        rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}) := by
  obtain ⟨w, hw, i, hiJ, hmem, hnot⟩ := exists_canonicalRep_conj_not_mem_rootSpan_ne_single J ht ht1
  refine ⟨w, hw, i, hiJ, hmem, fun h => hnot (classDescent_rootSpan_mono ?_ h)⟩
  rintro α ⟨hα, hαi⟩
  exact ⟨hα.2.1, hα.2.2, hαi⟩

theorem classDescent_exists_pinnedX_mul {τ : Tag} {J : Set (Fin τ.rank)} {i : Fin τ.rank}
    (hi : i ∈ J) {x : ModGL τ K} (hx : x ∈ rootSpan τ K (parabolicPosRoots τ J)) :
    ∃ c : K, ∃ u ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
      x = pinnedX τ K (Pi.single i 1) c * u := by
  have hiS : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicPosRoots τ J :=
    ⟨⟨isRoot_single τ i, fun l hl => Pi.single_eq_of_ne (by rintro rfl; exact hl hi) 1⟩,
      isRoot_single τ i, by rw [height_single]; exact one_pos⟩
  have hS : ∀ α ∈ parabolicPosRoots τ J, IsRoot τ α ∧ 0 < height α := fun α hα => hα.2
  obtain ⟨k, γ, hγ⟩ := ((finite_setOf_isRoot τ).subset
    fun β (hβ : β ∈ parabolicPosRoots τ J \ {Pi.single i 1}) => (hS β hβ.1).1).fin_embedding
  set β : Fin (k + 1) → Fin τ.rank → ℤ := Fin.cons (Pi.single i 1) γ with hβ
  have hβinj : Function.Injective β := Fin.cons_injective_iff.2
    ⟨fun h => by
      rw [hγ] at h
      exact h.2 rfl, γ.injective⟩
  have hβrange : Set.range β = parabolicPosRoots τ J := by
    rw [hβ, Fin.range_cons, hγ, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hiS]
  obtain ⟨d, -, hd⟩ := (bijOn_prod_pinnedX K hS (classDescent_parabolicPosRoots_closed J) β hβinj
    hβrange).surjOn hx
  refine ⟨d 0, (List.ofFn fun l => pinnedX τ K (γ l) (d l.succ)).prod, ?_, ?_⟩
  · refine list_prod_mem fun y hy => ?_
    obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hy
    have hl : γ l ∈ parabolicPosRoots τ J \ {Pi.single i 1} := hγ ▸ Set.mem_range_self l
    exact (le_iSup₂_of_le (γ l) hl le_rfl : rootSubgroup τ K (γ l) ≤ _)
      (Subgroup.subset_closure ⟨d l.succ, rfl⟩)
  · rw [← hd]
    simp only [List.ofFn_succ, List.prod_cons, hβ, Fin.cons_zero, Fin.cons_succ]

theorem exists_canonicalRep_conj_eq_pinnedX_simple_mul {τ : Tag} (J : Set (Fin τ.rank))
    {t : ModGL τ K} (ht : t ∈ rootSpan τ K (parabolicPosRoots τ J)) (ht1 : t ≠ 1) :
    ∃ w ∈ Subgroup.closure ((simple τ) '' J), ∃ i ∈ J, ∃ c : K, c ≠ 0 ∧
      ∃ u ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
        canonicalRep (coxeterSystem τ) K w * t * (canonicalRep (coxeterSystem τ) K w)⁻¹ =
          pinnedX τ K (Pi.single i 1) c * u := by
  obtain ⟨w, hw, i, hiJ, hmem, hnot⟩ := exists_canonicalRep_conj_not_mem_simpleRadical J ht ht1
  obtain ⟨c, u, hu, he⟩ := classDescent_exists_pinnedX_mul hiJ hmem
  refine ⟨w, hw, i, hiJ, c, fun hc => hnot ?_, u, hu, he⟩
  rw [he, hc, pinnedX_zero, one_mul]
  exact hu

theorem exists_prod_weylElt_conj_eq_pinnedX_simple_mul {τ : Tag} (J : Set (Fin τ.rank))
    {t : ModGL τ K} (ht : t ∈ rootSpan τ K (parabolicPosRoots τ J)) (ht1 : t ≠ 1) :
    ∃ ω : List (Fin τ.rank), (∀ j ∈ ω, j ∈ J) ∧ ∃ i ∈ J, ∃ c : K, c ≠ 0 ∧
      ∃ u ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
        (ω.map fun j => weylElt τ K j 1).prod * t * ((ω.map fun j => weylElt τ K j 1).prod)⁻¹ =
          pinnedX τ K (Pi.single i 1) c * u := by
  obtain ⟨ω, hωJ, i, hiJ, hmem, hnot⟩ := exists_prod_weylElt_conj_not_mem_simpleRadical J ht ht1
  obtain ⟨c, u, hu, he⟩ := classDescent_exists_pinnedX_mul hiJ hmem
  refine ⟨ω, hωJ, i, hiJ, c, fun hc => hnot ?_, u, hu, he⟩
  rw [he, hc, pinnedX_zero, one_mul]
  refine classDescent_rootSpan_mono ?_ hu
  rintro α ⟨hα, hαi⟩
  exact ⟨hα.2.1, hα.2.2, hαi⟩

theorem exists_mem_parabolicLevi_conj_eq_pinnedX_simple_mul {τ : Tag} (J : Set (Fin τ.rank))
    {t : ModGL τ K} (ht : t ∈ rootSpan τ K (parabolicPosRoots τ J)) (ht1 : t ≠ 1) :
    ∃ g ∈ parabolicLevi τ K J, ∃ i ∈ J, ∃ c : K, c ≠ 0 ∧
      ∃ u ∈ rootSpan τ K (parabolicPosRoots τ J \ {Pi.single i 1}),
        g * t * g⁻¹ = pinnedX τ K (Pi.single i 1) c * u := by
  obtain ⟨w, hw, i, hiJ, c, hc, u, hu, he⟩ :=
    exists_canonicalRep_conj_eq_pinnedX_simple_mul J ht ht1
  exact ⟨_, canonicalRep_mem_parabolicLevi hw, i, hiJ, c, hc, u, hu, he⟩

end CFSG.SeitzReduction
