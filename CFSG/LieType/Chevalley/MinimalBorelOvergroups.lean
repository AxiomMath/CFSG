module

public import CFSG.LieType.Chevalley.BorelOvergroups
public import CFSG.LieType.Chevalley.RankOneBruhat
public import CFSG.LieType.Chevalley.RankOneCentralImage
public import CFSG.LieType.Chevalley.OppositeBorel
public import CFSG.LieType.Chevalley.ParabolicWeylStabilizer

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def oppositeBorel
    : Subgroup (ModGL τ K) :=
  torusGroup τ K ⊔ negUnipotent τ K

variable (τ K) in
@[expose] def oppositeMinimalParabolic
    (i : Fin τ.rank) : Subgroup (ModGL τ K) :=
  oppositeBorel τ K ⊔ Subgroup.closure (Set.range (xUnit τ K i))

theorem parabolicSubgroup_le_parabolicSubgroup_iff
    {J J' : Set (Fin τ.rank)} :
    parabolicSubgroup τ K J ≤ parabolicSubgroup τ K J' ↔ J ⊆ J' :=
  (standard_parabolic_cells τ K).2.2.2.1 J J'

theorem parabolicSubgroup_injective
    : Function.Injective (parabolicSubgroup τ K) :=
  fun _ _ h => Set.Subset.antisymm (parabolicSubgroup_le_parabolicSubgroup_iff.1 h.le)
    (parabolicSubgroup_le_parabolicSubgroup_iff.1 h.ge)

theorem parabolicSubgroup_empty
    : parabolicSubgroup τ K ∅ = borelGroup τ K :=
  (standard_parabolic_cells τ K).2.2.2.2.1

theorem borelGroup_lt_parabolicSubgroup
    {J : Set (Fin τ.rank)} (hJ : J.Nonempty) :
    borelGroup τ K < parabolicSubgroup τ K J := by
  refine lt_of_le_of_ne (borelGroup_le_parabolicSubgroup J) fun h => ?_
  rw [← parabolicSubgroup_empty] at h
  exact hJ.ne_empty (parabolicSubgroup_injective h).symm

theorem nonempty_of_borelGroup_lt
    {J : Set (Fin τ.rank)}
    (h : borelGroup τ K < parabolicSubgroup τ K J) : J.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [parabolicSubgroup_empty] at h
  exact lt_irrefl _ h

theorem borelGroup_covBy_iff
    {A : Subgroup (ModGL τ K)} (hA : A ≤ adjointGroup τ K) :
    borelGroup τ K ⋖ A ↔ ∃ i, A = parabolicSubgroup τ K {i} := by
  have hclass := (borel_overgroup_classification τ K).2
  constructor
  · rintro ⟨hlt, hmin⟩
    obtain ⟨J, hJ, -⟩ := hclass A hlt.le hA
    obtain ⟨i, hi⟩ := nonempty_of_borelGroup_lt (hJ ▸ hlt)
    refine ⟨i, ?_⟩
    have hle : parabolicSubgroup τ K {i} ≤ A := hJ ▸
      parabolicSubgroup_le_parabolicSubgroup_iff.2 (Set.singleton_subset_iff.2 hi)
    by_contra hne
    exact hmin (borelGroup_lt_parabolicSubgroup (Set.singleton_nonempty i))
      (lt_of_le_of_ne hle fun h => hne h.symm)
  · rintro ⟨i, rfl⟩
    refine ⟨borelGroup_lt_parabolicSubgroup (Set.singleton_nonempty i), fun A' hBA' hA'P => ?_⟩
    obtain ⟨J', hJ', -⟩ := hclass A' hBA'.le (hA'P.le.trans hA)
    have hsub : J' ⊆ {i} := parabolicSubgroup_le_parabolicSubgroup_iff.1 (hJ' ▸ hA'P.le)
    obtain ⟨j, hj⟩ := nonempty_of_borelGroup_lt (hJ' ▸ hBA')
    have hJ'i : J' = {i} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.2 (by
      have := hsub hj
      rw [Set.mem_singleton_iff] at this
      exact this ▸ hj))
    rw [hJ', hJ'i] at hA'P
    exact lt_irrefl _ hA'P

theorem coe_rootSubgroup_single
    (i : Fin τ.rank) :
    (rootSubgroup τ K (Pi.single i 1) : Set (ModGL τ K)) = Set.range (xUnit τ K i) := by
  ext g
  rw [SetLike.mem_coe, mem_rootSubgroup]
  simp only [pinnedX_single, Set.mem_range]

theorem coe_rootSubgroup_neg_single
    (i : Fin τ.rank) :
    (rootSubgroup τ K (-Pi.single i 1) : Set (ModGL τ K)) = Set.range (yUnit τ K i) := by
  ext g
  rw [SetLike.mem_coe, mem_rootSubgroup]
  simp only [pinnedX_neg_single, Set.mem_range]

theorem rootSubgroup_single_eq_closure
    (i : Fin τ.rank) :
    rootSubgroup τ K (Pi.single i 1) = Subgroup.closure (Set.range (xUnit τ K i)) := by
  rw [rootSubgroup]
  congr 1
  ext g
  simp only [Set.mem_range, pinnedX_single]

theorem mem_parabolicWeylGroup_singleton
    {i : Fin τ.rank} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ {i}) : w = 1 ∨ w = simple τ i := by
  rw [parabolicWeylGroup, Set.image_singleton] at hw
  obtain ⟨n, rfl⟩ := Subgroup.mem_closure_singleton.1 hw
  have hsq : simple τ i * simple τ i = 1 := (coxeterSystem τ).simple_mul_simple_self i
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_two, hsq, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hsq, one_zpow, one_mul, zpow_one]

theorem inversionSet_simple
    (i : Fin τ.rank) :
    inversionSet (simple τ i) = {Pi.single i 1} := by
  have h := (inversionSet_mul_simple (w := 1) (i := i) (by
    rw [one_mul, (coxeterSystem τ).length_one, zero_add]
    exact (coxeterSystem τ).length_simple i)).1
  rw [one_mul, inversionSet_one, Set.image_empty, insert_empty_eq] at h
  exact h

theorem rootSpan_singleton
    (α : Fin τ.rank → ℤ) :
    rootSpan τ K {α} = rootSubgroup τ K α := by
  rw [rootSpan, iSup_singleton]

theorem mul_weylElt_not_mem_negUnipotent
    (i : Fin τ.rank) {b : ModGL τ K}
    (hb : b ∈ borelGroup τ K) : b * weylElt τ K i 1 ∉ negUnipotent τ K := by
  intro hv
  have hl := isLowerUnitriangular_of_mem (negUnipotent_le_posFiltration τ K hv)
  have hu := ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2).1 b hb
  have hneg : IsRoot τ (-Pi.single i 1) := IsRoot.neg (isRoot_single τ i)
  set b₀ : Label τ := .inr ⟨-Pi.single i 1, hneg⟩
  set b₁ : Label τ := .inr ⟨Pi.single i 1, isRoot_single τ i⟩
  have h1 := hl.1 b₀
  have hn : (weylElt τ K i 1 : Module.End K (RootModule τ K)) (Finsupp.single b₀ 1) =
      Finsupp.single b₁ 1 := by
    have h := weylElt_rootVec_neg_single (τ := τ) (R := K) i 1
    rw [rootVec_eq_single_of_isRoot hneg, rootVec_eq_single_of_isRoot (isRoot_single τ i),
      Units.val_one, one_pow, one_smul] at h
    exact h
  have hprec : b₁.Precedes b₀ := by
    left
    change height (-Pi.single i 1 : Fin τ.rank → ℤ) < height (Pi.single i 1 : Fin τ.rank → ℤ)
    rw [height_neg, height_single]
    omega
  rw [Units.val_mul, Module.End.mul_apply, hn, hu b₀ b₁ hprec] at h1
  exact zero_ne_one h1

theorem yUnit_mem_parabolicSubgroup
    (i : Fin τ.rank) (c : K) :
    yUnit τ K i c ∈ parabolicSubgroup τ K {i} := by
  rw [yUnit_eq_conj]
  have hn := weylElt_mem_parabolicSubgroup (K := K) (Set.mem_singleton i)
  exact mul_mem (mul_mem hn (borelGroup_le_parabolicSubgroup _ (xUnit_mem_borelGroup i _)))
    (inv_mem hn)

theorem parabolicSubgroup_singleton_inf_negUnipotent
    (i : Fin τ.rank) :
    parabolicSubgroup τ K {i} ⊓ negUnipotent τ K = rootSubgroup τ K (-Pi.single i 1) := by
  refine le_antisymm (fun v hv => ?_) fun v hv => ?_
  · obtain ⟨hvP, hvV⟩ := Subgroup.mem_inf.1 hv
    rw [← SetLike.mem_coe, coe_rootSubgroup_neg_single]
    have hvP' : v ∈ (parabolicSubgroup τ K {i} : Set (ModGL τ K)) := hvP
    rw [(standard_parabolic_cells τ K).1] at hvP'
    obtain ⟨w, hw, hvw⟩ := Set.mem_iUnion₂.1 hvP'
    rcases mem_parabolicWeylGroup_singleton hw with rfl | rfl
    ·
      obtain ⟨b, hb, b', hb', hbb⟩ := mem_bruhatCell.1 hvw
      rw [canonicalRep_one, mul_one] at hbb
      have hvB : v ∈ borelGroup τ K := hbb ▸ mul_mem hb hb'
      have : v ∈ borelGroup τ K ⊓ negUnipotent τ K := Subgroup.mem_inf.2 ⟨hvB, hvV⟩
      rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at this
      exact ⟨0, by rw [yUnit_zero, this]⟩
    ·
      obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, rfl⟩ := (bijOn_bruhatCell (K := K) (simple τ i)).surjOn hvw
      rw [inversionSet_simple, rootSpan_singleton, coe_rootSubgroup_single] at hu
      obtain ⟨c, rfl⟩ := hu
      simp only [canonicalRep_simple] at hvV ⊢
      by_cases hc : c = 0
      · rw [hc, xUnit_zero, mul_one] at hvV
        exact absurd hvV (mul_weylElt_not_mem_negUnipotent i hb)
      · obtain ⟨b', hb', hb'eq⟩ := (simple_rank_one_bruhat_identity τ K).2 K i c hc
        rw [mul_assoc, hb'eq, ← mul_assoc] at hvV ⊢
        have hbb : b * b' ∈ borelGroup τ K ⊓ negUnipotent τ K := by
          refine Subgroup.mem_inf.2 ⟨mul_mem hb hb', ?_⟩
          have := mul_mem hvV (inv_mem (yUnit_mem_negUnipotent (K := K) i c⁻¹))
          rwa [mul_inv_cancel_right] at this
        rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hbb
        exact ⟨c⁻¹, by rw [hbb, one_mul]⟩
  · rw [← SetLike.mem_coe, coe_rootSubgroup_neg_single] at hv
    obtain ⟨c, rfl⟩ := hv
    exact Subgroup.mem_inf.2 ⟨yUnit_mem_parabolicSubgroup i c, yUnit_mem_negUnipotent i c⟩

theorem parabolicSubgroup_singleton_eq
    (i : Fin τ.rank) :
    parabolicSubgroup τ K {i} = borelGroup τ K ⊔ rootSubgroup τ K (-Pi.single i 1) := by
  refine le_antisymm (sup_le le_sup_left ((Subgroup.closure_le _).2 ?_))
    (sup_le (borelGroup_le_parabolicSubgroup _) ?_)
  · rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff] at hj
    subst hj
    change weylElt τ K j 1 ∈ _
    rw [weylElt_eq_yUnit_mul]
    have hy : yUnit τ K j (-1) ∈ borelGroup τ K ⊔ rootSubgroup τ K (-Pi.single j 1) :=
      Subgroup.mem_sup_right (by
        rw [← SetLike.mem_coe, coe_rootSubgroup_neg_single]
        exact ⟨_, rfl⟩)
    exact mul_mem (mul_mem hy (Subgroup.mem_sup_left (xUnit_mem_borelGroup j 1))) hy
  · rw [← parabolicSubgroup_singleton_inf_negUnipotent]
    exact inf_le_left

theorem exists_eq_single_of_height_eq_one
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h1 : height α = 1) : ∃ j, α = Pi.single j 1 := by
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

theorem exists_smul_single_eq_neg
    {w₀ : WeylGroup τ} (h₀ : ReversesSigns w₀)
    (hsq : w₀ * w₀ = 1) (i : Fin τ.rank) :
    ∃ j, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single j 1 := by
  set v : Fin τ.rank → ℤ := -(w₀ • (Pi.single i 1 : Fin τ.rank → ℤ)) with hv
  have hvroot : IsRoot τ v := IsRoot.neg (IsRoot.smul (isRoot_single τ i) w₀)
  have hvpos : 0 < height v := by
    rw [hv, height_neg]
    have := h₀ _ (isRoot_single τ i) (by rw [height_single]; exact one_pos)
    omega
  have hvnn := (IsRoot.height_pos_iff hvroot).1 hvpos
  have hback : -(w₀ • v) = Pi.single i 1 := by
    rw [hv, smul_neg, neg_neg, smul_smul, hsq, one_smul]
  have hexp : -(w₀ • v) = ∑ k, v k • -(w₀ • (Pi.single k 1 : Fin τ.rank → ℤ)) := by
    rw [smul_eq_sum_smul_single w₀ v, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => (smul_neg _ _).symm
  have hheight : ∀ k, 1 ≤ height (-(w₀ • (Pi.single k 1 : Fin τ.rank → ℤ))) := fun k => by
    rw [height_neg]
    have := h₀ _ (isRoot_single τ k) (by rw [height_single]; exact one_pos)
    omega
  have hlin : ∀ (s : Finset (Fin τ.rank)) (f : Fin τ.rank → Fin τ.rank → ℤ),
      height (∑ k ∈ s, f k) = ∑ k ∈ s, height (f k) := fun s f => by
    simp only [height, Finset.sum_apply]
    exact Finset.sum_comm
  have hsmul : ∀ (c : ℤ) (x : Fin τ.rank → ℤ), height (c • x) = c * height x := fun c x => by
    simp only [height, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  have hone : height (Pi.single i 1 : Fin τ.rank → ℤ) =
      ∑ k, v k * height (-(w₀ • (Pi.single k 1 : Fin τ.rank → ℤ))) := by
    rw [← hback, hexp, hlin]
    exact Finset.sum_congr rfl fun k _ => hsmul _ _
  rw [height_single] at hone
  have hle : height v ≤ 1 := by
    rw [hone]
    refine Finset.sum_le_sum fun k _ => ?_
    have := hheight k
    have := hvnn k
    nlinarith
  obtain ⟨j, hj⟩ := exists_eq_single_of_height_eq_one hvroot (by omega)
  exact ⟨j, by rw [← hj, hv, neg_neg]⟩

theorem covBy_map_conj_iff (g : ModGL τ K) {H A : Subgroup (ModGL τ K)} :
    H.map (MulAut.conj g).toMonoidHom ⋖ A.map (MulAut.conj g).toMonoidHom ↔ H ⋖ A :=
  apply_covBy_apply_iff (MulEquiv.mapSubgroup (MulAut.conj g))

theorem single_injective_one : Function.Injective
    (fun j : Fin τ.rank => (Pi.single j 1 : Fin τ.rank → ℤ)) := by
  intro j k h
  have := congrFun h j
  simp only [Pi.single_eq_same] at this
  by_contra hjk
  rw [Pi.single_eq_of_ne hjk] at this
  exact one_ne_zero this

variable (τ K) in
theorem exists_opposite_data :
    ∃ (n₀ : ModGL τ K) (δ : Fin τ.rank → Fin τ.rank),
    n₀ ∈ adjointGroup τ K ∧ (∀ i, δ (δ i) = i) ∧
    (borelGroup τ K).map (MulAut.conj n₀).toMonoidHom = oppositeBorel τ K ∧
    (negUnipotent τ K).map (MulAut.conj n₀).toMonoidHom = posUnipotent τ K ∧
    ∀ i, (rootSubgroup τ K (-Pi.single i 1)).map (MulAut.conj n₀).toMonoidHom =
      rootSubgroup τ K (Pi.single (δ i) 1) := by
  obtain ⟨w₀, hmax, -, himage, hsq, -, -⟩ := weyl_longest_element τ
  have h₀ : ReversesSigns w₀ := reversesSigns_of_forall_length_le hmax
  have hsq' : w₀ * w₀ = 1 := by rw [← pow_two]; exact hsq
  choose δ hδ using exists_smul_single_eq_neg h₀ hsq'
  have hδδ : ∀ i, δ (δ i) = i := fun i => by
    have h1 : w₀ • (w₀ • (Pi.single i 1 : Fin τ.rank → ℤ)) = Pi.single i 1 := by
      rw [smul_smul, hsq', one_smul]
    rw [hδ i, smul_neg, hδ (δ i), neg_neg] at h1
    exact single_injective_one h1
  have himage' : (fun α => w₀ • α) '' {α : Fin τ.rank → ℤ | IsRoot τ α ∧ height α < 0} =
      {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α} := by
    rw [← himage, Set.image_image]
    simp only [smul_smul, hsq', one_smul, Set.image_id']
  obtain ⟨hS, hR, -⟩ := canonical_weyl_root_transport τ K
  refine ⟨canonicalRep (coxeterSystem τ) K w₀, δ, canonicalRep_mem_adjointGroup _ K w₀, hδδ,
    (opposite_Borel_intersection τ K w₀ hmax).2.1, ?_, fun i => ?_⟩
  · rw [negUnipotent, hS w₀ _ fun α hα => hα.1, himage']
    rfl
  · rw [hR w₀ _ (IsRoot.neg (isRoot_single τ i)), smul_neg, hδ, neg_neg]

theorem exceptional_ordinary_minimal_Borel_intersections
    (τ : Tag) (K : Type) [Field K] :
    (∀ A : Subgroup (ModGL τ K), A ≤ adjointGroup τ K →
      (borelGroup τ K ⋖ A ↔ ∃ i, A = parabolicSubgroup τ K {i})) ∧
    Function.Injective (fun i : Fin τ.rank => parabolicSubgroup τ K {i}) ∧
    (∀ i, ((parabolicSubgroup τ K {i} ⊓ negUnipotent τ K : Subgroup (ModGL τ K)) :
      Set (ModGL τ K)) = Set.range (yUnit τ K i)) ∧
    (∀ A : Subgroup (ModGL τ K), A ≤ adjointGroup τ K →
      (oppositeBorel τ K ⋖ A ↔ ∃ i, A = oppositeMinimalParabolic τ K i)) ∧
    Function.Injective (oppositeMinimalParabolic τ K) ∧
    ∀ i, ((oppositeMinimalParabolic τ K i ⊓ posUnipotent τ K : Subgroup (ModGL τ K)) :
      Set (ModGL τ K)) = Set.range (xUnit τ K i) := by
  have hPinj : Function.Injective (fun i : Fin τ.rank => parabolicSubgroup τ K {i}) :=
    fun i j h => Set.singleton_injective (parabolicSubgroup_injective h)
  obtain ⟨n₀, δ, hn₀, hδδ, hB, hV, hY⟩ := exists_opposite_data τ K
  set φ : ModGL τ K →* ModGL τ K := (MulAut.conj n₀).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj n₀).injective
  have hφsurj : Function.Surjective φ := (MulAut.conj n₀).surjective
  have hP : ∀ i, (parabolicSubgroup τ K {i}).map φ = oppositeMinimalParabolic τ K (δ i) :=
    fun i => by
      rw [parabolicSubgroup_singleton_eq, Subgroup.map_sup, hB, hY, oppositeMinimalParabolic,
        rootSubgroup_single_eq_closure]
  have hQ : ∀ j, oppositeMinimalParabolic τ K j = (parabolicSubgroup τ K {δ j}).map φ :=
    fun j => by rw [hP, hδδ]
  refine ⟨fun A hA => borelGroup_covBy_iff hA, hPinj, fun i => ?_, fun A hA => ?_, fun j k h => ?_,
    fun j => ?_⟩
  · rw [parabolicSubgroup_singleton_inf_negUnipotent, coe_rootSubgroup_neg_single]
  · have hAc : (A.comap φ).map φ = A := Subgroup.map_comap_eq_self_of_surjective hφsurj A
    have hAcC : A.comap φ ≤ adjointGroup τ K := fun x hx => by
      have h1 : n₀ * x * n₀⁻¹ ∈ adjointGroup τ K := hA hx
      have h2 := mul_mem (mul_mem (inv_mem hn₀) h1) hn₀
      simpa [mul_assoc] using h2
    rw [← hB, ← hAc, covBy_map_conj_iff, borelGroup_covBy_iff hAcC]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨δ i, by rw [hi, hP]⟩
    · rintro ⟨j, hj⟩
      refine ⟨δ j, Subgroup.map_injective hφinj ?_⟩
      rw [hj, hQ]
  · rw [hQ, hQ] at h
    have := hPinj (Subgroup.map_injective hφinj h)
    rw [← hδδ j, ← hδδ k]
    exact congrArg δ this
  · rw [hQ, ← hV, ← Subgroup.map_inf_eq _ _ φ hφinj, parabolicSubgroup_singleton_inf_negUnipotent,
      hY, hδδ, coe_rootSubgroup_single]

end CFSG.LieType.Chevalley
