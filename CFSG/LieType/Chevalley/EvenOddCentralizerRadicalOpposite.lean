module

public import CFSG.LieType.Chevalley.RootWeightStabilizersGrading
public import CFSG.LieType.Chevalley.MinimalBorelOvergroups
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalLevels

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

@[expose] def gradeBy (φ : (Fin τ.rank → ℤ) →+ ℝ) (b : Label τ) : ℝ :=
  φ b.latticeWeight

theorem labelRaises_pinnedX_sub_one_gradeBy
    (φ : (Fin τ.rank → ℤ) →+ ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hm : ε ≤ φ α) (c : K) :
    LabelRaises (gradeBy φ) ε ((pinnedX τ K α c : Module.End K (RootModule τ K)) - 1) := by
  intro a b hab
  rw [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply, sub_ne_zero] at hab
  obtain ⟨k, hk, hab'⟩ := pinnedX_weight_shift hα c a b hab
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [gradeBy]
  rw [hab', map_add, map_nsmul, nsmul_eq_mul]
  nlinarith

theorem rootSpan_le_labelRaisingSubgroup
    (φ : (Fin τ.rank → ℤ) →+ ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) {X : Set (Fin τ.rank → ℤ)} (hX : ∀ α ∈ X, IsRoot τ α ∧ ε ≤ φ α) :
    rootSpan τ K X ≤ labelRaisingSubgroup τ K (gradeBy φ) ε hε := by
  refine iSup₂_le fun α hα => fun g hg => ?_
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
  obtain ⟨c', hc'⟩ := mem_rootSubgroup.1 (inv_mem hg)
  refine ⟨labelRaises_pinnedX_sub_one_gradeBy φ hε (hX α hα).1 (hX α hα).2 c, ?_⟩
  rw [← hc']
  exact labelRaises_pinnedX_sub_one_gradeBy φ hε (hX α hα).1 (hX α hα).2 c'

theorem parabolicLevi_le_labelRaisingSubgroup
    (φ : (Fin τ.rank → ℤ) →+ ℝ)
    {J : Set (Fin τ.rank)} (hJ : ∀ j ∈ J, φ (Pi.single j 1) = 0) :
    parabolicLevi τ K J ≤ labelRaisingSubgroup τ K (gradeBy φ) 0 le_rfl := by
  refine sup_le (torusGroup_le_labelRaisingSubgroup _) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [← pinnedX_single]
    exact rootSpan_le_labelRaisingSubgroup φ le_rfl (X := {Pi.single j 1})
      (fun α hα => by rw [Set.mem_singleton_iff.1 hα, hJ j hj]; exact ⟨isRoot_single τ j, le_rfl⟩)
      (pinnedX_mem_rootSpan (Set.mem_singleton _) c)
  · rw [← pinnedX_neg_single]
    exact rootSpan_le_labelRaisingSubgroup φ le_rfl (X := {-Pi.single j 1})
      (fun α hα => by
        rw [Set.mem_singleton_iff.1 hα, map_neg, hJ j hj, neg_zero]
        exact ⟨isRoot_neg_single τ j, le_rfl⟩)
      (pinnedX_mem_rootSpan (Set.mem_singleton _) c)

theorem eq_zero_of_labelRaises
    (φ : (Fin τ.rank → ℤ) →+ ℝ) {ε : ℝ} (hε : 0 < ε)
    {T : Module.End K (RootModule τ K)} (h : LabelRaises (gradeBy φ) 0 T)
    (h' : LabelRaises (gradeBy (-φ)) ε T) : T = 0 := by
  refine Finsupp.lhom_ext fun b c => ?_
  have hb : T (Finsupp.single b 1) = 0 := by
    refine Finsupp.ext fun a => ?_
    by_contra hab
    have h1 := h a b hab
    have h2 := h' a b hab
    simp only [gradeBy, AddMonoidHom.neg_apply] at h1 h2
    linarith
  rw [LinearMap.zero_apply, ← Finsupp.smul_single_one, map_smul, hb, smul_zero]

theorem eq_one_of_labelRaises
    (φ : (Fin τ.rank → ℤ) →+ ℝ) {ε : ℝ} (hε : 0 < ε)
    {g : ModGL τ K} (h : LabelRaises (gradeBy φ) 0 ((g : Module.End K (RootModule τ K)) - 1))
    (h' : LabelRaises (gradeBy (-φ)) ε ((g : Module.End K (RootModule τ K)) - 1)) : g = 1 :=
  Units.ext (sub_eq_zero.1 (eq_zero_of_labelRaises φ hε h h'))

variable (τ) in
@[expose] def degreeHom (J : Set (Fin τ.rank)) : (Fin τ.rank → ℤ) →+ ℝ where
  toFun v := (parabolicDegree τ J v : ℝ)
  map_zero' := by rw [parabolicDegree_zero, Int.cast_zero]
  map_add' u v := by rw [parabolicDegree_add, Int.cast_add]

theorem degreeHom_apply (J : Set (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    degreeHom τ J v = (parabolicDegree τ J v : ℝ) :=
  rfl

variable (τ) in
@[expose] def oppRadicalRoots (J : Set (Fin τ.rank)) : Set (Fin τ.rank → ℤ) :=
  {α | -α ∈ parabolicRadicalRoots τ J}

variable (τ K) in
@[expose] def oppRadical
    (J : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  rootSpan τ K (oppRadicalRoots τ J)

theorem isRoot_of_mem_oppRadicalRoots {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ oppRadicalRoots τ J) : IsRoot τ α := by
  have := IsRoot.neg hα.1.1
  rwa [neg_neg] at this

theorem oppRadical_le_negUnipotent
    (J : Set (Fin τ.rank)) :
    oppRadical τ K J ≤ negUnipotent τ K :=
  rootSpan_le_negUnipotent fun α hα => ⟨isRoot_of_mem_oppRadicalRoots hα, by
    have := hα.1.2
    rw [height_neg] at this
    omega⟩

theorem parabolicSubgroup_le_labelRaisingSubgroup
    (J : Set (Fin τ.rank)) :
    parabolicSubgroup τ K J ≤ labelRaisingSubgroup τ K (gradeBy (degreeHom τ J)) 0 le_rfl := by
  have hM := parabolicLevi_le_labelRaisingSubgroup (K := K) (degreeHom τ J) (J := J)
    fun j hj => by rw [degreeHom_apply, parabolicDegree_single_of_mem hj, Int.cast_zero]
  refine sup_le (sup_le (torusGroup_le_labelRaisingSubgroup _)
    (rootSpan_le_labelRaisingSubgroup _ le_rfl fun α hα => ⟨hα.1, ?_⟩))
    ((Subgroup.closure_le _).2 ?_)
  · rw [degreeHom_apply]
    exact_mod_cast parabolicDegree_nonneg_of_pos (J := J) hα.1 hα.2
  · rintro _ ⟨j, hj, rfl⟩
    exact hM (weylElt_mem_parabolicLevi hj)

theorem oppRadical_le_labelRaisingSubgroup
    (J : Set (Fin τ.rank)) :
    oppRadical τ K J ≤ labelRaisingSubgroup τ K (gradeBy (-degreeHom τ J)) 1 zero_le_one :=
  rootSpan_le_labelRaisingSubgroup _ zero_le_one fun α hα => ⟨isRoot_of_mem_oppRadicalRoots hα, by
    rw [AddMonoidHom.neg_apply, degreeHom_apply, ← Int.cast_neg, ← parabolicDegree_neg]
    exact_mod_cast one_le_parabolicDegree_of_mem hα⟩

theorem parabolicSubgroup_inf_oppRadical
    (J : Set (Fin τ.rank)) :
    parabolicSubgroup τ K J ⊓ oppRadical τ K J = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgP, hgQ⟩ := Subgroup.mem_inf.1 hg
  exact Subgroup.mem_bot.2 (eq_one_of_labelRaises (degreeHom τ J) one_pos
    (parabolicSubgroup_le_labelRaisingSubgroup J hgP).1
    (oppRadical_le_labelRaisingSubgroup J hgQ).1)

theorem exists_longest (τ : Tag) :
    ∃ (w₀ : WeylGroup τ) (δ : Fin τ.rank → Fin τ.rank), Function.Injective δ ∧
      (∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) ∧ w₀ * w₀ = 1 ∧
      ReversesSigns w₀ := by
  obtain ⟨w₀, hmax, -, -, hsq, -, -⟩ := weyl_longest_element τ
  have hsq' : w₀ * w₀ = 1 := by rw [← pow_two]; exact hsq
  have h₀ := reversesSigns_of_forall_length_le hmax
  choose δ hδ using exists_smul_single_eq_neg h₀ hsq'
  refine ⟨w₀, δ, fun i j hij => ?_, hδ, hsq', h₀⟩
  have h : w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = w₀ • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    rw [hδ, hδ, hij]
  exact single_injective_one (smul_left_cancel w₀ h)

theorem eq_sum_smul_single (v : Fin τ.rank → ℤ) :
    v = ∑ j, v j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

open _root_.Classical in
theorem parabolicDegree_smul_single (J : Set (Fin τ.rank)) (c : ℤ) (k : Fin τ.rank) :
    parabolicDegree τ J (c • Pi.single k 1) = if k ∈ J then 0 else c := by
  classical
  unfold parabolicDegree
  rw [Finset.sum_eq_single k]
  · split_ifs <;> simp
  · intro i _ hik
    split_ifs <;> simp [hik]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem parabolicDegree_sum (J : Set (Fin τ.rank)) (f : Fin τ.rank → Fin τ.rank → ℤ) :
    parabolicDegree τ J (∑ j, f j) = ∑ j, parabolicDegree τ J (f j) := by
  classical
  unfold parabolicDegree
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [Finset.sum_apply]

theorem parabolicDegree_longest {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}
    (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    parabolicDegree τ (δ '' J) (w₀ • v) = -parabolicDegree τ J v := by
  classical
  conv_rhs => rw [eq_sum_smul_single v]
  rw [smul_eq_sum_smul_single, parabolicDegree_sum, parabolicDegree_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hδ, smul_neg, ← neg_smul, parabolicDegree_smul_single, parabolicDegree_smul_single,
    hinj.mem_set_image]
  split_ifs <;> simp

theorem longest_mem_parabolicGraded
    {w₀ : WeylGroup τ} {δ : Fin τ.rank → Fin τ.rank}
    (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1)
    (J : Set (Fin τ.rank)) (d : ℤ) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J (-d)) :
    (canonicalRep (coxeterSystem τ) K w₀ : Module.End K (RootModule τ K)) x ∈
      parabolicGraded τ K (δ '' J) d := by
  have hmaps : MapsLabelWt (canonicalRep (coxeterSystem τ) K w₀ : Module.End K (RootModule τ K))
      (w₀ • ·) := fun a b hab => by
    have := (mapsWeights_canonicalRep (K := K) w₀).1 a b hab
    rcases a with _ | _ <;> rcases b with _ | _ <;> exact this
  rw [parabolicGraded_eq_supported] at hx ⊢
  refine mem_supported_of_mapsLabelWt hmaps (fun b hb a ha => ?_) hx
  simp only [gradedLabels, Set.mem_ofPred_eq] at hb ⊢
  rw [ha, parabolicDegree_longest hinj hδ, hb, neg_neg]

theorem parabolicRadicalRoots_subset_longest
    {w₀ : WeylGroup τ}
    {δ : Fin τ.rank → Fin τ.rank} (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    parabolicRadicalRoots τ (δ '' J) ⊆ (fun α => w₀ • α) '' oppRadicalRoots τ J := by
  intro β hβ
  have hr := hβ.1.1
  refine ⟨w₀ • β, ?_, by simp only [smul_smul, hsq, one_smul]⟩
  have hd : parabolicDegree τ J (-(w₀ • β)) = parabolicDegree τ (δ '' J) β := by
    have := parabolicDegree_longest hinj hδ J (w₀ • β)
    rw [smul_smul, hsq, one_smul] at this
    rw [parabolicDegree_neg, this]
  show -(w₀ • β) ∈ parabolicRadicalRoots τ J
  refine mem_parabolicRadicalRoots_of_degree (IsRoot.neg (IsRoot.smul hr w₀)) ?_ ?_
  · rw [height_neg]
    have := h₀ β hr hβ.1.2
    omega
  · rw [hd]
    have := one_le_parabolicDegree_of_mem hβ
    omega

theorem map_conj_longest_parabolicRadical_le
    {w₀ : WeylGroup τ}
    {δ : Fin τ.rank → Fin τ.rank} (hinj : Function.Injective δ)
    (hδ : ∀ i, w₀ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single (δ i) 1) (hsq : w₀ * w₀ = 1)
    (h₀ : ReversesSigns w₀) (J : Set (Fin τ.rank)) :
    (parabolicRadical τ K (δ '' J)).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)⁻¹).toMonoidHom ≤ oppRadical τ K J := by
  have hT := (canonical_weyl_root_transport τ K).1 w₀ (oppRadicalRoots τ J)
    fun α hα => isRoot_of_mem_oppRadicalRoots hα
  have hle : parabolicRadical τ K (δ '' J) ≤
      (oppRadical τ K J).map (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)).toMonoidHom := by
    rw [oppRadical, hT]
    exact rootSpan_mono (parabolicRadicalRoots_subset_longest hinj hδ hsq h₀ J)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, rfl⟩ := hle hy
  have e : (MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)⁻¹).toMonoidHom
      ((MulAut.conj (canonicalRep (coxeterSystem τ) K w₀)).toMonoidHom z) = z := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hz

end CFSG.LieType.Chevalley.EvenOddRadical
