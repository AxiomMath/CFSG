module

public import CFSG.LieType.Chevalley.ParabolicRadicalLeviRoots
public import CFSG.LieType.Chevalley.SimpleRootSubgroups
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

variable (τ) in
@[expose] def gradedLabels (J : Set (Fin τ.rank)) (d : ℤ) : Set (Label τ) :=
  {b | parabolicDegree τ J (labelWt τ b) = d}

variable (τ) in
@[expose] def filtrationLabels (J : Set (Fin τ.rank)) (d : ℤ) : Set (Label τ) :=
  {b | d ≤ parabolicDegree τ J (labelWt τ b)}

theorem parabolicGraded_eq_supported (J : Set (Fin τ.rank)) (d : ℤ) :
    parabolicGraded τ K J d = Finsupp.supported K K (gradedLabels τ J d) := by
  apply le_antisymm
  · rw [parabolicGraded, Submodule.span_le]
    rintro x (⟨α, hα, hd, rfl⟩ | ⟨hd, i, rfl⟩)
    · rw [rootVec_eq_single_of_isRoot hα]
      exact Finsupp.single_mem_supported K 1 (by simpa [gradedLabels, labelWt] using hd)
    · exact Finsupp.single_mem_supported K 1
        (by simp [gradedLabels, labelWt, parabolicDegree_zero, hd])
  · rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    apply Submodule.subset_span
    rcases b with i | ⟨α, hα⟩
    · right
      refine ⟨?_, i, rfl⟩
      simpa [gradedLabels, labelWt, parabolicDegree_zero] using hb.symm
    · left
      exact ⟨α, hα, hb, (rootVec_eq_single_of_isRoot hα).symm⟩

theorem parabolicFiltration_eq_supported (J : Set (Fin τ.rank)) (d : ℤ) :
    parabolicFiltration τ K J d = Finsupp.supported K K (filtrationLabels τ J d) := by
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    rw [parabolicGraded_eq_supported]
    exact Finsupp.supported_mono fun b hb => by
      simp only [gradedLabels, filtrationLabels, Set.mem_ofPred_eq] at hb ⊢
      omega
  · rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    refine (le_iSup₂_of_le (parabolicDegree τ J (labelWt τ b)) hb le_rfl :
      parabolicGraded τ K J _ ≤ parabolicFiltration τ K J d) ?_
    rw [parabolicGraded_eq_supported]
    exact Finsupp.single_mem_supported K 1 rfl

theorem mem_supported_of_mapsLabelWt {f : Module.End K (RootModule τ K)}
    {φ : (Fin τ.rank → ℤ) → Fin τ.rank → ℤ} (hf : MapsLabelWt f φ) {s t : Set (Label τ)}
    (hst : ∀ b ∈ s, ∀ a, labelWt τ a = φ (labelWt τ b) → a ∈ t) {x : RootModule τ K}
    (hx : x ∈ Finsupp.supported K K s) : f x ∈ Finsupp.supported K K t := by
  have hle : (Finsupp.supported K K s).map f ≤ Finsupp.supported K K t := by
    rw [Finsupp.supported_eq_span_single, Submodule.map_span_le]
    rintro _ ⟨b, hb, rfl⟩
    exact (Finsupp.mem_supported K _).2 fun a ha =>
      hst b hb a (hf a b (Finsupp.mem_support_iff.1 ha))
  exact hle ⟨x, hx, rfl⟩

theorem mapsLabelWt_torusElt
    (i : Fin τ.rank) (t : Kˣ) :
    MapsLabelWt (torusElt τ K i t : Module.End K (RootModule τ K)) id := by
  intro a b hab
  rcases b with j | ⟨α, hα⟩
  · have h := torusElt_hVec (τ := τ) (R := K) i j t
    change (torusElt τ K i t : Module.End K (RootModule τ K)) (hVec τ K j) a ≠ 0 at hab
    rw [h, hVec, Finsupp.single_apply] at hab
    split_ifs at hab with hja
    · rw [← hja]
      rfl
    · exact absurd rfl hab
  · have h := torusElt_rootVec (τ := τ) (R := K) i t hα
    rw [rootVec_eq_single_of_isRoot hα] at h
    rw [h, Finsupp.smul_apply, Finsupp.single_apply] at hab
    split_ifs at hab with hαa
    · rw [← hαa]
      rfl
    · simp at hab

theorem mapsLabelWt_pinnedCoeff
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {k : ℕ} (hk : 1 ≤ k) :
    MapsLabelWt (pinnedCoeff τ K α k) (· + k • α) := by
  rw [(rootOperatorFamily τ).pinnedCoeff_eq_smul_D K hα k]
  exact ((rootOperatorFamily τ).mapsLabelWt_D (R := K) ⟨α, hα⟩ hk).smul _

theorem mem_graded_of_mapsLabelWt {J : Set (Fin τ.rank)} {f : Module.End K (RootModule τ K)}
    {v : Fin τ.rank → ℤ} (hf : MapsLabelWt f (· + v)) (hv : parabolicDegree τ J v = 0) {d : ℤ}
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J d) : f x ∈ parabolicGraded τ K J d := by
  rw [parabolicGraded_eq_supported] at hx ⊢
  refine mem_supported_of_mapsLabelWt hf (fun b hb a ha => ?_) hx
  simp only [gradedLabels, Set.mem_ofPred_eq] at hb ⊢
  rw [ha, parabolicDegree_add, hv, add_zero, hb]

theorem mem_filtration_succ_of_mapsLabelWt {J : Set (Fin τ.rank)}
    {f : Module.End K (RootModule τ K)} {v : Fin τ.rank → ℤ} (hf : MapsLabelWt f (· + v))
    (hv : 1 ≤ parabolicDegree τ J v) {d : ℤ} {x : RootModule τ K}
    (hx : x ∈ parabolicFiltration τ K J d) : f x ∈ parabolicFiltration τ K J (d + 1) := by
  rw [parabolicFiltration_eq_supported] at hx ⊢
  refine mem_supported_of_mapsLabelWt hf (fun b hb a ha => ?_) hx
  simp only [filtrationLabels, Set.mem_ofPred_eq] at hb ⊢
  rw [ha, parabolicDegree_add]
  omega

theorem xOp_mem_graded
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) (c : K) {d : ℤ}
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J d) :
    xOp τ K j c x ∈ parabolicGraded τ K J d := by
  rw [xOp_eq_sum_xCoeff, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [xCoeff_zero]
    exact hx
  · refine mem_graded_of_mapsLabelWt (mapsLabelWt_xCoeff j hk) ?_ hx
    rw [parabolicDegree_nsmul, parabolicDegree_single_of_mem hj, mul_zero]

theorem yOp_mem_graded
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) (c : K) {d : ℤ}
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J d) :
    yOp τ K j c x ∈ parabolicGraded τ K J d := by
  rw [yOp_eq_sum_yCoeff, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [yCoeff_zero]
    exact hx
  · have hf : MapsLabelWt (yCoeff τ K j k) (· + (-(k • Pi.single j 1))) :=
      (mapsLabelWt_yCoeff j hk).congr fun μ => sub_eq_add_neg _ _
    refine mem_graded_of_mapsLabelWt hf ?_ hx
    rw [parabolicDegree_neg, parabolicDegree_nsmul, parabolicDegree_single_of_mem hj, mul_zero,
      neg_zero]

theorem torusElt_mem_graded
    {J : Set (Fin τ.rank)} (i : Fin τ.rank) (t : Kˣ) {d : ℤ}
    {x : RootModule τ K} (hx : x ∈ parabolicGraded τ K J d) :
    (torusElt τ K i t : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d := by
  rw [parabolicGraded_eq_supported] at hx ⊢
  exact mem_supported_of_mapsLabelWt (mapsLabelWt_torusElt i t)
    (fun b hb a ha => by
      simp only [gradedLabels, Set.mem_ofPred_eq] at hb ⊢
      rw [ha]
      exact hb) hx

theorem parabolicLevi_preserves
    {J : Set (Fin τ.rank)} {g : ModGL τ K}
    (hg : g ∈ parabolicLevi τ K J) (d : ℤ) {x : RootModule τ K}
    (hx : x ∈ parabolicGraded τ K J d) :
    (g : Module.End K (RootModule τ K)) x ∈ parabolicGraded τ K J d := by
  have hM : parabolicLevi τ K J = Subgroup.closure
      (Set.range (fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2) ∪
        {g | ∃ j ∈ J, ∃ c : K, g = xUnit τ K j c ∨ g = yUnit τ K j c}) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hM] at hg
  induction hg using Subgroup.closure_induction'' generalizing x with
  | mem g hgs =>
    rcases hgs with ⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · exact torusElt_mem_graded i t hx
    · rw [coe_xUnit]
      exact xOp_mem_graded hj c hx
    · rw [coe_yUnit]
      exact yOp_mem_graded hj c hx
  | inv_mem g hgs =>
    rcases hgs with ⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · have h : (torusElt τ K i t)⁻¹ = torusElt τ K i t⁻¹ :=
        inv_eq_of_mul_eq_one_right (by rw [← torusElt_mul, mul_inv_cancel, torusElt_one])
      rw [h]
      exact torusElt_mem_graded i t⁻¹ hx
    · rw [← xUnit_neg, coe_xUnit]
      exact xOp_mem_graded hj (-c) hx
    · rw [← yUnit_neg, coe_yUnit]
      exact yOp_mem_graded hj (-c) hx
  | one => simpa using hx
  | mul g h _ _ hg hh =>
    rw [Units.val_mul, Module.End.mul_apply]
    exact hg (hh hx)

theorem pinnedX_mem_filtration
    {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ}
    (hα : α ∈ parabolicRadicalRoots τ J) (c : K) {d : ℤ} {x : RootModule τ K}
    (hx : x ∈ parabolicFiltration τ K J d) :
    (pinnedX τ K α c : Module.End K (RootModule τ K)) x - x ∈
      parabolicFiltration τ K J (d + 1) := by
  have hsum : (pinnedX τ K α c : Module.End K (RootModule τ K)) x - x =
      ∑ k ∈ (Finset.range 4).erase 0, c ^ k • pinnedCoeff τ K α k x := by
    rw [pinnedX_eq_sum, LinearMap.sum_apply, ← Finset.add_sum_erase _ _ (Finset.mem_range.2
      (by norm_num : 0 < 4)), pow_zero, LinearMap.smul_apply, one_smul, pinnedCoeff_zero,
      Module.End.one_apply, add_sub_cancel_left]
    exact Finset.sum_congr rfl fun k _ => LinearMap.smul_apply _ _ _
  rw [hsum]
  refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (Finset.ne_of_mem_erase hk)
  refine mem_filtration_succ_of_mapsLabelWt (mapsLabelWt_pinnedCoeff hα.1.1 hk1) ?_ hx
  rw [parabolicDegree_nsmul]
  have h1 := one_le_parabolicDegree_of_mem hα
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk1
  nlinarith

theorem filtration_succ_le (J : Set (Fin τ.rank)) (d : ℤ) :
    parabolicFiltration τ K J (d + 1) ≤ parabolicFiltration τ K J d :=
  parabolicFiltration_antitone τ K J (by omega)

theorem parabolicRadical_unipotent
    {J : Set (Fin τ.rank)} {g : ModGL τ K}
    (hg : g ∈ parabolicRadical τ K J) (d : ℤ) {x : RootModule τ K}
    (hx : x ∈ parabolicFiltration τ K J d) :
    (g : Module.End K (RootModule τ K)) x ∈ parabolicFiltration τ K J d ∧
      (g : Module.End K (RootModule τ K)) x - x ∈ parabolicFiltration τ K J (d + 1) := by
  have hQ : parabolicRadical τ K J = Subgroup.closure
      (⋃ α ∈ parabolicRadicalRoots τ J, Set.range (pinnedX τ K α)) := by
    simp only [parabolicRadical, rootSpan, rootSubgroup, Subgroup.closure_iUnion]
  rw [hQ] at hg
  induction hg using Subgroup.closure_induction'' generalizing d x with
  | mem g hgs =>
    obtain ⟨α, hα, c, rfl⟩ := by simpa using hgs
    have h := pinnedX_mem_filtration hα c hx
    refine ⟨?_, h⟩
    have := Submodule.add_mem _ (filtration_succ_le J d h) hx
    rwa [sub_add_cancel] at this
  | inv_mem g hgs =>
    obtain ⟨α, hα, c, rfl⟩ := by simpa using hgs
    rw [pinnedX_neg]
    have h := pinnedX_mem_filtration hα (-c) hx
    refine ⟨?_, h⟩
    have := Submodule.add_mem _ (filtration_succ_le J d h) hx
    rwa [sub_add_cancel] at this
  | one => simpa using hx
  | mul g h _ _ hg hh =>
    obtain ⟨hh1, hh2⟩ := hh d hx
    obtain ⟨hg1, hg2⟩ := hg d hh1
    obtain ⟨-, hg3⟩ := hg (d + 1) hh2
    rw [Units.val_mul, Module.End.mul_apply]
    refine ⟨hg1, ?_⟩
    have hgy := (hg (d + 1) hh2).1
    have : (g : Module.End K (RootModule τ K)) ((h : Module.End K (RootModule τ K)) x) - x =
        (g : Module.End K (RootModule τ K)) ((h : Module.End K (RootModule τ K)) x - x) +
          ((g : Module.End K (RootModule τ K)) x - x) := by
      rw [map_sub]
      abel
    rw [this]
    exact Submodule.add_mem _ hgy (hg d hx).2

theorem parabolicGraded_inf_filtration_succ (J : Set (Fin τ.rank)) (d : ℤ) :
    parabolicGraded τ K J d ⊓ parabolicFiltration τ K J (d + 1) = ⊥ := by
  rw [parabolicGraded_eq_supported, parabolicFiltration_eq_supported, ← Finsupp.supported_inter,
    eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine Finsupp.ext fun b => ?_
  by_contra hb
  have := (Finsupp.mem_supported K x).1 hx (Finsupp.mem_support_iff.2 hb)
  simp only [Set.mem_inter_iff, gradedLabels, filtrationLabels, Set.mem_ofPred_eq] at this
  omega

theorem parabolicRadical_inf_parabolicLevi
    (J : Set (Fin τ.rank)) :
    parabolicRadical τ K J ⊓ parabolicLevi τ K J = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgQ, hgM⟩ := Subgroup.mem_inf.1 hg
  rw [Subgroup.mem_bot]
  refine Units.ext (end_ext_single fun b => ?_)
  set d := parabolicDegree τ J (labelWt τ b)
  have hbV : (Finsupp.single b 1 : RootModule τ K) ∈ parabolicGraded τ K J d := by
    rw [parabolicGraded_eq_supported]
    exact Finsupp.single_mem_supported K 1 rfl
  have hbF : (Finsupp.single b 1 : RootModule τ K) ∈ parabolicFiltration τ K J d := by
    rw [parabolicFiltration_eq_supported]
    exact Finsupp.single_mem_supported K 1 (show d ≤ d from le_rfl)
  have h1 := parabolicLevi_preserves hgM d hbV
  have h2 := (parabolicRadical_unipotent hgQ d hbF).2
  have h3 : (g : Module.End K (RootModule τ K)) (Finsupp.single b 1) - Finsupp.single b 1 ∈
      parabolicGraded τ K J d ⊓ parabolicFiltration τ K J (d + 1) :=
    Submodule.mem_inf.2 ⟨Submodule.sub_mem _ h1 hbV, h2⟩
  rw [parabolicGraded_inf_filtration_succ, Submodule.mem_bot, sub_eq_zero] at h3
  rw [h3, Units.val_one, Module.End.one_apply]

end CFSG.LieType.Chevalley
