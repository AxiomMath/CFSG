module

public import CFSG.LieType.Chevalley.C2E6StandardLevi
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
open scoped Pointwise

variable {J : Set (Fin 4)}

theorem nativeParabolic_eq'
    (J : Set (Fin 4)) :
    nativeParabolic J = graphFixedParabolic TwistTag.E6 K barHom (foldedIndex '' J) :=
  nativeParabolic_eq J

theorem stdRadical_le_stdUnipotent0
    (J : Set (Fin 4)) : stdRadical J ≤ stdUnipotent0 := by
  rw [stdRadical_eq]
  exact graphFixedParabolicRadical_le_graphFixedPosUnipotent _

theorem stdUnipotent0_le_stdBorel
    : stdUnipotent0 ≤ stdBorel :=
  graphFixedPosUnipotent_le_graphFixedRootBorel

theorem stdRadical_le_stdBorel
    (J : Set (Fin 4)) : stdRadical J ≤ stdBorel :=
  (stdRadical_le_stdUnipotent0 J).trans stdUnipotent0_le_stdBorel

theorem stdBorel_le_nativeParabolic
    (J : Set (Fin 4)) : stdBorel ≤ nativeParabolic J := by
  rw [nativeParabolic_eq']
  exact graphFixedRootBorel_le_graphFixedParabolic _ _ _ _

theorem stdRadical_le_nativeParabolic
    (J : Set (Fin 4)) : stdRadical J ≤ nativeParabolic J :=
  (stdRadical_le_stdBorel J).trans (stdBorel_le_nativeParabolic J)

theorem stdRadical_normal
    (J : Set (Fin 4)) :
    ((stdRadical J).subgroupOf (nativeParabolic J)).Normal := by
  have h := (diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K barEquiv
    (foldedIndex '' J)).2.2.2.2.2.2.2.2.2.1
  rw [barEquiv_toRingHom] at h
  rw [stdRadical_eq, nativeParabolic_eq']
  exact h

theorem stdLevi_le_nativeParabolic
    (hJ : (2 : Fin 4) ∈ J) : stdLevi J ≤ nativeParabolic J := by
  have h := (diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K barEquiv
    (foldedIndex '' J)).2.2.2.2.2.2.2.2.2.2.1
  rw [barEquiv_toRingHom] at h
  rw [stdLevi_eq hJ, nativeParabolic_eq']
  exact h

theorem stdLevi_le_parabolicLevi
    (J : Set (Fin 4)) :
    stdLevi J ≤ parabolicLevi Tag.E6 K (nativeUnion J) ⊓ stdFixedGroup :=
  inf_le_inf_right _ (subsystemGroup_le_parabolicLevi _)

theorem stdRadical_inf_stdLevi
    (J : Set (Fin 4)) : stdRadical J ⊓ stdLevi J = ⊥ := by
  have h := (diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K barEquiv
    (foldedIndex '' J)).2.2.2.2.2.2.1
  rw [barEquiv_toRingHom] at h
  refine eq_bot_iff.mpr fun g hg => ?_
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
  have h1 : g ∈ graphFixedParabolicRadical TwistTag.E6 K barHom (foldedIndex '' J) := by
    rw [← stdRadical_eq]
    exact hg1
  have h2 := stdLevi_le_parabolicLevi J hg2
  rw [nativeUnion_eq] at h2
  have h3 : g ∈ graphFixedParabolicRadical TwistTag.E6 K barHom (foldedIndex '' J) ⊓
      (parabolicLevi TwistTag.E6.tag K (TwistTag.E6.orbitUnion (foldedIndex '' J)) ⊓
        twistedFixedGroup TwistTag.E6 K barHom) := ⟨h1, h2⟩
  rw [h] at h3
  exact h3

theorem existsUnique_stdRadical_mul_stdLevi
    (hJ : (2 : Fin 4) ∈ J) {g : ModGL Tag.E6 K}
    (hg : g ∈ nativeParabolic J) :
    ∃! ql : ModGL Tag.E6 K × ModGL Tag.E6 K,
      ql.1 ∈ stdRadical J ∧ ql.2 ∈ stdLevi J ∧ g = ql.1 * ql.2 := by
  have h := (diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K barEquiv
    (foldedIndex '' J)).2.2.2.2.2.2.2.2.2.2.2.1
  rw [barEquiv_toRingHom] at h
  rw [stdRadical_eq, stdLevi_eq hJ]
  rw [nativeParabolic_eq'] at hg
  exact h g hg

theorem stdTorus_le_normalizer_stdLeviUnipotent
    (J : Set (Fin 4)) :
    stdTorus ≤ Subgroup.normalizer (stdLeviUnipotent J : Set (ModGL Tag.E6 K)) := by
  intro h hh
  have hh1 := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hh).1
  have hT : h ∈ torusGroup Tag.E6 K := hh1.1
  have hΓ : h ∈ stdFixedGroup := hh1.2
  have hN := torusGroup_le_normalizer_rootSpan (K := K)
    (S := parabolicPosRoots Tag.E6 (nativeUnion J)) (fun _ hα => hα.1.1) hT
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro g
  constructor
  · intro hg
    obtain ⟨hgV, hgΓ⟩ := Subgroup.mem_inf.mp hg
    exact Subgroup.mem_inf.mpr ⟨(hN g).1 hgV, mul_mem (mul_mem hΓ hgΓ) (inv_mem hΓ)⟩
  · intro hg
    obtain ⟨hgV, hgΓ⟩ := Subgroup.mem_inf.mp hg
    refine Subgroup.mem_inf.mpr ⟨(hN g).2 hgV, ?_⟩
    have := mul_mem (mul_mem (inv_mem hΓ) hgΓ) hΓ
    rwa [show h⁻¹ * (h * g * h⁻¹) * h = g by group] at this

theorem coe_stdLeviBorel
    (J : Set (Fin 4)) :
    (stdLeviBorel J : Set (ModGL Tag.E6 K)) =
      (stdTorus : Set (ModGL Tag.E6 K)) * (stdLeviUnipotent J : Set (ModGL Tag.E6 K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _ (stdTorus_le_normalizer_stdLeviUnipotent J)

theorem stdTorus_le_stdBorel :
    stdTorus ≤ stdBorel :=
  graphFixedRootTorus_le_graphFixedRootBorel

theorem stdLeviUnipotent_le_stdBorel
    (J : Set (Fin 4)) : stdLeviUnipotent J ≤ stdBorel := by
  rw [stdLeviUnipotent_eq]
  exact (graphFixedParabolicLeviUnipotent_le _ _ _ _).trans stdUnipotent0_le_stdBorel

theorem stdLeviBorel_le_stdBorel
    (J : Set (Fin 4)) : stdLeviBorel J ≤ stdBorel :=
  sup_le stdTorus_le_stdBorel (stdLeviUnipotent_le_stdBorel J)

theorem stdLeviBorel_le_stdLevi
    (hJ : (2 : Fin 4) ∈ J) : stdLeviBorel J ≤ stdLevi J := by
  have h := (diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K barEquiv
    (foldedIndex '' J)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [barEquiv_toRingHom] at h
  intro x hx
  have hx' : x ∈ (stdLeviBorel J : Set (ModGL Tag.E6 K)) := hx
  rw [coe_stdLeviBorel] at hx'
  obtain ⟨a, ha, v, hv, rfl⟩ := hx'
  rw [stdLevi_eq hJ]
  refine h ⟨a, ha, v, ?_, rfl⟩
  rw [← stdLeviUnipotent_eq]
  exact hv

theorem existsUnique_stdRadical_mul_stdBorel
    (J : Set (Fin 4)) {b : ModGL Tag.E6 K}
    (hb : b ∈ stdBorel) :
    ∃! qc : ModGL Tag.E6 K × ModGL Tag.E6 K,
      qc.1 ∈ stdRadical J ∧ qc.2 ∈ stdLeviBorel J ∧ b = qc.1 * qc.2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hBset, hBuniq, -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 K barEquiv (foldedIndex '' J)
  rw [barEquiv_toRingHom] at hBset hBuniq
  have hb' : b ∈ (graphFixedRootBorel TwistTag.E6 K barHom : Set (ModGL TwistTag.E6.tag K)) := hb
  rw [hBset] at hb'
  obtain ⟨q, hq, x, hx, rfl⟩ := hb'
  have hx' : x ∈ stdLeviBorel J := by
    have : x ∈ (stdLeviBorel J : Set (ModGL Tag.E6 K)) := by
      rw [coe_stdLeviBorel, stdLeviUnipotent_eq]
      exact hx
    exact this
  refine ⟨(q, x), ⟨by rw [stdRadical_eq]; exact hq, hx', rfl⟩, ?_⟩
  rintro ⟨q', x'⟩ ⟨hq', hx'', heq⟩
  have hx''' : x' ∈ (graphFixedRootTorus TwistTag.E6 K barHom : Set (ModGL TwistTag.E6.tag K)) *
      (graphFixedParabolicLeviUnipotent TwistTag.E6 K barHom (foldedIndex '' J) :
        Set (ModGL TwistTag.E6.tag K)) := by
    have : x' ∈ (stdLeviBorel J : Set (ModGL Tag.E6 K)) := hx''
    rw [coe_stdLeviBorel, stdLeviUnipotent_eq] at this
    exact this
  have hq'' : q' ∈ graphFixedParabolicRadical TwistTag.E6 K barHom (foldedIndex '' J) := by
    rw [← stdRadical_eq]
    exact hq'
  obtain ⟨e1, e2⟩ := hBuniq q' hq'' q hq x' hx''' x hx heq.symm
  rw [e1, e2]

theorem stdLevi_inf_stdBorel
    (hJ : (2 : Fin 4) ∈ J) : stdLevi J ⊓ stdBorel = stdLeviBorel J := by
  refine le_antisymm (fun x hx => ?_) (le_inf (stdLeviBorel_le_stdLevi hJ)
    (stdLeviBorel_le_stdBorel J))
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨⟨q, c⟩, ⟨hq, hc, rfl⟩, -⟩ := existsUnique_stdRadical_mul_stdBorel J hx2
  have hqL : q ∈ stdLevi J := by
    have := mul_mem hx1 (inv_mem (stdLeviBorel_le_stdLevi hJ hc))
    rwa [mul_inv_cancel_right] at this
  have hq1 : q = 1 := by
    have : q ∈ stdRadical J ⊓ stdLevi J := ⟨hq, hqL⟩
    rw [stdRadical_inf_stdLevi] at this
    exact this
  simp only [hq1, one_mul]
  exact hc

theorem wordProd_mem_parabolicWeylGroup
    {S : Set (Fin Tag.E6.rank)} {ω : List (Fin Tag.E6.rank)}
    (h : ∀ j ∈ ω, j ∈ S) : (coxeterSystem Tag.E6).wordProd ω ∈ parabolicWeylGroup Tag.E6 S := by
  induction ω with
  | nil =>
    rw [CoxeterSystem.wordProd_nil]
    exact one_mem _
  | cons j ω ih =>
    rw [CoxeterSystem.wordProd_cons]
    exact mul_mem (Subgroup.subset_closure ⟨j, h j List.mem_cons_self, rfl⟩)
      (ih fun k hk => h k (List.mem_cons_of_mem _ hk))

theorem nativeRefl_mem_parabolicWeylGroup
    {i : Fin 4} (hi : i ∈ J) :
    nativeRefl i ∈ parabolicWeylGroup Tag.E6 (nativeUnion J) :=
  wordProd_mem_parabolicWeylGroup fun _ hj =>
    Set.mem_biUnion hi (Finset.mem_coe.mpr ((Finset.mem_sort (α := Fin 6) (· ≤ ·)).mp hj))

theorem nativeRep_mem_stdLevi
    {i : Fin 4} (hi : i ∈ J) : nativeRep i ∈ stdLevi J := by
  refine ⟨canonicalRep_mem_subsystemGroup (τ := Tag.E6) (K := K) (A := nativeUnion J)
    (nativeRefl_mem_parabolicWeylGroup hi), ?_⟩
  rw [stdFixedGroup_eq_stdGroup, nativeRep, nativeRefl_eq]
  exact canonicalRep_orbitReflection_mem_graphFixedRootGroup _

theorem nativeRep_mem_nativeParabolic
    {i : Fin 4} (hi : i ∈ J) : nativeRep i ∈ nativeParabolic J :=
  Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)

theorem nativeParabolic_mono
    {I : Set (Fin 4)} (hIJ : I ⊆ J) :
    nativeParabolic I ≤ nativeParabolic J :=
  Subgroup.closure_mono (Set.union_subset_union_right _ (Set.image_mono hIJ))

end CFSG.LieType.Chevalley.C2E6Std
