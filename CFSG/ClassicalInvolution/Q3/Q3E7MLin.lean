module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.EvenOddRadical
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

set_option linter.unusedSectionVars false


section Operators

variable {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {R : Type} [Field R]

include hτ in
theorem xOp_basis_poly (i : Fin τ.rank) (b : Label τ) :
    ∃ a a' : RootModule τ R, ∀ c : R,
      xOp τ R i c (Finsupp.single b 1) = Finsupp.single b 1 + c • a + c ^ 2 • a' := by
  rcases b with j | ⟨α, hα⟩
  · refine ⟨(((τ.cartan j i).natAbs : R)) • rootVec τ R (Pi.single i 1), 0, fun c => ?_⟩
    have h : xOp τ R i c (hVec τ R j) =
        hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1) := by
      change xOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
      rw [xOp, Finsupp.linearCombination_single, one_smul]
    change xOp τ R i c (hVec τ R j) = hVec τ R j + _ + _
    rw [h]
    module
  · by_cases h1 : α = Pi.single i 1
    · refine ⟨0, 0, fun c => ?_⟩
      subst h1
      rw [xOp, Finsupp.linearCombination_single, one_smul]
      simp
    · by_cases h2 : α = -Pi.single i 1
      · refine ⟨hVec τ R i, rootVec τ R (Pi.single i 1), fun c => ?_⟩
        subst h2
        rw [xOp, Finsupp.linearCombination_single, one_smul]
        simp [(single_ne_neg_single i).symm]
      · refine ⟨rootVec τ R (α + Pi.single i 1), 0, fun c => ?_⟩
        have h := xOp_rootVec hτ i c hα h1 h2
        rw [rootVec_of_isRoot hα] at h
        rw [h]
        simp

include hτ in
theorem yOp_basis_poly (i : Fin τ.rank) (b : Label τ) :
    ∃ a a' : RootModule τ R, ∀ c : R,
      yOp τ R i c (Finsupp.single b 1) = Finsupp.single b 1 + c • a + c ^ 2 • a' := by
  rcases b with j | ⟨α, hα⟩
  · refine ⟨(((τ.cartan j i).natAbs : R)) • rootVec τ R (-Pi.single i 1), 0, fun c => ?_⟩
    have h : yOp τ R i c (hVec τ R j) =
        hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1) := by
      change yOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
      rw [yOp, Finsupp.linearCombination_single, one_smul]
    change yOp τ R i c (hVec τ R j) = hVec τ R j + _ + _
    rw [h]
    module
  · by_cases h1 : α = -Pi.single i 1
    · refine ⟨0, 0, fun c => ?_⟩
      subst h1
      rw [yOp, Finsupp.linearCombination_single, one_smul]
      simp
    · by_cases h2 : α = Pi.single i 1
      · refine ⟨hVec τ R i, rootVec τ R (-Pi.single i 1), fun c => ?_⟩
        subst h2
        rw [yOp, Finsupp.linearCombination_single, one_smul]
        simp [single_ne_neg_single i]
      · refine ⟨rootVec τ R (α - Pi.single i 1), 0, fun c => ?_⟩
        have h := yOp_rootVec hτ i c hα h2 h1
        rw [rootVec_of_isRoot hα] at h
        rw [h]
        simp

include hτ in
theorem xOp_eq_poly (h2 : (2 : R) ≠ 0) (i : Fin τ.rank) (c : R) :
    xOp τ R i c = 1 + c • ((2 : R)⁻¹ • (xOp τ R i 1 - xOp τ R i (-1))) +
      c ^ 2 • ((2 : R)⁻¹ • (xOp τ R i 1 + xOp τ R i (-1)) - 1) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  obtain ⟨a, a', ha⟩ := xOp_basis_poly hτ (R := R) i b
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    ha c, ha 1, ha (-1)]
  match_scalars <;> field_simp <;> ring

include hτ in
theorem yOp_eq_poly (h2 : (2 : R) ≠ 0) (i : Fin τ.rank) (c : R) :
    yOp τ R i c = 1 + c • ((2 : R)⁻¹ • (yOp τ R i 1 - yOp τ R i (-1))) +
      c ^ 2 • ((2 : R)⁻¹ • (yOp τ R i 1 + yOp τ R i (-1)) - 1) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  obtain ⟨a, a', ha⟩ := yOp_basis_poly hτ (R := R) i b
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply,
    ha c, ha 1, ha (-1)]
  match_scalars <;> field_simp <;> ring

include hτ in
theorem commute_xOp_of_commute_pm_one (h2 : (2 : R) ≠ 0) (i : Fin τ.rank)
    {y : Module.End R (RootModule τ R)} (h1 : Commute y (xOp τ R i 1))
    (h1' : Commute y (xOp τ R i (-1))) (c : R) : Commute y (xOp τ R i c) := by
  rw [xOp_eq_poly hτ h2 i c]
  have hA : Commute y ((2 : R)⁻¹ • (xOp τ R i 1 - xOp τ R i (-1))) :=
    (h1.sub_right h1').smul_right _
  have hB : Commute y ((2 : R)⁻¹ • (xOp τ R i 1 + xOp τ R i (-1)) - 1) :=
    ((h1.add_right h1').smul_right _).sub_right (Commute.one_right y)
  exact ((Commute.one_right y).add_right (hA.smul_right c)).add_right (hB.smul_right (c ^ 2))

include hτ in
theorem commute_yOp_of_commute_pm_one (h2 : (2 : R) ≠ 0) (i : Fin τ.rank)
    {y : Module.End R (RootModule τ R)} (h1 : Commute y (yOp τ R i 1))
    (h1' : Commute y (yOp τ R i (-1))) (c : R) : Commute y (yOp τ R i c) := by
  rw [yOp_eq_poly hτ h2 i c]
  have hA : Commute y ((2 : R)⁻¹ • (yOp τ R i 1 - yOp τ R i (-1))) :=
    (h1.sub_right h1').smul_right _
  have hB : Commute y ((2 : R)⁻¹ • (yOp τ R i 1 + yOp τ R i (-1)) - 1) :=
    ((h1.add_right h1').smul_right _).sub_right (Commute.one_right y)
  exact ((Commute.one_right y).add_right (hA.smul_right c)).add_right (hB.smul_right (c ^ 2))

end Operators

section Extension

variable {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {F k : Type} [Field F] [Field k]

theorem commute_units_iff {M : Type*} [Monoid M] (a b : Mˣ) :
    Commute a b ↔ Commute (a : M) (b : M) :=
  ⟨Commute.units_val, fun h => Units.ext h.eq⟩

include hτ in
theorem commute_rootSL2_baseChange (ι : F →+* k) (h2 : (2 : k) ≠ 0) (β : Fin τ.rank → ℤ)
    {y : ModGL τ F} (hy : ∀ A : SL2 F, Commute y (rootSL2 τ F β A)) (A : SL2 k) :
    Commute (baseChangeGL ι y) (rootSL2 τ k β A) := by
  set j := (pinnedData τ β).1 with hj
  set W : ModGL τ F := pinnedWeyl τ F β with hW
  have hWk : baseChangeGL ι W = pinnedWeyl τ k β :=
    ModelFacts.Levi.baseChangeGL_pinnedWeyl' ι β
  set y₁ : ModGL τ F := W⁻¹ * y * W with hy₁def
  have hy₁ : ∀ B : SL2 F, Commute y₁ (simpleRootSL2 τ F j B) := by
    intro B
    have h := (hy B).eq
    rw [rootSL2_apply] at h
    show y₁ * simpleRootSL2 τ F j B = simpleRootSL2 τ F j B * y₁
    calc W⁻¹ * y * W * simpleRootSL2 τ F j B
        = W⁻¹ * (y * (W * simpleRootSL2 τ F j B * W⁻¹)) * W := by group
      _ = W⁻¹ * ((W * simpleRootSL2 τ F j B * W⁻¹) * y) * W := by rw [h]
      _ = simpleRootSL2 τ F j B * (W⁻¹ * y * W) := by group
  set yk₁ : ModGL τ k := baseChangeGL ι y₁ with hyk₁
  have hx1 : Commute yk₁ (xUnit τ k j 1) := by
    have := (hy₁ (uSL 1)).map (baseChangeGL ι)
    rw [simpleRootSL2_uSL, baseChangeGL_xUnit, map_one] at this
    exact this
  have hx2 : Commute yk₁ (xUnit τ k j (-1)) := by
    have := (hy₁ (uSL (-1))).map (baseChangeGL ι)
    rw [simpleRootSL2_uSL, baseChangeGL_xUnit, map_neg, map_one] at this
    exact this
  have hv1 : Commute yk₁ (yUnit τ k j 1) := by
    have := (hy₁ (vSL 1)).map (baseChangeGL ι)
    rw [simpleRootSL2_vSL, baseChangeGL_yUnit, map_one] at this
    exact this
  have hv2 : Commute yk₁ (yUnit τ k j (-1)) := by
    have := (hy₁ (vSL (-1))).map (baseChangeGL ι)
    rw [simpleRootSL2_vSL, baseChangeGL_yUnit, map_neg, map_one] at this
    exact this
  have hall : ∀ B : SL2 k, Commute yk₁ (simpleRootSL2 τ k j B) := by
    have hle : (⊤ : Subgroup (SL2 k)) ≤
        (Subgroup.centralizer ({yk₁} : Set (ModGL τ k))).comap (simpleRootSL2 τ k j) := by
      rw [← sl2_closure_upper_lower (K := k)]
      refine (Subgroup.closure_le _).mpr ?_
      rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change simpleRootSL2 τ k j (uSL c) ∈ Subgroup.centralizer ({yk₁} : Set (ModGL τ k))
        rw [simpleRootSL2_uSL, Subgroup.mem_centralizer_singleton_iff]
        have hc : Commute yk₁ (xUnit τ k j c) := (commute_units_iff _ _).2
          (commute_xOp_of_commute_pm_one hτ h2 j ((commute_units_iff _ _).1 hx1)
            ((commute_units_iff _ _).1 hx2) c)
        exact hc.eq.symm
      · change simpleRootSL2 τ k j (vSL c) ∈ Subgroup.centralizer ({yk₁} : Set (ModGL τ k))
        rw [simpleRootSL2_vSL, Subgroup.mem_centralizer_singleton_iff]
        have hc : Commute yk₁ (yUnit τ k j c) := (commute_units_iff _ _).2
          (commute_yOp_of_commute_pm_one hτ h2 j ((commute_units_iff _ _).1 hv1)
            ((commute_units_iff _ _).1 hv2) c)
        exact hc.eq.symm
    intro B
    have hB := hle (Subgroup.mem_top B)
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hB
    exact hB.symm
  have hyk : baseChangeGL ι y = (pinnedWeyl τ k β) * yk₁ * (pinnedWeyl τ k β)⁻¹ := by
    rw [hyk₁, hy₁def, map_mul, map_mul, map_inv, hWk]
    group
  show baseChangeGL ι y * rootSL2 τ k β A = rootSL2 τ k β A * baseChangeGL ι y
  rw [hyk, rootSL2_apply]
  have h := (hall A).eq
  calc pinnedWeyl τ k β * yk₁ * (pinnedWeyl τ k β)⁻¹ *
        (pinnedWeyl τ k β * simpleRootSL2 τ k j A * (pinnedWeyl τ k β)⁻¹)
      = pinnedWeyl τ k β * (yk₁ * simpleRootSL2 τ k j A) * (pinnedWeyl τ k β)⁻¹ := by group
    _ = pinnedWeyl τ k β * (simpleRootSL2 τ k j A * yk₁) * (pinnedWeyl τ k β)⁻¹ := by rw [h]
    _ = pinnedWeyl τ k β * simpleRootSL2 τ k j A * (pinnedWeyl τ k β)⁻¹ *
        (pinnedWeyl τ k β * yk₁ * (pinnedWeyl τ k β)⁻¹) := by group

end Extension

end CFSG.ClassicalInvolution.Q3.Q3W
