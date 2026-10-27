module

public import CFSG.LieType.Steinberg.Adjoint.Datum
public import CFSG.LieType.Chevalley.RootOps.CommAll
public import CFSG.LieType.Chevalley.WeylSpace

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootSpace Matrix
open scoped commutatorElement

variable {τ : Tag}

theorem exists_minor_pos {γ δ : Fin τ.rank → ℤ} (hγ : γ ≠ 0) (hlin : LinIndepPair γ δ) :
    ∃ i j, 0 < γ i * δ j - γ j * δ i := by
  obtain ⟨k, hk⟩ : ∃ k, γ k ≠ 0 := by
    by_contra! h
    exact hγ (funext h)
  by_contra! h
  have h0 : ∀ j, γ k * δ j - γ j * δ k = 0 := fun j =>
    le_antisymm (h k j) (by linarith [h j k])
  have := (hlin (δ k) (-γ k) (funext fun j => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    linear_combination -h0 j)).2
  exact hk (neg_eq_zero.1 this)

theorem inner_ofPi_inv_mulVec
    (y : RootSpace τ) (c : Fin τ.rank → ℝ) :
    inner ℝ y (ofPi ((formMatrix τ)⁻¹ *ᵥ c)) = y.toPi ⬝ᵥ c := by
  have hdet : IsUnit (formMatrix τ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (posDef_formMatrix τ).isUnit
  rw [inner_def, toPi_ofPi, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

theorem exists_weyl_height_pos
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (hlin : LinIndepPair γ δ) : ∃ w : WeylGroup τ, 0 < height (w • γ) ∧ 0 < height (w • δ) := by
  obtain ⟨i, j, hM⟩ := exists_minor_pos hγ.ne_zero hlin
  set x : RootSpace τ := ofPi ((formMatrix τ)⁻¹ *ᵥ
    (((δ j - γ j : ℤ) : ℝ) • Pi.single i 1 + ((γ i - δ i : ℤ) : ℝ) • Pi.single j 1))
  have hx : ∀ v : Fin τ.rank → ℤ, inner ℝ (ofLattice v) x =
      ((v i * (δ j - γ j) + v j * (γ i - δ i) : ℤ) : ℝ) := fun v => by
    rw [inner_ofPi_inv_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul,
      dotProduct_single, dotProduct_single]
    simp only [ofLattice_apply, mul_one, smul_eq_mul]
    push_cast
    ring
  obtain ⟨w, y, hy, hxy⟩ := exists_weylAct_mem_dominantCone x
  have key : ∀ v, IsRoot τ v → 0 < v i * (δ j - γ j) + v j * (γ i - δ i) →
      0 < height (w⁻¹ • v) := fun v hv hpos => by
    have hr : IsRoot τ (w⁻¹ • v) := IsRoot.smul hv w⁻¹
    have e : inner ℝ (ofLattice (w⁻¹ • v)) y = inner ℝ (ofLattice v) x := by
      rw [hxy, ← LinearIsometryEquiv.inner_map_map (weylAct τ w), weylAct_ofLattice,
        smul_inv_smul]
    rcases IsRoot.height_pos_or_neg hr with h | h
    · exact h
    · have hn := IsRoot.inner_nonneg_of_mem_dominantCone (IsRoot.neg hr)
        (by rw [height_neg]; omega) hy
      rw [ofLattice_neg, inner_neg_left, e, hx] at hn
      have : (0 : ℝ) < ((v i * (δ j - γ j) + v j * (γ i - δ i) : ℤ) : ℝ) := by exact_mod_cast hpos
      linarith
  have eγ : γ i * (δ j - γ j) + γ j * (γ i - δ i) = γ i * δ j - γ j * δ i := by ring
  have eδ : δ i * (δ j - γ j) + δ j * (γ i - δ i) = γ i * δ j - γ j * δ i := by ring
  exact ⟨w⁻¹, key γ hγ (eγ ▸ hM), key δ hδ (eδ ▸ hM)⟩

theorem ne_of_linIndepPair {γ δ : Fin τ.rank → ℤ} (hlin : LinIndepPair γ δ) : γ ≠ δ := fun h =>
  one_ne_zero (hlin 1 (-1) (by rw [h, one_smul, neg_one_smul, add_neg_cancel])).1

variable (K : Type) [Field K]

theorem commContained_of_linIndepPair
    {α β : Root τ} (hlin : LinIndepPair α.1 β.1) :
    (rootOperatorFamily τ).CommContained K α β := by
  obtain ⟨w, hα, hβ⟩ := exists_weyl_height_pos α.2 β.2 hlin
  have hne : w • α ≠ w • β := fun h =>
    ne_of_linIndepPair hlin (congrArg Subtype.val (smul_left_cancel w h))
  exact ((rootOperatorFamily τ).commContained_smul_iff w).1
    (commContained_pos K (w • α) (w • β) hα hβ hne)

variable {K}

theorem commutator_mem_openCone_of_linIndepPair
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hlin : LinIndepPair γ δ) {x y : adjointGroup τ K}
    (hx : x ∈ rootGroup (rootOperatorFamily τ) K γ)
    (hy : y ∈ rootGroup (rootOperatorFamily τ) K δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (adjDatum (rootOperatorFamily τ) K).roots γ δ,
      (adjDatum (rootOperatorFamily τ) K).rootGroup ε := by
  rw [rootGroup_of_isRoot hγ] at hx
  rw [rootGroup_of_isRoot hδ] at hy
  have h := commContained_of_linIndepPair K (α := ⟨γ, hγ⟩) (β := ⟨δ, hδ⟩) hlin x hx y hy
  have hle : (⨆ (ε : Root τ) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ ε.1 = a • γ + b • δ),
      (rootOperatorFamily τ).rootSubgroup K ε) ≤
      ⨆ ε ∈ openCone (adjDatum (rootOperatorFamily τ) K).roots γ δ,
        (adjDatum (rootOperatorFamily τ) K).rootGroup ε :=
    iSup₂_le fun ε ⟨a, b, ha, hb, hεab⟩ =>
      le_iSup₂_of_le ε.1 ⟨mem_adjDatum_roots.2 ε.2, a, b, ha, hb, hεab⟩
        (rootGroup_of_isRoot ε.2).ge
  rw [commutatorElement_def]
  exact hle h

variable (K) in
theorem steinbergExtras_of_normalizer
    (hnorm : ∀ i, ∀ u ∈ rootGroup (rootOperatorFamily τ) K (Pi.single i 1),
      u ∈ Subgroup.normalizer
        (rootGroup (rootOperatorFamily τ) K (-Pi.single i 1) : Set (adjointGroup τ K)) → u = 1)
    {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : τ.cartan * B = 1) :
    SteinbergExtras (adjDatum (rootOperatorFamily τ) K) (CFSG.LieType.Chevalley.weylElement τ K)
      (torus K) where
  ne_bot γ hγ := rootGroup_ne_bot (mem_adjDatum_roots.1 hγ)
  two_smul_le γ _ h2 := absurd (eq_one_of_isRoot_nsmul (mem_adjDatum_roots.1 h2)) (by norm_num)
  commutator_mem γ hγ δ hδ hlin x hx y hy :=
    commutator_mem_openCone_of_linIndepPair (mem_adjDatum_roots.1 hγ) (mem_adjDatum_roots.1 hδ)
      hlin hx hy
  prodInjective_pos L hnd hmem hsort :=
    prodInjective htHom L hnd
      (fun γ hγ => ⟨mem_adjDatum_roots.1 ((hmem γ).1 hγ).1, ((hmem γ).1 hγ).2.1⟩) hsort
  prodInjective_neg L hnd hmem hsort :=
    prodInjective (-htHom) L hnd
      (fun γ hγ => ⟨mem_adjDatum_roots.1 ((hmem γ).1 hγ).1, by
        rw [AddMonoidHom.neg_apply, htHom_apply]
        exact neg_pos.2 ((hmem γ).1 hγ).2.1⟩)
      (hsort.imp fun h => by
        rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, htHom_apply, htHom_apply]
        exact neg_le_neg h)
  posPart_inf_negPart :=
    eq_bot_iff.2 ((inf_le_inf (iSup₂_le fun γ hγ => rootGroup_le_unip htHom hγ.2)
      (iSup₂_le fun γ hγ => rootGroup_le_unip (-htHom) (by
        rw [AddMonoidHom.neg_apply, htHom_apply]
        exact neg_pos.2 hγ.2))).trans (unip_inf_unip_neg htHom).le)
  rankOne_bruhat i g hg := rankOne_bruhat (rootOperatorFamily τ) i hg
  eq_one_of_mem_normalizer := hnorm
  torus_commute i j h hh h' hh' := torus_commute hh hh'
  torus_iSupIndep := torus_iSupIndep hB
  torus_inf_posPart :=
    eq_bot_iff.2 ((inf_le_inf_left _ (iSup₂_le fun γ hγ => rootGroup_le_unip htHom hγ.2)).trans
      (iSup_torus_inf_unip htHom).le)

end CFSG.LieType.Steinberg.Adjoint
