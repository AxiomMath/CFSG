module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.LinearAlgebra.Projectivization.Action

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]
  [Module.Finite k X]

private def smulRightLinearMap (l : E →ₗ[k] k) (w : X) : E →ₗ[k] X where
  toFun t := l t • w
  map_add' t u := by simp [add_smul]
  map_smul' c t := by
    rw [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply]

private def compMulLeftLinearMap {Y : Type*} [AddCommGroup Y] [Module k Y]
    (χ : E →ₗ[k] Y) : E →ₗ[k] (E →ₗ[k] Y) where
  toFun s := χ ∘ₗ LinearMap.mulLeft k s
  map_add' s t := by
    ext x
    simp [add_mul, map_add]
  map_smul' c s := by
    ext x
    simp [smul_mul_assoc]

private theorem injective_compMulLeftLinearMap {Y : Type*} [AddCommGroup Y] [Module k Y]
    {χ : E →ₗ[k] Y} (hχ : χ ≠ 0) : Function.Injective (compMulLeftLinearMap χ) := by
  intro s t hst
  by_contra hne
  have hst0 : s - t ≠ 0 := sub_ne_zero.mpr hne
  apply hχ
  ext y
  have hdiff : compMulLeftLinearMap χ (s - t) = 0 := by rw [map_sub, hst, sub_self]
  have h1 : compMulLeftLinearMap χ (s - t) ((s - t)⁻¹ * y) = 0 := by rw [hdiff]; rfl
  have h2 : (s - t) * ((s - t)⁻¹ * y) = y := by
    rw [← mul_assoc, mul_inv_cancel₀ hst0, one_mul]
  simpa [compMulLeftLinearMap, LinearMap.comp_apply, LinearMap.mulLeft_apply, h2] using h1

private theorem exists_specialLinearGroup_smul_eq_of_ne_zero
    {v w : X} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SpecialLinearGroup k X, ∃ c : k, c ≠ 0 ∧ (g : X ≃ₗ[k] X) v = c • w := by
  haveI : MulAction.IsPretransitive (SpecialLinearGroup k X) (Projectivization k X) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq (SpecialLinearGroup k X)
      (Projectivization.mk k v hv) (Projectivization.mk k w hw)
  rw [Projectivization.smul_mk] at hg
  obtain ⟨c, hc⟩ :=
    (Projectivization.mk_eq_mk_iff' k ((g : X ≃ₗ[k] X) v) w
      (fun h => hv ((g : X ≃ₗ[k] X).map_eq_zero_iff.mp h)) hw).mp hg
  have hcne : c ≠ 0 := by
    rintro rfl
    have hzero : (g : X ≃ₗ[k] X) v = 0 := by rw [← hc, zero_smul]
    exact hv ((g : X ≃ₗ[k] X).map_eq_zero_iff.mp hzero)
  exact ⟨g, c, hcne, hc.symm⟩

private theorem exists_eq_comp_mulLeft_of_ne_zero [Module.Finite k E]
    {l₀ : E →ₗ[k] k} (hl₀ : l₀ ≠ 0) (l : E →ₗ[k] k) :
    ∃ s : E, l = l₀ ∘ₗ LinearMap.mulLeft k s := by
  have hfin : Module.finrank k E = Module.finrank k (E →ₗ[k] k) :=
    (Subspace.dual_finrank_eq (K := k) (V := E)).symm
  have hsurj : Function.Surjective (compMulLeftLinearMap l₀) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp
      (injective_compMulLeftLinearMap hl₀)
  obtain ⟨s, hs⟩ := hsurj l
  exact ⟨s, by simpa [compMulLeftLinearMap] using hs.symm⟩

private theorem exists_eq_comp_mulLeft_of_finrank_eq_one [Module.Finite k E]
    (hX : Module.finrank k X = 1) {χ : E →ₗ[k] X} (hχ : χ ≠ 0) (χ' : E →ₗ[k] X) :
    ∃ s : E, χ' = χ ∘ₗ LinearMap.mulLeft k s := by
  have hfin : Module.finrank k E = Module.finrank k (E →ₗ[k] X) := by
    rw [Module.finrank_linearMap, hX, mul_one]
  have hsurj : Function.Surjective (compMulLeftLinearMap χ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp
      (injective_compMulLeftLinearMap hχ)
  obtain ⟨s, hs⟩ := hsurj χ'
  exact ⟨s, by simpa [compMulLeftLinearMap] using hs.symm⟩

private theorem comp_algebraLinearMap_mem_of_stable_hom_to
    (M : AddSubgroup (X →ₗ[k] E))
    (hE : ∀ (s : E) (φ : X →ₗ[k] E), φ ∈ M → LinearMap.mulLeft k s ∘ₗ φ ∈ M)
    (hG : ∀ (g : SpecialLinearGroup k X) (φ : X →ₗ[k] E), φ ∈ M →
      φ ∘ₗ (g : X ≃ₗ[k] X).toLinearMap ∈ M)
    {ψ : X →ₗ[k] E} (hψ : ψ ∈ M) {w : X} (hw : ψ w ≠ 0) :
    ∀ f : X →ₗ[k] k, f w = 0 → (Algebra.linearMap k E).comp f ∈ M := by
  intro f hfw
  let τ : SpecialLinearGroup k X :=
    ⟨LinearEquiv.transvection hfw, LinearEquiv.transvection.det_eq_one hfw⟩
  have h1 : ψ ∘ₗ (τ : X ≃ₗ[k] X).toLinearMap ∈ M := hG τ ψ hψ
  have h2 : ψ ∘ₗ (τ : X ≃ₗ[k] X).toLinearMap - ψ ∈ M := sub_mem h1 hψ
  have h3 : LinearMap.mulLeft k ((ψ w)⁻¹) ∘ₗ
      (ψ ∘ₗ (τ : X ≃ₗ[k] X).toLinearMap - ψ) ∈ M := hE _ _ h2
  have h4 : LinearMap.mulLeft k ((ψ w)⁻¹) ∘ₗ
      (ψ ∘ₗ (τ : X ≃ₗ[k] X).toLinearMap - ψ) =
      (Algebra.linearMap k E).comp f := by
    ext x
    have hτ : (τ : X ≃ₗ[k] X).toLinearMap x = x + f x • w := by
      change LinearEquiv.transvection hfw x = x + f x • w
      rw [LinearEquiv.transvection.apply]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      Algebra.linearMap_apply, hτ, map_add, map_smul]
    rw [add_sub_cancel_left, Algebra.smul_def,
      mul_comm (algebraMap k E (f x)) (ψ w), ← mul_assoc, inv_mul_cancel₀ hw, one_mul]
  rwa [h4] at h3

private theorem smulRightLinearMap_mem_of_stable_hom_from
    (M : AddSubgroup (E →ₗ[k] X))
    (hG : ∀ (g : SpecialLinearGroup k X) (χ : E →ₗ[k] X), χ ∈ M →
      (g : X ≃ₗ[k] X).toLinearMap ∘ₗ χ ∈ M)
    {χ : E →ₗ[k] X} (hχ : χ ∈ M) {f : X →ₗ[k] k} {w : X} (hfw : f w = 0) :
    smulRightLinearMap (f ∘ₗ χ) w ∈ M := by
  let τ : SpecialLinearGroup k X :=
    ⟨LinearEquiv.transvection hfw, LinearEquiv.transvection.det_eq_one hfw⟩
  have h1 : (τ : X ≃ₗ[k] X).toLinearMap ∘ₗ χ ∈ M := hG τ χ hχ
  have h2 : (τ : X ≃ₗ[k] X).toLinearMap ∘ₗ χ - χ ∈ M := sub_mem h1 hχ
  have h3 : (τ : X ≃ₗ[k] X).toLinearMap ∘ₗ χ - χ = smulRightLinearMap (f ∘ₗ χ) w := by
    ext t
    have hτ : (τ : X ≃ₗ[k] X).toLinearMap (χ t) = χ t + f (χ t) • w := by
      change LinearEquiv.transvection hfw (χ t) = χ t + f (χ t) • w
      rw [LinearEquiv.transvection.apply]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, smulRightLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, hτ, map_add, map_smul]
    rw [add_sub_cancel_left]
  rwa [h3] at h2

private theorem smulRightLinearMap_mem_of_ne_zero [Module.Finite k E]
    (M : AddSubgroup (E →ₗ[k] X))
    (hE : ∀ (s : E) (χ : E →ₗ[k] X), χ ∈ M → χ ∘ₗ LinearMap.mulLeft k s ∈ M)
    {w : X} {l₀ : E →ₗ[k] k} (hl₀ : l₀ ≠ 0)
    (hbase : smulRightLinearMap l₀ w ∈ M) :
    ∀ l : E →ₗ[k] k, smulRightLinearMap l w ∈ M := by
  intro l
  obtain ⟨s, hs⟩ := exists_eq_comp_mulLeft_of_ne_zero hl₀ l
  have h := hE s (smulRightLinearMap l₀ w) hbase
  have heq : smulRightLinearMap l₀ w ∘ₗ LinearMap.mulLeft k s = smulRightLinearMap l w := by
    ext t
    have h1 : l t = l₀ (s * t) := by
      have := congrArg (fun (f : E →ₗ[k] k) => f t) hs
      simpa [LinearMap.comp_apply, LinearMap.mulLeft_apply] using this
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, smulRightLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, h1]
  rwa [heq] at h

private theorem smulRightLinearMap_mem_of_ne_zero_target
    (hX : 2 ≤ Module.finrank k X)
    (M : AddSubgroup (E →ₗ[k] X))
    (hG : ∀ (g : SpecialLinearGroup k X) (χ : E →ₗ[k] X), χ ∈ M →
      (g : X ≃ₗ[k] X).toLinearMap ∘ₗ χ ∈ M)
    {w : X} (hw : w ≠ 0)
    (h : ∀ l : E →ₗ[k] k, smulRightLinearMap l w ∈ M) :
    ∀ (w' : X) (l : E →ₗ[k] k), smulRightLinearMap l w' ∈ M := by
  intro w' l
  by_cases hw' : w' = 0
  · subst hw'
    have hzero : smulRightLinearMap l (0 : X) = 0 := by
      ext t
      simp [smulRightLinearMap]
    rw [hzero]
    exact M.zero_mem
  · obtain ⟨g, c, hc0, hgc⟩ :=
      exists_specialLinearGroup_smul_eq_of_ne_zero (k := k) (X := X) (v := w) (w := w') hw hw'
    have hmem := hG g (smulRightLinearMap ((c⁻¹ : k) • l) w) (h _)
    have hgc' : (g : X ≃ₗ[k] X).toLinearMap w = c • w' := hgc
    have heq : (g : X ≃ₗ[k] X).toLinearMap ∘ₗ smulRightLinearMap ((c⁻¹ : k) • l) w =
        smulRightLinearMap l w' := by
      ext t
      have hlt : ((c⁻¹ : k) • l) t = c⁻¹ * l t := by simp
      simp only [LinearMap.comp_apply, smulRightLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        hlt, map_smul]
      rw [hgc', smul_smul, mul_assoc, mul_comm (l t) c, ← mul_assoc,
        inv_mul_cancel₀ hc0, one_mul]
    rwa [heq] at hmem

theorem eq_bot_or_eq_top_of_stable_hom_to (M : AddSubgroup (X →ₗ[k] E))
    (hE : ∀ (s : E) (φ : X →ₗ[k] E), φ ∈ M → LinearMap.mulLeft k s ∘ₗ φ ∈ M)
    (hG : ∀ (g : SpecialLinearGroup k X) (φ : X →ₗ[k] E), φ ∈ M →
      φ ∘ₗ (g : X ≃ₗ[k] X).toLinearMap ∈ M) :
    M = ⊥ ∨ M = ⊤ := by
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨φ, hφM, hφ0⟩ : ∃ φ ∈ M, φ ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot (le_antisymm (fun x hx => by rw [AddSubgroup.mem_bot]; exact h x hx) bot_le)
  rw [eq_top_iff]
  intro ψ _
  rcases lt_or_ge (Module.finrank k X) 2 with hlt | hge
  · have hcases : Module.finrank k X = 0 ∨ Module.finrank k X = 1 := by omega
    rcases hcases with hX0 | hX1
    · haveI : Subsingleton X := (Module.finrank_eq_zero_iff_of_free k X).mp hX0
      have hφzero : φ = 0 := by
        ext x
        simp [Subsingleton.elim x 0]
      exact absurd hφzero hφ0
    · obtain ⟨x₀, hx₀, hφx₀⟩ : ∃ x₀ : X, x₀ ≠ 0 ∧ φ x₀ ≠ 0 := by
        obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
          by_contra h
          push Not at h
          exact hφ0 (LinearMap.ext h)
        exact ⟨y, fun hy0 => hy (by rw [hy0, map_zero]), hy⟩
      have hspan : ∀ y : X, ∃ c : k, c • x₀ = y :=
        (finrank_eq_one_iff_of_nonzero' x₀ hx₀).mp hX1
      let s : E := (φ x₀)⁻¹ * ψ x₀
      have hs : s * φ x₀ = ψ x₀ := by
        dsimp only [s]
        rw [mul_assoc, mul_comm (ψ x₀) (φ x₀), ← mul_assoc, inv_mul_cancel₀ hφx₀, one_mul]
      have hψeq : ψ = LinearMap.mulLeft k s ∘ₗ φ := by
        ext y
        obtain ⟨c, hc⟩ := hspan y
        calc ψ y = ψ (c • x₀) := by rw [hc]
             _ = c • ψ x₀ := by rw [map_smul]
             _ = c • (s * φ x₀) := by rw [hs]
             _ = s * (c • φ x₀) := by
                   rw [Algebra.smul_def, Algebra.smul_def]
                   ring
             _ = s * φ (c • x₀) := by rw [map_smul]
             _ = (LinearMap.mulLeft k s ∘ₗ φ) y := by rw [hc]; rfl
      rw [hψeq]
      exact hE s φ hφM
  · have hrank : ∀ f : X →ₗ[k] k, (Algebra.linearMap k E).comp f ∈ M := by
      intro f
      obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
        by_contra h
        push Not at h
        exact hφ0 (LinearMap.ext h)
      have hu0 : u ≠ 0 := fun h => hu (by rw [h, map_zero])
      have hker : LinearMap.ker f ≠ ⊥ := by
        apply f.ker_ne_bot_of_finrank_lt
        rw [Module.finrank_self]
        omega
      obtain ⟨w, hwker, hw0⟩ := (LinearMap.ker f).ne_bot_iff.mp hker
      have hfw : f w = 0 := by simpa [LinearMap.mem_ker] using hwker
      obtain ⟨g, c, hc0, hgc⟩ :=
        exists_specialLinearGroup_smul_eq_of_ne_zero (k := k) (X := X) (v := u) (w := w) hu0 hw0
      let g' : SpecialLinearGroup k X := g⁻¹
      have hg'mem : φ ∘ₗ (g' : X ≃ₗ[k] X).toLinearMap ∈ M := hG g' φ hφM
      have hgw : (g' : X ≃ₗ[k] X).toLinearMap (c • w) = u := by
        change (g : X ≃ₗ[k] X)⁻¹ (c • w) = u
        have := congrArg (fun y => (g : X ≃ₗ[k] X).symm y) hgc
        simpa using this.symm
      have hnonzero : (φ ∘ₗ (g' : X ≃ₗ[k] X).toLinearMap) (c • w) ≠ 0 := by
        simp only [LinearMap.comp_apply]
        rw [hgw]
        exact hu
      have hfcw : f (c • w) = 0 := by
        rw [map_smul, hfw, smul_zero]
      exact comp_algebraLinearMap_mem_of_stable_hom_to M hE hG hg'mem hnonzero f hfcw
    let b := Module.finBasis k X
    have hsum : ψ = ∑ i, LinearMap.mulLeft k (ψ (b i)) ∘ₗ
        (Algebra.linearMap k E).comp (b.coord i) := by
      ext t
      rw [LinearMap.sum_apply]
      conv_lhs => rw [← b.sum_repr t]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, Algebra.linearMap_apply,
        Module.Basis.coord_apply]
      rw [map_smul, Algebra.smul_def, mul_comm]
    rw [hsum]
    apply sum_mem
    intro i _
    exact hE (ψ (b i)) _ (hrank (b.coord i))

variable [Module.Finite k E] in
theorem eq_bot_or_eq_top_of_stable_hom_from (M : AddSubgroup (E →ₗ[k] X))
    (hE : ∀ (s : E) (χ : E →ₗ[k] X), χ ∈ M → χ ∘ₗ LinearMap.mulLeft k s ∈ M)
    (hG : ∀ (g : SpecialLinearGroup k X) (χ : E →ₗ[k] X), χ ∈ M →
      (g : X ≃ₗ[k] X).toLinearMap ∘ₗ χ ∈ M) :
    M = ⊥ ∨ M = ⊤ := by
  by_cases hbot : M = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨χ, hχM, hχ0⟩ : ∃ χ ∈ M, χ ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot (le_antisymm (fun x hx => by rw [AddSubgroup.mem_bot]; exact h x hx) bot_le)
  rw [eq_top_iff]
  intro χ' _
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : E, χ t₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hχ0 (LinearMap.ext h)
  rcases lt_or_ge (Module.finrank k X) 2 with hlt | hge
  · have hcases : Module.finrank k X = 0 ∨ Module.finrank k X = 1 := by omega
    rcases hcases with hX0 | hX1
    · haveI : Subsingleton X := (Module.finrank_eq_zero_iff_of_free k X).mp hX0
      have hχzero : χ = 0 := by
        ext x
        exact Subsingleton.elim (χ x) 0
      exact absurd hχzero hχ0
    · obtain ⟨s, hs⟩ := exists_eq_comp_mulLeft_of_finrank_eq_one hX1 hχ0 χ'
      rw [hs]
      exact hE s χ hχM
  · obtain ⟨f₀, hf₀⟩ : ∃ f₀ : X →ₗ[k] k, f₀ (χ t₀) ≠ 0 :=
      Module.Projective.exists_dual_ne_zero k ht₀
    have hker : LinearMap.ker f₀ ≠ ⊥ := by
      apply f₀.ker_ne_bot_of_finrank_lt
      rw [Module.finrank_self]
      omega
    obtain ⟨w, hwker, hw0⟩ := (LinearMap.ker f₀).ne_bot_iff.mp hker
    have hfw : f₀ w = 0 := by simpa [LinearMap.mem_ker] using hwker
    have hbase : smulRightLinearMap (f₀ ∘ₗ χ) w ∈ M :=
      smulRightLinearMap_mem_of_stable_hom_from M hG hχM hfw
    have hfχ0 : f₀ ∘ₗ χ ≠ 0 := by
      intro h
      have h1 : f₀ (χ t₀) = 0 := by
        rw [← LinearMap.comp_apply, h, LinearMap.zero_apply]
      exact hf₀ h1
    have hall : ∀ l : E →ₗ[k] k, smulRightLinearMap l w ∈ M :=
      smulRightLinearMap_mem_of_ne_zero M hE hfχ0 hbase
    have hall' : ∀ (w' : X) (l : E →ₗ[k] k), smulRightLinearMap l w' ∈ M :=
      smulRightLinearMap_mem_of_ne_zero_target hge M hG hw0 hall
    let b := Module.finBasis k X
    have hsum : χ' = ∑ i, smulRightLinearMap (b.coord i ∘ₗ χ') (b i) := by
      ext t
      simp only [LinearMap.sum_apply, smulRightLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        LinearMap.comp_apply, Module.Basis.coord_apply]
      exact (b.sum_repr (χ' t)).symm
    rw [hsum]
    apply sum_mem
    intro i _
    exact hall' (b i) (b.coord i ∘ₗ χ')

end CFSG.LinearAlgebra.RootGroupSL
