module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import CFSG.LinearAlgebra.RootGroupSL.SchurSL

public section

namespace CFSG.ClassicalGroups.SpecialLinear

open Matrix

private theorem transvection_mulVec {K : Type*} [Field K] {n : ℕ} (a b : Fin n) (c : K)
    (x : Fin n → K) :
    Matrix.transvection a b c *ᵥ x = x + Pi.single a (c * x b) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  ext i
  by_cases hi : i = a
  · subst hi
    simp [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne hi]

private theorem transvection_transpose {K : Type*} [Field K] {n : ℕ} (a b : Fin n) (c : K) :
    (Matrix.transvection a b c)ᵀ = Matrix.transvection b a c := by
  simp only [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

private theorem eq_zero_of_natural_dual_hom {K : Type*} [Field K] {n : ℕ} (hn : 3 ≤ n)
    (f : (Fin n → K) →ₗ[K] (Fin n → K))
    (hf : ∀ (A : Matrix.SpecialLinearGroup (Fin n) K) (x : Fin n → K),
      f ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) =
        ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ f x) :
    f = 0 := by
  have key : ∀ a b : Fin n, a ≠ b →
      f (Pi.single a 1) = Pi.single b (-(f (Pi.single b 1) a)) := by
    intro a b hab
    let A : Matrix.SpecialLinearGroup (Fin n) K :=
      Matrix.SpecialLinearGroup.transvection hab 1
    have hcoe : (A : Matrix (Fin n) (Fin n) K) = Matrix.transvection a b 1 := rfl
    have hinv : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        Matrix.transvection a b (-1) := by
      rw [show A⁻¹ = Matrix.SpecialLinearGroup.transvection hab (-1) from
        Matrix.SpecialLinearGroup.transvection_inv hab 1]
      rfl
    have h := hf A (Pi.single b 1)
    rw [hcoe, hinv, transvection_mulVec, transvection_transpose, transvection_mulVec,
      Pi.single_eq_same, one_mul, neg_one_mul, map_add] at h
    exact add_left_cancel h
  have hsingle : ∀ i : Fin n, f (Pi.single i 1) = 0 := by
    intro i
    have hlt : 2 < n := by omega
    obtain ⟨j, hji, -⟩ := Fin.exists_ne_and_ne_of_two_lt i i hlt
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hlt
    have h1 := key i j hji.symm
    have h2 := key i k hki.symm
    have hzero : f (Pi.single i 1) = 0 := by
      have h := congrFun (h1.symm.trans h2) j
      simp only [Pi.single_eq_same, Pi.single_eq_of_ne hkj.symm, neg_eq_zero] at h
      rw [h1, h]
      simp
    exact hzero
  apply LinearMap.ext
  intro x
  rw [show x = ∑ i, x i • Pi.single i 1 from pi_eq_sum_univ' x]
  rw [map_sum]
  simp [map_smul, hsingle]

variable {K U : Type} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {n : ℕ}

private noncomputable def lagPhi (P : LinearMap.BilinForm K U) {V : Submodule K U}
    (b : Module.Basis (Fin n) K V) : U →ₗ[K] (Fin n → K) :=
  LinearMap.pi fun i => P (b i : U)

private lemma lagPhi_apply {P : LinearMap.BilinForm K U} {V : Submodule K U}
    {b : Module.Basis (Fin n) K V} (u : U) (i : Fin n) :
    lagPhi P b u i = P (b i : U) u := rfl

private lemma lagPhi_ker {P : LinearMap.BilinForm K U} {V : Submodule K U}
    (hV : LinearMap.BilinForm.orthogonal P V = V) (b : Module.Basis (Fin n) K V) :
    LinearMap.ker (lagPhi P b) = V := by
  ext u
  constructor
  · intro hu
    rw [LinearMap.mem_ker] at hu
    rw [← hV, LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    have hvsum : v = ∑ i, b.repr ⟨v, hv⟩ i • (b i : U) := by
      have h := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h.symm
    rw [hvsum]
    change (P.flip u) (∑ i, b.repr ⟨v, hv⟩ i • (b i : U)) = 0
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, LinearMap.BilinForm.flip_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : P (b i : U) u = 0 := by
      rw [← lagPhi_apply u i]
      exact congrFun hu i
    rw [hi, mul_zero]
  · intro hu
    rw [LinearMap.mem_ker]
    ext i
    rw [lagPhi_apply, Pi.zero_apply]
    rw [← hV, LinearMap.BilinForm.mem_orthogonal_iff] at hu
    exact hu (b i) (b i).property

private lemma lagPhi_surjective {P : LinearMap.BilinForm K U} (hP : P.Nondegenerate)
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) : Function.Surjective (lagPhi P b) := by
  have hdimV : Module.finrank K V = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hdimU : Module.finrank K U = 2 * n := by
    have h := LinearMap.BilinForm.finrank_orthogonal hP V
    rw [hV, hdimV] at h
    omega
  have hrank := LinearMap.finrank_range_add_finrank_ker (lagPhi P b)
  rw [lagPhi_ker hV b, hdimV, hdimU] at hrank
  have hrange : Module.finrank K (LinearMap.range (lagPhi P b)) = n := by omega
  have htop : LinearMap.range (lagPhi P b) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrange, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact LinearMap.range_eq_top.mp htop

private lemma exists_lagRightInverse {P : LinearMap.BilinForm K U} (hP : P.Nondegenerate)
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) :
    ∃ σ : (Fin n → K) →ₗ[K] U, ∀ y, lagPhi P b (σ y) = y := by
  obtain ⟨σ, hσ⟩ := (lagPhi P b).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (lagPhi_surjective hP hV b))
  refine ⟨σ, fun y => ?_⟩
  have h := LinearMap.congr_fun hσ y
  simpa using h

private lemma lagRightInverse_sub_mem_V {P : LinearMap.BilinForm K U}
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) (σ : (Fin n → K) →ₗ[K] U)
    (hσ : ∀ y, lagPhi P b (σ y) = y) (u : U) :
    σ (lagPhi P b u) - u ∈ V := by
  have h : lagPhi P b (σ (lagPhi P b u) - u) = 0 := by
    rw [map_sub, hσ, sub_self]
  have hker : σ (lagPhi P b u) - u ∈ LinearMap.ker (lagPhi P b) :=
    LinearMap.mem_ker.mpr h
  rwa [lagPhi_ker hV b] at hker

private noncomputable def restrictEquivMap (g : U ≃ₗ[K] U) {V : Submodule K U}
    (hΓV : ∀ v ∈ V, g v ∈ V) : V →ₗ[K] V where
  toFun v := ⟨g v, hΓV v v.property⟩
  map_add' v w := by
    apply Subtype.ext
    simp
  map_smul' a v := by
    apply Subtype.ext
    simp

private lemma restrictEquivMap_apply (g : U ≃ₗ[K] U) {V : Submodule K U}
    (hΓV : ∀ v ∈ V, g v ∈ V) (v : V) :
    ((restrictEquivMap g hΓV v : V) : U) = g v := rfl

private lemma codRestrict_comp_eq_toLin {V : Submodule K U}
    {b : Module.Basis (Fin n) K V} {g : U ≃ₗ[K] U}
    {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hΓV : ∀ v ∈ V, g v ∈ V)
    (hg : ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U)) :
    restrictEquivMap g hΓV = Matrix.toLin b b (A : Matrix (Fin n) (Fin n) K) := by
  apply b.ext
  intro j
  apply Subtype.ext
  rw [restrictEquivMap_apply, Matrix.toLin_self, Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  exact hg j

private lemma equivFun_comp_of_basis {V : Submodule K U}
    {b : Module.Basis (Fin n) K V} {g : U ≃ₗ[K] U}
    {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hΓV : ∀ v ∈ V, g v ∈ V)
    (hg : ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U)) :
    ∀ v : V, b.equivFun ⟨g v, hΓV v v.property⟩ =
      (A : Matrix (Fin n) (Fin n) K) *ᵥ b.equivFun v := by
  let gV : V →ₗ[K] V := restrictEquivMap g hΓV
  have hgV : gV = Matrix.toLin b b (A : Matrix (Fin n) (Fin n) K) :=
    codRestrict_comp_eq_toLin hΓV hg
  intro v
  change b.equivFun (gV v) = (A : Matrix (Fin n) (Fin n) K) *ᵥ b.equivFun v
  rw [hgV, Matrix.toLin_apply, Module.Basis.equivFun_apply, Module.Basis.repr_sum_self,
    Module.Basis.equivFun_apply]

private lemma symm_apply_basis {V : Submodule K U}
    {b : Module.Basis (Fin n) K V} {g : U ≃ₗ[K] U}
    {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hΓV : ∀ v ∈ V, g v ∈ V)
    (hg : ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (i : Fin n) :
    g.symm (b i : U) = ∑ k, ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) k i • (b k : U) := by
  have hgV : restrictEquivMap g hΓV =
      Matrix.toLin b b (A : Matrix (Fin n) (Fin n) K) :=
    codRestrict_comp_eq_toLin hΓV hg
  have hy : Matrix.toLin b b (A : Matrix (Fin n) (Fin n) K)
      (∑ k, ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) k i • (b k : V)) = b i := by
    rw [← Matrix.toLin_self b b ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i]
    rw [← Matrix.toLin_mul_apply]
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.toLin_one]
    rfl
  have hy' : restrictEquivMap g hΓV
      (∑ k, ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) k i • (b k : V)) = b i := by
    rw [hgV]
    exact hy
  have hyU : g (∑ k, ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) k i • (b k : U)) = (b i : U) := by
    have h := congrArg Subtype.val hy'
    simpa [restrictEquivMap_apply] using h
  exact (LinearEquiv.symm_apply_eq g).mpr hyU.symm

private lemma lagPhi_comp_iso {P : LinearMap.BilinForm K U} {V : Submodule K U}
    {b : Module.Basis (Fin n) K V} {g : U ≃ₗ[K] U}
    {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hΓV : ∀ v ∈ V, g v ∈ V)
    (hg : ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (hgP : ∀ u w, P (g u) (g w) = P u w) (u : U) :
    lagPhi P b (g u) = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)ᵀ *ᵥ lagPhi P b u := by
  ext i
  rw [lagPhi_apply, Matrix.mulVec_apply_eq_sum]
  have hiso : P (b i : U) (g u) = P (g.symm (b i : U)) u := by
    have h1 : P (b i : U) (g u) = P (g (g.symm (b i : U))) (g u) := by
      rw [g.apply_symm_apply]
    rw [h1]
    exact hgP _ _
  rw [hiso, symm_apply_basis hΓV hg i]
  change (P.flip u) (∑ k, ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K) k i • (b k : U)) =
    ∑ j, (((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K)ᵀ) i j * lagPhi P b u j
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, LinearMap.BilinForm.flip_apply, Matrix.transpose_apply,
    lagPhi_apply]

section PreservesLagrangian

variable {K U : Type} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {n : ℕ}

private noncomputable def psiCoord (P : LinearMap.BilinForm K U) {V : Submodule K U}
    (b : Module.Basis (Fin n) K V) (ψ : U →ₗ[K] U) :
    (Fin n → K) →ₗ[K] (Fin n → K) :=
  (lagPhi P b).comp (ψ.comp (V.subtype.comp b.equivFun.symm.toLinearMap))

private lemma psiCoord_intertwines {P : LinearMap.BilinForm K U} {V : Submodule K U}
    {b : Module.Basis (Fin n) K V} {Γ : Set (U ≃ₗ[K] U)}
    (hΓP : ∀ g ∈ Γ, ∀ u w, P (g u) (g w) = P u w)
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (ψ : U →ₗ[K] U) (hψ : ∀ g ∈ Γ, ∀ u, ψ (g u) = g (ψ u)) :
    ∀ (A : Matrix.SpecialLinearGroup (Fin n) K) (x : Fin n → K),
      psiCoord P b ψ ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) =
        ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)ᵀ *ᵥ psiCoord P b ψ x := by
  intro A x
  let e : (Fin n → K) →ₗ[K] U := V.subtype.comp b.equivFun.symm.toLinearMap
  obtain ⟨g, hgΓ, hg⟩ := hSL A
  have hgV : ∀ v ∈ V, g v ∈ V := fun v hv => hΓV g hgΓ v hv
  have hc := equivFun_comp_of_basis (V := V) (b := b) (g := g) (A := A) hgV hg
    (b.equivFun.symm x)
  have hc2 : b.equivFun ⟨g (b.equivFun.symm x),
      hgV (b.equivFun.symm x) (b.equivFun.symm x).property⟩ =
      (A : Matrix (Fin n) (Fin n) K) *ᵥ x := by
    rw [hc, b.equivFun.apply_symm_apply]
  have hc' : b.equivFun.symm ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) =
      ⟨g (b.equivFun.symm x), hgV _ (b.equivFun.symm x).property⟩ := by
    apply b.equivFun.injective
    rw [b.equivFun.apply_symm_apply, hc2]
  have he : e ((A : Matrix (Fin n) (Fin n) K) *ᵥ x) = g (e x) := by
    simp only [e, LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe]
    rw [hc']
  calc psiCoord P b ψ ((A : Matrix (Fin n) (Fin n) K) *ᵥ x)
      = lagPhi P b (ψ (e ((A : Matrix (Fin n) (Fin n) K) *ᵥ x))) := rfl
    _ = lagPhi P b (ψ (g (e x))) := by rw [he]
    _ = lagPhi P b (g (ψ (e x))) := by rw [hψ g hgΓ]
    _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)ᵀ *ᵥ lagPhi P b (ψ (e x)) :=
        lagPhi_comp_iso hgV hg (hΓP g hgΓ) (ψ (e x))
    _ = ((A⁻¹ : Matrix.SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)ᵀ *ᵥ psiCoord P b ψ x := rfl

private lemma psi_maps_V {P : LinearMap.BilinForm K U} {V : Submodule K U}
    (hV : LinearMap.BilinForm.orthogonal P V = V) (b : Module.Basis (Fin n) K V)
    {Γ : Set (U ≃ₗ[K] U)}
    (hΓP : ∀ g ∈ Γ, ∀ u w, P (g u) (g w) = P u w)
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (ψ : U →ₗ[K] U) (hψ : ∀ g ∈ Γ, ∀ u, ψ (g u) = g (ψ u))
    (hn : 3 ≤ n) : ∀ v : V, ψ (v : U) ∈ V := by
  have hfzero := eq_zero_of_natural_dual_hom hn (psiCoord P b ψ)
    (psiCoord_intertwines hΓP hΓV hSL ψ hψ)
  intro v
  have h : psiCoord P b ψ (b.equivFun v) = 0 := by rw [hfzero]; rfl
  have hfv : psiCoord P b ψ (b.equivFun v) = lagPhi P b (ψ (v : U)) := by
    simp only [psiCoord, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      LinearEquiv.symm_apply_apply]
  rw [hfv] at h
  have hmem : ψ (v : U) ∈ LinearMap.ker (lagPhi P b) := LinearMap.mem_ker.mpr h
  rwa [lagPhi_ker hV b] at hmem

end PreservesLagrangian

section ScalarOnLagrangian

variable {K U : Type} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {n : ℕ}

private noncomputable def psiRestrict (ψ : U →ₗ[K] U) {V : Submodule K U}
    (hψV : ∀ v : V, ψ (v : U) ∈ V) : V →+ V where
  toFun v := ⟨ψ (v : U), hψV v⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' v w := by
    apply Subtype.ext
    simp

private lemma psiRestrict_commutes {V : Submodule K U} (b : Module.Basis (Fin n) K V)
    {Γ : Set (U ≃ₗ[K] U)}
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (ψ : U →ₗ[K] U) (hψ : ∀ g ∈ Γ, ∀ u, ψ (g u) = g (ψ u))
    (hψV : ∀ v : V, ψ (v : U) ∈ V) :
    ∀ g : SpecialLinearGroup K V, ∀ v : V,
      psiRestrict ψ hψV (g v) = g (psiRestrict ψ hψV v) := by
  intro g v
  let A : Matrix.SpecialLinearGroup (Fin n) K :=
    (Matrix.SpecialLinearGroup.toLin_equiv b).symm g
  have hgA : Matrix.SpecialLinearGroup.toLin_equiv b A = g := by
    simpa [A] using (Matrix.SpecialLinearGroup.toLin_equiv b).apply_symm_apply g
  obtain ⟨h, hhΓ, hh⟩ := hSL A
  have hgV_eq : (g : V →ₗ[K] V) = Matrix.toLin b b (A : Matrix (Fin n) (Fin n) K) := by
    apply b.ext
    intro j
    have h1 : (g : V →ₗ[K] V) (b j) =
        (Matrix.SpecialLinearGroup.toLin_equiv b A : V →ₗ[K] V) (b j) := by
      rw [hgA]
    rw [h1, Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq, Matrix.toLin_self]
  have hg_basis : ∀ j, ((g : V →ₗ[K] V) (b j) : U) =
      ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U) := by
    intro j
    have h := congrArg Subtype.val (LinearMap.congr_fun hgV_eq (b j))
    rw [Matrix.toLin_self] at h
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  have hg_eq : ∀ v : V, (g v : U) = h v := by
    have hlin : (V.subtype.comp (g : V →ₗ[K] V)) = h.toLinearMap.comp V.subtype := by
      apply b.ext
      intro j
      exact (hg_basis j).trans (hh j).symm
    intro w
    exact LinearMap.congr_fun hlin w
  apply Subtype.ext
  calc (psiRestrict ψ hψV (g v) : U) = ψ (g v) := rfl
    _ = ψ (h v) := by rw [hg_eq v]
    _ = h (ψ (v : U)) := hψ h hhΓ (v : U)
    _ = h ((psiRestrict ψ hψV v : V) : U) := rfl
    _ = (g (psiRestrict ψ hψV v) : U) := by rw [hg_eq (psiRestrict ψ hψV v)]

private lemma psi_scalar_on_V {V : Submodule K U} (b : Module.Basis (Fin n) K V)
    {Γ : Set (U ≃ₗ[K] U)}
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (ψ : U →ₗ[K] U) (hψ : ∀ g ∈ Γ, ∀ u, ψ (g u) = g (ψ u))
    (hψV : ∀ v : V, ψ (v : U) ∈ V) (hn : 3 ≤ n) :
    ∃ a : K, ∀ v : V, ψ (v : U) = a • (v : U) := by
  have hfin : Module.finrank K V = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  obtain ⟨a, ha⟩ := CFSG.LinearAlgebra.RootGroupSL.exists_smul_of_commute_specialLinear
    (F := K) (V := V) (by omega : 2 ≤ Module.finrank K V) (psiRestrict ψ hψV)
    (psiRestrict_commutes b hΓV hSL ψ hψ hψV)
  refine ⟨a, fun v => ?_⟩
  simpa [psiRestrict] using congrArg Subtype.val (ha v)

end ScalarOnLagrangian

section MatrixHelpers

variable {K : Type} [Field K] {n : ℕ}

private lemma transpose_transpose (A : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose A) = A := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.transpose]

private lemma transpose_inv (A : Matrix.SpecialLinearGroup (Fin n) K) :
    Matrix.SpecialLinearGroup.transpose A⁻¹ = (Matrix.SpecialLinearGroup.transpose A)⁻¹ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.adjugate_transpose]

private lemma transpose_inv_surjective (B : Matrix.SpecialLinearGroup (Fin n) K) :
    ∃ A : Matrix.SpecialLinearGroup (Fin n) K,
      Matrix.SpecialLinearGroup.transpose A⁻¹ = B ∧
        A = Matrix.SpecialLinearGroup.transpose B⁻¹ := by
  refine ⟨(Matrix.SpecialLinearGroup.transpose B)⁻¹, ?_, ?_⟩
  · rw [inv_inv, transpose_transpose]
  · exact (transpose_inv B).symm

private lemma exists_scalar_of_commutes_slMatrix (hn : 3 ≤ n)
    (T : (Fin n → K) →ₗ[K] (Fin n → K))
    (hT : ∀ (B : Matrix.SpecialLinearGroup (Fin n) K) (y : Fin n → K),
      T ((B : Matrix (Fin n) (Fin n) K) *ᵥ y) =
        (B : Matrix (Fin n) (Fin n) K) *ᵥ T y) :
    ∃ c : K, T = c • LinearMap.id := by
  have hSchur : ∀ g : SpecialLinearGroup K (Fin n → K), ∀ y, T (g y) = g (T y) := by
    intro g y
    let B : Matrix.SpecialLinearGroup (Fin n) K :=
      (Matrix.SpecialLinearGroup.toLin_equiv (Pi.basisFun K (Fin n))).symm g
    have hB : Matrix.SpecialLinearGroup.toLin_equiv (Pi.basisFun K (Fin n)) B = g :=
      (Matrix.SpecialLinearGroup.toLin_equiv (Pi.basisFun K (Fin n))).apply_symm_apply g
    have hg_lin : (g : (Fin n → K) →ₗ[K] (Fin n → K)) =
        Matrix.toLin (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin n))
          (B : Matrix (Fin n) (Fin n) K) := by
      have h := congrArg (fun x : SpecialLinearGroup K (Fin n → K) =>
        (x : (Fin n → K) →ₗ[K] (Fin n → K))) hB
      rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq] at h
      exact h.symm
    have hg : ∀ z, g z = (B : Matrix (Fin n) (Fin n) K) *ᵥ z := by
      intro z
      have := LinearMap.congr_fun hg_lin z
      rwa [Matrix.toLin_eq_toLin', Matrix.toLin'_apply] at this
    rw [hg y, hT B y, hg (T y)]
  obtain ⟨c, hc⟩ := CFSG.LinearAlgebra.RootGroupSL.exists_smul_of_commute_specialLinear
    (F := K) (V := (Fin n → K)) (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      omega) T.toAddMonoidHom hSchur
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro y
  simpa using hc y

private lemma exists_scalar_of_commutes_transposeInv (hn : 3 ≤ n)
    (T : (Fin n → K) →ₗ[K] (Fin n → K))
    (hT : ∀ (A : Matrix.SpecialLinearGroup (Fin n) K) (y : Fin n → K),
      T ((Matrix.SpecialLinearGroup.transpose A⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ y) =
        (Matrix.SpecialLinearGroup.transpose A⁻¹ : Matrix (Fin n) (Fin n) K) *ᵥ T y) :
    ∃ c : K, T = c • LinearMap.id := by
  apply exists_scalar_of_commutes_slMatrix hn
  intro B y
  obtain ⟨A, hA, -⟩ := transpose_inv_surjective B
  have hAm : (Matrix.SpecialLinearGroup.transpose A⁻¹ : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) := congrArg Subtype.val hA
  rw [← hAm]
  exact hT A y

end MatrixHelpers

section ScalarModuloLagrangian

variable {K U : Type} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {n : ℕ}

private lemma Kmap_relation {P : LinearMap.BilinForm K U} (hP : P.Nondegenerate)
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) {Γ : Set (U ≃ₗ[K] U)}
    (hΓP : ∀ g ∈ Γ, ∀ u w, P (g u) (g w) = P u w)
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (S : U →ₗ[K] U) (σ : (Fin n → K) →ₗ[K] U)
    (Kmap : (Fin n → K) →ₗ[K] (Fin n → K))
    (hKmap_Phi : ∀ u : U, Kmap (lagPhi P b u) = lagPhi P b (S u))
    (hScomm : ∀ g ∈ Γ, ∀ u, S (g u) = g (S u)) :
    ∀ (A : Matrix.SpecialLinearGroup (Fin n) K) (y : Fin n → K),
      Kmap ((↑(A⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ y) =
        (↑(A⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ Kmap y := by
  intro A y
  obtain ⟨u, rfl⟩ := lagPhi_surjective hP hV b y
  obtain ⟨g, hgΓ, hg⟩ := hSL A
  have hgV : ∀ v ∈ V, g v ∈ V := fun v hv => hΓV g hgΓ v hv
  rw [← lagPhi_comp_iso hgV hg (hΓP g hgΓ) u, hKmap_Phi, hScomm g hgΓ u,
    hKmap_Phi, lagPhi_comp_iso hgV hg (hΓP g hgΓ) (S u)]

private lemma psi_sub_scalar_mem_V_add {P : LinearMap.BilinForm K U} (hP : P.Nondegenerate)
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) {Γ : Set (U ≃ₗ[K] U)}
    (hΓP : ∀ g ∈ Γ, ∀ u w, P (g u) (g w) = P u w)
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (ψ : U →ₗ[K] U) (hψ : ∀ g ∈ Γ, ∀ u, ψ (g u) = g (ψ u))
    (hψV : ∀ v : V, ψ (v : U) ∈ V) {a : K} (ha : ∀ v : V, ψ (v : U) = a • (v : U))
    (hn : 3 ≤ n) :
    ∃ a' : K, ∀ u : U, ψ u - a • u - a' • u ∈ V := by
  let S : U →ₗ[K] U := ψ - a • LinearMap.id
  have hSV : ∀ v : V, S (v : U) = 0 := by
    intro v
    simp [S, ha v]
  have hScomm : ∀ g ∈ Γ, ∀ u, S (g u) = g (S u) := by
    intro g hg u
    simp only [S, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hψ g hg u, map_sub, map_smul]
  obtain ⟨σ, hσ⟩ := exists_lagRightInverse hP hV b
  let Kmap : (Fin n → K) →ₗ[K] (Fin n → K) := (lagPhi P b).comp (S.comp σ)
  have hKmap_Phi : ∀ u : U, Kmap (lagPhi P b u) = lagPhi P b (S u) := by
    intro u
    have hzero : S (σ (lagPhi P b u) - u) = 0 := by
      have := hSV ⟨_, lagRightInverse_sub_mem_V hV b σ hσ u⟩
      simpa using this
    have hSu : S (σ (lagPhi P b u)) = S u := by
      have h : S (σ (lagPhi P b u)) - S u = 0 := by
        rw [← map_sub]
        exact hzero
      exact sub_eq_zero.mp h
    simp only [Kmap, LinearMap.comp_apply, hSu]
  have hKmap_rel := Kmap_relation hP hV b hΓP hΓV hSL S σ Kmap hKmap_Phi hScomm
  obtain ⟨a', ha'⟩ := exists_scalar_of_commutes_transposeInv hn Kmap hKmap_rel
  refine ⟨a', fun u => ?_⟩
  have hKa : Kmap (lagPhi P b u) = a' • lagPhi P b u := by
    rw [ha']
    rfl
  have h1 : lagPhi P b (S u - a' • u) = 0 := by
    rw [map_sub, map_smul, ← hKmap_Phi u, hKa, sub_self]
  have hmem : S u - a' • u ∈ V := by
    have hker : S u - a' • u ∈ LinearMap.ker (lagPhi P b) := LinearMap.mem_ker.mpr h1
    rwa [lagPhi_ker hV b] at hker
  simpa [S] using hmem

end ScalarModuloLagrangian

section CorrectionVanishes

variable {K U : Type} [Field K] [AddCommGroup U] [Module K U]
  {n : ℕ}

private lemma lagrangian_correction_eq_zero {P : LinearMap.BilinForm K U}
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    {Γ : Set (U ≃ₗ[K] U)}
    (hΓP : ∀ g ∈ Γ, ∀ u w, P (g u) (g w) = P u w)
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (ψ : U →ₗ[K] U) (hψ : ∀ g ∈ Γ, ∀ u, ψ (g u) = g (ψ u))
    {a : K} (ha : ∀ v : V, ψ (v : U) = a • (v : U)) {a' : K}
    (ha' : ∀ u : U, ψ u - a • u - a' • u ∈ V)
    (hN : ∃ g ∈ Γ, (∀ v ∈ V, g v = v) ∧ ∃ u, g u ≠ u) :
    a' = 0 := by
  by_contra h'
  obtain ⟨g, hgΓ, hfixV, u, hgu⟩ := hN
  have hdiff : g u - u ∈ V := by
    rw [← hV, LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    have hgv : g.symm v = v := by
      apply g.injective
      rw [g.apply_symm_apply]
      exact (hfixV v hv).symm
    have h1 : P v (g u) = P (g.symm v) u := by
      have h2 : P v (g u) = P (g (g.symm v)) (g u) := by rw [g.apply_symm_apply]
      rw [h2, hΓP g hgΓ]
    rw [map_sub, h1, hgv, sub_self]
  have hwg : g (ψ u - a • u) = ψ u - a • u := by
    have h1 : ψ (g u) - a • g u = ψ u - a • u := by
      have hdiff' : ψ (g u - u) = a • (g u - u) := ha ⟨g u - u, hdiff⟩
      have hψadd : ψ (g u) = ψ u + ψ (g u - u) := by
        rw [← map_add]
        congr 1
        abel
      rw [hψadd, hdiff', smul_sub]
      abel
    rw [map_sub, map_smul, ← hψ g hgΓ u]
    exact h1
  have hfix := hfixV (ψ u - a • u - a' • u) (ha' u)
  rw [map_sub, map_smul, hwg] at hfix
  have hEq : a' • g u = a' • u := by
    set X : U := ψ u - a • u
    have hX : X - a' • g u = X - a' • u := hfix
    have h2 : X - a' • u + a' • u = X - a' • u + a' • g u := by
      rw [sub_add_cancel, ← hX, sub_add_cancel]
    exact (add_left_cancel h2).symm
  have hgu_eq : g u = u := by
    have hscale := congrArg (fun t => a'⁻¹ • t) hEq
    simpa [smul_smul, inv_mul_cancel₀ h'] using hscale
  exact hgu hgu_eq

end CorrectionVanishes

section DualCoordinates

variable {K U : Type} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {n : ℕ}

private noncomputable def dualCoordMap (S : U →ₗ[K] U) {V : Submodule K U}
    (hSV : ∀ u : U, S u ∈ V) (b : Module.Basis (Fin n) K V)
    (σ : (Fin n → K) →ₗ[K] U) : (Fin n → K) →ₗ[K] (Fin n → K) :=
  b.equivFun.toLinearMap.comp ((S.comp σ).codRestrict V (fun y => hSV (σ y)))

private lemma dualCoordMap_apply (S : U →ₗ[K] U) {V : Submodule K U}
    (hSV : ∀ u : U, S u ∈ V) (b : Module.Basis (Fin n) K V)
    (σ : (Fin n → K) →ₗ[K] U) (y : Fin n → K) :
    dualCoordMap S hSV b σ y = b.equivFun ⟨S (σ y), hSV (σ y)⟩ := by
  have h1 : (S.comp σ).codRestrict V (fun y => hSV (σ y)) y =
      ⟨S (σ y), hSV (σ y)⟩ := by
    apply Subtype.ext
    rfl
  rw [dualCoordMap, LinearMap.comp_apply, h1]
  rfl

private lemma dualCoordMap_apply_lagPhi {P : LinearMap.BilinForm K U}
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) (S : U →ₗ[K] U) (hSV : ∀ u : U, S u ∈ V)
    (σ : (Fin n → K) →ₗ[K] U) (hσ : ∀ y, lagPhi P b (σ y) = y)
    (hSVzero : ∀ v : V, S (v : U) = 0) (u : U) :
    dualCoordMap S hSV b σ (lagPhi P b u) = b.equivFun ⟨S u, hSV u⟩ := by
  have hzero : S (σ (lagPhi P b u) - u) = 0 := by
    have := hSVzero ⟨_, lagRightInverse_sub_mem_V hV b σ hσ u⟩
    simpa using this
  have hSu : S (σ (lagPhi P b u)) = S u := by
    have h : S (σ (lagPhi P b u)) - S u = 0 := by
      rw [← map_sub]
      exact hzero
    exact sub_eq_zero.mp h
  rw [dualCoordMap_apply]
  apply congrArg b.equivFun
  apply Subtype.ext
  exact hSu

private lemma dualCoordMap_relation {P : LinearMap.BilinForm K U} (hP : P.Nondegenerate)
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) {Γ : Set (U ≃ₗ[K] U)}
    (hΓP : ∀ g ∈ Γ, ∀ u w, P (g u) (g w) = P u w)
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (S : U →ₗ[K] U) (hSV : ∀ u : U, S u ∈ V)
    (σ : (Fin n → K) →ₗ[K] U) (hσ : ∀ y, lagPhi P b (σ y) = y)
    (hSVzero : ∀ v : V, S (v : U) = 0)
    (hScomm : ∀ g ∈ Γ, ∀ u, S (g u) = g (S u)) :
    ∀ (A : Matrix.SpecialLinearGroup (Fin n) K) (y : Fin n → K),
      dualCoordMap S hSV b σ ((↑(A⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ y) =
        (A : Matrix (Fin n) (Fin n) K) *ᵥ dualCoordMap S hSV b σ y := by
  intro A y
  obtain ⟨u, rfl⟩ := lagPhi_surjective hP hV b y
  obtain ⟨g, hgΓ, hg⟩ := hSL A
  have hgV : ∀ v ∈ V, g v ∈ V := fun v hv => hΓV g hgΓ v hv
  have hσS : S (σ (lagPhi P b (g u))) = S (g u) := by
    have hzero : S (σ (lagPhi P b (g u)) - g u) = 0 := by
      have := hSVzero ⟨_, lagRightInverse_sub_mem_V hV b σ hσ (g u)⟩
      simpa using this
    have h : S (σ (lagPhi P b (g u))) - S (g u) = 0 := by
      rw [← map_sub]
      exact hzero
    exact sub_eq_zero.mp h
  have hcSu : b.equivFun ⟨g (S u), hgV (S u) (hSV u)⟩ =
      (A : Matrix (Fin n) (Fin n) K) *ᵥ b.equivFun ⟨S u, hSV u⟩ :=
    equivFun_comp_of_basis hgV hg ⟨S u, hSV u⟩
  have hPhi : lagPhi P b (g u) =
      (↑(A⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ lagPhi P b u :=
    lagPhi_comp_iso hgV hg (hΓP g hgΓ) u
  calc dualCoordMap S hSV b σ ((↑(A⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ lagPhi P b u)
      = dualCoordMap S hSV b σ (lagPhi P b (g u)) := by rw [← hPhi]
    _ = b.equivFun ⟨S (g u), hSV (g u)⟩ :=
        dualCoordMap_apply_lagPhi hV b S hSV σ hσ hSVzero (g u)
    _ = b.equivFun ⟨g (S u), hgV (S u) (hSV u)⟩ := by
        apply congrArg b.equivFun
        apply Subtype.ext
        exact hScomm g hgΓ u
    _ = (A : Matrix (Fin n) (Fin n) K) *ᵥ b.equivFun ⟨S u, hSV u⟩ := hcSu
    _ = (A : Matrix (Fin n) (Fin n) K) *ᵥ dualCoordMap S hSV b σ (lagPhi P b u) := by
        rw [dualCoordMap_apply_lagPhi hV b S hSV σ hσ hSVzero u]

private lemma dualCoordMap_standard (S : U →ₗ[K] U) {V : Submodule K U}
    (hSV : ∀ u : U, S u ∈ V) (b : Module.Basis (Fin n) K V)
    (σ : (Fin n → K) →ₗ[K] U)
    (hrel : ∀ (A : Matrix.SpecialLinearGroup (Fin n) K) (y : Fin n → K),
      dualCoordMap S hSV b σ ((↑(A⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ y) =
        (A : Matrix (Fin n) (Fin n) K) *ᵥ dualCoordMap S hSV b σ y) :
    ∀ (B : Matrix.SpecialLinearGroup (Fin n) K) (y : Fin n → K),
      dualCoordMap S hSV b σ ((B : Matrix (Fin n) (Fin n) K) *ᵥ y) =
        (↑(B⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ dualCoordMap S hSV b σ y := by
  intro B y
  obtain ⟨A, hA, hAeq⟩ := transpose_inv_surjective B
  have hB : (↑(A⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ = (B : Matrix (Fin n) (Fin n) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_transpose, hA]
  have hAmat : (A : Matrix (Fin n) (Fin n) K) =
      (↑(B⁻¹) : Matrix (Fin n) (Fin n) K)ᵀ := by
    rw [hAeq, Matrix.SpecialLinearGroup.coe_transpose]
  rw [← hB, hrel A y, hAmat]

private lemma S_eq_zero_of_dualCoordMap_eq_zero {P : LinearMap.BilinForm K U}
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) (S : U →ₗ[K] U) (hSV : ∀ u : U, S u ∈ V)
    (σ : (Fin n → K) →ₗ[K] U) (hσ : ∀ y, lagPhi P b (σ y) = y)
    (hSVzero : ∀ v : V, S (v : U) = 0)
    (hzero : dualCoordMap S hSV b σ = 0) : S = 0 := by
  have hSσ : ∀ y : Fin n → K, S (σ y) = 0 := by
    intro y
    have h0 : dualCoordMap S hSV b σ y = 0 := by rw [hzero]; rfl
    have h0' : b.equivFun ⟨S (σ y), hSV (σ y)⟩ = 0 := by
      rwa [dualCoordMap_apply] at h0
    have hV0 : (⟨S (σ y), hSV (σ y)⟩ : V) = 0 :=
      b.equivFun.injective (by simpa using h0')
    simpa using congrArg Subtype.val hV0
  apply LinearMap.ext
  intro u
  have hz : S (σ (lagPhi P b u)) = 0 := hSσ _
  have hz' : S (σ (lagPhi P b u) - u) = 0 := by
    have := hSVzero ⟨_, lagRightInverse_sub_mem_V hV b σ hσ u⟩
    simpa using this
  have harg : σ (lagPhi P b u) - (σ (lagPhi P b u) - u) = u := by abel
  have h1 : S (σ (lagPhi P b u) - (σ (lagPhi P b u) - u)) = 0 := by
    rw [map_sub, hz, hz', sub_zero]
  rw [← harg]
  simpa using h1

private lemma psi_sub_scalar_eq_zero {P : LinearMap.BilinForm K U} (hP : P.Nondegenerate)
    {V : Submodule K U} (hV : LinearMap.BilinForm.orthogonal P V = V)
    (b : Module.Basis (Fin n) K V) {Γ : Set (U ≃ₗ[K] U)}
    (hΓP : ∀ g ∈ Γ, ∀ u w, P (g u) (g w) = P u w)
    (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (ψ : U →ₗ[K] U) (hψ : ∀ g ∈ Γ, ∀ u, ψ (g u) = g (ψ u))
    {a : K} (ha : ∀ v : V, ψ (v : U) = a • (v : U))
    (hSVU : ∀ u : U, ψ u - a • u ∈ V) (hn : 3 ≤ n) :
    ψ = a • LinearMap.id := by
  let S : U →ₗ[K] U := ψ - a • LinearMap.id
  have hSVzero : ∀ v : V, S (v : U) = 0 := by
    intro v
    simp [S, ha v]
  have hSV : ∀ u : U, S u ∈ V := by
    intro u
    simpa [S] using hSVU u
  have hScomm : ∀ g ∈ Γ, ∀ u, S (g u) = g (S u) := by
    intro g hg u
    simp only [S, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hψ g hg u, map_sub, map_smul]
  obtain ⟨σ, hσ⟩ := exists_lagRightInverse hP hV b
  have hrel := dualCoordMap_relation hP hV b hΓP hΓV hSL S hSV σ hσ hSVzero hScomm
  have hstd := dualCoordMap_standard S hSV b σ hrel
  have hzero : dualCoordMap S hSV b σ = 0 :=
    eq_zero_of_natural_dual_hom hn (dualCoordMap S hSV b σ) hstd
  have hS0 : S = 0 := S_eq_zero_of_dualCoordMap_eq_zero hV b S hSV σ hσ hSVzero hzero
  apply LinearMap.ext
  intro u
  have h : ψ u - a • u = 0 := by simpa [S] using LinearMap.congr_fun hS0 u
  exact sub_eq_zero.mp h

end DualCoordinates

section Main

variable {K U : Type} [Field K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  {n : ℕ}

theorem eq_smul_of_commute_of_lagrangian (hn : 3 ≤ n) (P : LinearMap.BilinForm K U)
    (hP : P.Nondegenerate) (V : Submodule K U)
    (hV : LinearMap.BilinForm.orthogonal P V = V) (b : Module.Basis (Fin n) K V)
    (Γ : Set (U ≃ₗ[K] U))
    (hΓP : ∀ g ∈ Γ, ∀ u w, P (g u) (g w) = P u w) (hΓV : ∀ g ∈ Γ, ∀ v ∈ V, g v ∈ V)
    (hSL : ∀ A : Matrix.SpecialLinearGroup (Fin n) K, ∃ g ∈ Γ,
      ∀ j, g (b j) = ∑ i, (A : Matrix (Fin n) (Fin n) K) i j • (b i : U))
    (hN : ∃ g ∈ Γ, (∀ v ∈ V, g v = v) ∧ ∃ u, g u ≠ u)
    (ψ : U →ₗ[K] U) (hψ : ∀ g ∈ Γ, ∀ u, ψ (g u) = g (ψ u)) :
    ∃ c : K, ψ = c • LinearMap.id := by
  have hψV := psi_maps_V hV b hΓP hΓV hSL ψ hψ hn
  obtain ⟨a, ha⟩ := psi_scalar_on_V b hΓV hSL ψ hψ hψV hn
  obtain ⟨a', ha'⟩ := psi_sub_scalar_mem_V_add hP hV b hΓP hΓV hSL ψ hψ hψV ha hn
  have ha'0 : a' = 0 := lagrangian_correction_eq_zero hV hΓP hΓV ψ hψ ha ha' hN
  have hSVU : ∀ u : U, ψ u - a • u ∈ V := by
    intro u
    have h := ha' u
    rwa [ha'0, zero_smul, sub_zero] at h
  exact ⟨a, psi_sub_scalar_eq_zero hP hV b hΓP hΓV hSL ψ hψ ha hSVU hn⟩

end Main


end CFSG.ClassicalGroups.SpecialLinear

end
