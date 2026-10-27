module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianBasis

public section

namespace CFSG.ComponentClassification.CatalogueBHermitian

noncomputable section

universe u v w

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {sigma : K ≃+* K} (h : V →ₛₗ[sigma.toRingHom] V →ₗ[K] K)

theorem sum_left {ι : Type*} (s : Finset ι) (x : ι → V) (y : V) :
    h (∑ i ∈ s, x i) y = ∑ i ∈ s, h (x i) y := by
  rw [map_sum, LinearMap.sum_apply]

theorem form_eq_herm_coordinates {n : ℕ} (b : Module.Basis (Fin n) K V)
    (hb : ∀ i j, h (b i) (b j) = if i = j then 1 else 0) (x y : V) :
    h x y = CFSG.ClassicalGroups.Unitary.herm sigma (b.equivFun x) (b.equivFun y) := by
  classical
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  rw [sum_left]
  simp only [map_sum, smul_left, map_smul, smul_eq_mul, hb]
  simp [CFSG.ClassicalGroups.Unitary.herm_def, Module.Basis.equivFun_apply,
    mul_comm]

theorem exists_coordinate_isometry [Finite K] [FiniteDimensional K V]
    (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) :
    ∃ e : V ≃ₗ[K] (Fin (Module.finrank K V) → K),
      ∀ x y, CFSG.ClassicalGroups.Unitary.herm sigma (e x) (e y) = h x y := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis h hsym hnd hsigma hne
  exact ⟨b.equivFun, fun x y => (form_eq_herm_coordinates h b hb x y).symm⟩

variable {W : Type w} [AddCommGroup W] [Module K W]

theorem exists_isometry [Finite K] [FiniteDimensional K V] [FiniteDimensional K W]
    (g : W →ₛₗ[sigma.toRingHom] W →ₗ[K] K)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (gsym : g.IsSymm) (gnd : g.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1)
    (hdim : Module.finrank K V = Module.finrank K W) :
    ∃ e : V ≃ₗ[K] W, ∀ x y, g (e x) (e y) = h x y := by
  classical
  obtain ⟨bV, hbV⟩ := exists_orthonormal_basis h hsym hnd hsigma hne
  obtain ⟨bW, hbW⟩ := exists_orthonormal_basis g gsym gnd hsigma hne
  let bW' := bW.reindex (finCongr hdim.symm)
  have hbW' : ∀ i j, g (bW' i) (bW' j) = if i = j then 1 else 0 := by
    intro i j
    dsimp only [bW']
    simpa only [Module.Basis.reindex_apply, Equiv.apply_eq_iff_eq] using
      hbW ((finCongr hdim.symm).symm i) ((finCongr hdim.symm).symm j)
  let e := bV.equivFun.trans bW'.equivFun.symm
  refine ⟨e, ?_⟩
  intro x y
  rw [form_eq_herm_coordinates g bW' hbW']
  have hx : bW'.equivFun (e x) = bV.equivFun x := bW'.equivFun.apply_symm_apply _
  have hy : bW'.equivFun (e y) = bV.equivFun y := bW'.equivFun.apply_symm_apply _
  rw [hx, hy, ← form_eq_herm_coordinates h bV hbV]

end

end CFSG.ComponentClassification.CatalogueBHermitian
