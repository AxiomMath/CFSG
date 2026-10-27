module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.RootGroupSL.FpfArith
public import CFSG.LinearAlgebra.RootGroupSL.NoOuterGraphAux

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open NoOuterGraph

private lemma rog_mulLeftEquiv_symm_apply {k : Type} [Field k] (u : kˣ) (x : k) :
    (mulLeftEquiv k u).symm x = (u : k)⁻¹ * x := by
  change LinearMap.mulLeft k ((u⁻¹ : kˣ) : k) x = (u : k)⁻¹ * x
  rw [LinearMap.mulLeft_apply, Units.val_inv_eq_inv_val]

private lemma rog_mulLeftEquiv_inv_apply {k : Type} [Field k] (u : kˣ) (x : k) :
    ((mulLeftEquiv k u)⁻¹) x = (u : k)⁻¹ * x := by
  change (mulLeftEquiv k u).symm x = (u : k)⁻¹ * x
  rw [rog_mulLeftEquiv_symm_apply]

private lemma rog_det_mulLeftEquiv_self {k : Type} [Field k] (u : kˣ) :
    LinearEquiv.det (mulLeftEquiv k u) = u := by
  have he : ((mulLeftEquiv k u) : k →ₗ[k] k) = LinearMap.mulLeft k (u : k) := rfl
  have h := det_mulLeft_eq_norm (k := k) (E := k) (mulLeftEquiv k u) (u : k) he
  have hnorm : Algebra.norm k (u : k) = (u : k) := by simp [Algebra.norm_self]
  apply Units.ext
  rw [h, hnorm]

theorem false_of_graph_form_rankOne {k : Type} [Field k] [Finite k] [CharP k 2]
    (hk : 3 ≤ Nat.card k) (α : MulAut (SpecialLinearGroup k (DSpace k k)))
    (hR : (rootSL k k k).map α.toMonoidHom = rootSL k k k)
    (hC : ∀ h ∈ Subgroup.normalizer (rootSL k k k : Set (SpecialLinearGroup k (DSpace k k))),
      α h * h⁻¹ ∈ QK k k k)
    (σ : k ≃+* k) (T : Module.Dual k (DSpace k k) ≃+ DSpace k k)
    (hT : ∀ (c : k) (f : Module.Dual k (DSpace k k)), T (c • f) = σ c • T f)
    (hα : ∀ (g : SpecialLinearGroup k (DSpace k k)) (f : Module.Dual k (DSpace k k)),
      α g (T f) = T (f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap)) : False := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hcardk : 3 ≤ Fintype.card k := by simpa [Nat.card_eq_fintype_card] using hk
  have hcard_units : 2 ≤ Fintype.card kˣ := by
    rw [Fintype.card_units]
    omega
  have hlt : 1 < Fintype.card kˣ := by omega
  obtain ⟨s, hs1⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : kˣ)
  let a : k ≃ₗ[k] k := mulLeftEquiv k s
  let g : k ≃ₗ[k] k := mulLeftEquiv k s⁻¹
  have ha : LinearEquiv.det a = s := rog_det_mulLeftEquiv_self s
  have hg : LinearEquiv.det g = s⁻¹ := rog_det_mulLeftEquiv_self s⁻¹
  have hdet : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det (1 : k ≃ₗ[k] k) = 1 := by
    rw [ha, hg, map_one, mul_one, mul_inv_cancel]
  let t : SpecialLinearGroup k (DSpace k k) := blockSL a g 1 hdet
  have htN : t ∈ RootN := by
    rw [blockSL_mem_normalizer_iff]
    intro u
    refine ⟨(s : k) * u, ?_⟩
    apply LinearMap.ext
    intro x
    change (mulLeftEquiv k s) ((LinearMap.mulLeft k u) ((1 : k ≃ₗ[k] k).symm x)) =
      (LinearMap.mulLeft k ((s : k) * u)) x
    rw [mulLeftEquiv_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply]
    rw [show (LinearEquiv.symm (1 : k ≃ₗ[k] k)) x = x from rfl]
    rw [mul_assoc]
  have htriv : ∀ v : DSpace k k,
      (SpecialLinearGroup.toLinearEquiv t) v - v ∈ flagK k k k := by
    intro v
    rw [mem_flagK_iff]
    simp [t, blockSL_apply, blockDiag_apply]
  have hfixW : ∀ w ∈ flagW k k k, α t w = w :=
    fun w hw => action_fixes_flagW_of_trivial_quotient α hR T hα htriv hw
  have htinv : (SpecialLinearGroup.toLinearEquiv t⁻¹) ((1 : k), (0 : k), (0 : k)) =
      (s⁻¹ : k) • ((1 : k), (0 : k), (0 : k)) := by
    rw [map_inv]
    have htcoe : SpecialLinearGroup.toLinearEquiv t = blockDiag a g 1 := rfl
    rw [htcoe, blockDiag_inv, inv_one]
    apply Prod.ext
    · change ((mulLeftEquiv k s)⁻¹) 1 = (s⁻¹ : k) * 1
      rw [rog_mulLeftEquiv_inv_apply]
    · apply Prod.ext
      · change ((mulLeftEquiv k s⁻¹)⁻¹) 0 = (s⁻¹ : k) * 0
        rw [rog_mulLeftEquiv_inv_apply]
        simp
      · change (1 : k ≃ₗ[k] k) 0 = (s⁻¹ : k) * 0
        simp
  have hqk : α t * t⁻¹ ∈ QK k k k := hC t htN
  have hw0 : ((1 : k), (0 : k), (0 : k)) ∈ flagW k k k := by rw [mem_flagW_iff]; simp
  have hfixq : (α t * t⁻¹) ((1 : k), (0 : k), (0 : k)) = ((1 : k), (0 : k), (0 : k)) :=
    (mem_QK_iff.mp hqk).1 _ hw0
  have h1 : (SpecialLinearGroup.toLinearEquiv (α t))
      ((SpecialLinearGroup.toLinearEquiv t⁻¹) ((1 : k), (0 : k), (0 : k))) =
        ((1 : k), (0 : k), (0 : k)) := by
    have h := hfixq
    change (SpecialLinearGroup.toLinearEquiv (α t * t⁻¹)) ((1 : k), (0 : k), (0 : k)) =
      ((1 : k), (0 : k), (0 : k)) at h
    rw [map_mul, LinearEquiv.mul_apply] at h
    exact h
  have h2 : (SpecialLinearGroup.toLinearEquiv (α t))
      ((s⁻¹ : k) • ((1 : k), (0 : k), (0 : k))) = ((1 : k), (0 : k), (0 : k)) := by
    rw [htinv] at h1
    exact h1
  have h3 : (s⁻¹ : k) •
      ((SpecialLinearGroup.toLinearEquiv (α t)) ((1 : k), (0 : k), (0 : k))) =
        ((1 : k), (0 : k), (0 : k)) := by
    rw [LinearEquiv.map_smul] at h2
    exact h2
  have h4 : (s⁻¹ : k) • ((1 : k), (0 : k), (0 : k)) = ((1 : k), (0 : k), (0 : k)) := by
    have hfixW' : (SpecialLinearGroup.toLinearEquiv (α t)) ((1 : k), (0 : k), (0 : k)) =
        ((1 : k), (0 : k), (0 : k)) := hfixW _ hw0
    rw [hfixW'] at h3
    exact h3
  have h5 : (s⁻¹ : k) = 1 := by
    have h := congrArg Prod.fst h4
    simpa using h
  have h6 : s⁻¹ = 1 := Units.ext (by rw [Units.val_inv_eq_inv_val]; exact h5)
  exact hs1 (by rw [← inv_inv s, h6, inv_one])

end CFSG.LinearAlgebra.RootGroupSL
