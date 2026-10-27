module

public import CFSG.LieType.Chevalley.E7Three.CoordinateActions
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.BasisActions

open CFSG.LieType.Chevalley.E7Three.CoordinateActions CFSG.StandardType

theorem u_basis_zero : u (basis 0) = basis 0 := by decide +kernel
theorem u_basis_one : u (basis 1) = basis 1 * basis 0 ^ 2 := by decide +kernel
theorem u_basis_two : u (basis 2) = basis 2 := by decide +kernel
theorem v_basis_zero : v (basis 0) = basis 0 := by decide +kernel
theorem v_basis_one : v (basis 1) = basis 2 ^ 2 := by decide +kernel
theorem v_basis_two : v (basis 2) = basis 1 := by decide +kernel
theorem w_basis_zero : w (basis 0) = basis 1 ^ 2 := by decide +kernel
theorem w_basis_one : w (basis 1) = basis 0 ^ 2 := by decide +kernel
theorem w_basis_two : w (basis 2) = basis 2 ^ 2 := by decide +kernel

theorem hom_eq_of_basis {G : Type*} [Group G] (f g : D →* G)
    (h : ∀ i, f (basis i) = g (basis i)) : f = g := by
  ext d
  rw [basis_repr d]
  simp only [map_mul, map_pow, h]

theorem congr_eq_conjAut_of_basis {G : Type} [Group G] (E : Subgroup G)
    (e : D ≃* E) (φ : MulAut D) (n : G)
    (hn : n ∈ Subgroup.normalizer (E : Set G))
    (h : ∀ i, n * (e (basis i) : G) * n⁻¹ = (e (φ (basis i)) : G)) :
    MulAut.congr e φ = ggConjAut E hn := by
  let φE : MulAut E := MulAut.congr e φ
  let ψ : MulAut E := ggConjAut E hn
  have heq : φE.toMonoidHom.comp e.toMonoidHom = ψ.toMonoidHom.comp e.toMonoidHom := by
    apply hom_eq_of_basis
    intro i
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, φE, ψ, MulAut.congr_apply,
      MulEquiv.trans_apply, e.symm_apply_apply, ggConjAut_apply]
    exact (h i).symm
  have hφ : φE = ψ := by
    ext b : 1
    obtain ⟨d, rfl⟩ := e.surjective b
    exact DFunLike.congr_fun heq d
  exact hφ

theorem mem_automizer_of_conj_basis {G : Type} [Group G] (E : Subgroup G)
    (e : D ≃* E) (φ : MulAut D) (n : G)
    (hn : n ∈ Subgroup.normalizer (E : Set G))
    (h : ∀ i, n * (e (basis i) : G) * n⁻¹ = (e (φ (basis i)) : G)) :
    MulAut.congr e φ ∈ ggAutomizer (⊤ : Subgroup G) E := by
  rw [congr_eq_conjAut_of_basis E e φ n hn h]
  exact Subgroup.subset_closure (ggConjAut_mem_ggInduced (show n ∈ (⊤ : Subgroup G) by trivial) hn)

end CFSG.LieType.Chevalley.E7Three.BasisActions
