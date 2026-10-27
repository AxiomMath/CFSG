module

public import CFSG.LinearAlgebra.FrobeniusPowerNormalizer
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.LinearAlgebra

open Module

theorem exists_pairing_adjoint {K W W' : Type*} [Field K] [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W'] [FiniteDimensional K W] [FiniteDimensional K W']
    (P : W →ₗ[K] W' →ₗ[K] K) (hl : ∀ w, (∀ w', P w w' = 0) → w = 0)
    (hr : ∀ w', (∀ w, P w w' = 0) → w' = 0) (φ : W ≃ₗ[K] W) :
    ∃ ψ : W' ≃ₗ[K] W', ∀ w w', P (φ w) (ψ w') = P w w' := by
  let e : W' →ₗ[K] Module.Dual K W := P.flip
  have he_inj : Function.Injective e := by
    intro w₁ w₂ h
    have hzero : e (w₁ - w₂) = 0 := by
      rw [map_sub, h, sub_self]
    have hforall : ∀ w, P w (w₁ - w₂) = 0 := by
      intro w
      have hw : (e (w₁ - w₂)) w = 0 := by
        rw [hzero]
        rfl
      simpa [e, LinearMap.flip_apply] using hw
    have hsub := hr (w₁ - w₂) hforall
    exact sub_eq_zero.mp hsub
  have hP_inj : Function.Injective P := by
    intro w₁ w₂ h
    have hzero : P (w₁ - w₂) = 0 := by
      rw [map_sub, h, sub_self]
    have hforall : ∀ w', P (w₁ - w₂) w' = 0 := by
      intro w'
      have hw : (P (w₁ - w₂)) w' = 0 := by
        rw [hzero]
        rfl
      exact hw
    have hsub := hl (w₁ - w₂) hforall
    exact sub_eq_zero.mp hsub
  have hdim_le1 : finrank K W ≤ finrank K W' := by
    have h := LinearMap.finrank_le_finrank_of_injective hP_inj
    rwa [Subspace.dual_finrank_eq] at h
  have hdim_le2 : finrank K W' ≤ finrank K W := by
    have h := LinearMap.finrank_le_finrank_of_injective he_inj
    rwa [Subspace.dual_finrank_eq] at h
  have hdim : finrank K W = finrank K W' := le_antisymm hdim_le1 hdim_le2
  have he_surj : Function.Surjective e := by
    have h : finrank K W' = finrank K (Module.Dual K W) := by
      rw [Subspace.dual_finrank_eq]
      exact hdim.symm
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mp he_inj
  let e_equiv : W' ≃ₗ[K] Module.Dual K W := LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩
  let ψ : W' ≃ₗ[K] W' := e_equiv.trans ((φ.symm.dualMap).trans e_equiv.symm)
  refine ⟨ψ, fun w w' => ?_⟩
  have h1 : P (φ w) (ψ w') = (e (ψ w')) (φ w) := by
    simp [e, LinearMap.flip_apply]
  rw [h1]
  have h2 : e (ψ w') = φ.symm.dualMap (e_equiv w') := by
    have hψ : ψ w' = e_equiv.symm (φ.symm.dualMap (e_equiv w')) := by
      simp [ψ, LinearEquiv.trans_apply]
    rw [hψ]
    change e_equiv (e_equiv.symm (φ.symm.dualMap (e_equiv w'))) =
      φ.symm.dualMap (e_equiv w')
    rw [LinearEquiv.apply_symm_apply]
  rw [h2]
  rw [LinearEquiv.dualMap_apply]
  rw [LinearEquiv.symm_apply_apply]
  change (e w') w = P w w'
  rw [LinearMap.flip_apply]

theorem pairing_adjoint_comm {K W W' : Type*} [Field K] [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W'] (P : W →ₗ[K] W' →ₗ[K] K)
    (hr : ∀ w', (∀ w, P w w' = 0) → w' = 0) (φ : W ≃ₗ[K] W) (ψ : W' →ₗ[K] W')
    (hψ : ∀ w w', P (φ w) (ψ w') = P w w') (a c : W ≃ₗ[K] W) (a' c' : W' →ₗ[K] W')
    (ha : ∀ w w', P (a w) (a' w') = P w w') (hc : ∀ w w', P (c w) (c' w') = P w w')
    (hφ : ∀ w, φ (a w) = c (φ w)) : ∀ w', ψ (a' w') = c' (ψ w') := by
  intro w'
  have h : ∀ z, P z (ψ (a' w')) = P z (c' (ψ w')) := by
    intro z
    obtain ⟨u, rfl⟩ := φ.surjective z
    have h1 : φ (a (a.symm u)) = c (φ (a.symm u)) := hφ (a.symm u)
    rw [LinearEquiv.apply_symm_apply] at h1
    have h2 : c.symm (φ u) = φ (a.symm u) := by
      rw [h1, LinearEquiv.symm_apply_apply]
    calc
      P (φ u) (ψ (a' w')) = P u (a' w') := hψ u (a' w')
      _ = P (a (a.symm u)) (a' w') := by rw [LinearEquiv.apply_symm_apply]
      _ = P (a.symm u) w' := ha (a.symm u) w'
      _ = P (φ (a.symm u)) (ψ w') := (hψ (a.symm u) w').symm
      _ = P (c.symm (φ u)) (ψ w') := by rw [h2]
      _ = P (c (c.symm (φ u))) (c' (ψ w')) := (hc (c.symm (φ u)) (ψ w')).symm
      _ = P (φ u) (c' (ψ w')) := by rw [LinearEquiv.apply_symm_apply]
  apply sub_eq_zero.mp
  apply hr (ψ (a' w') - c' (ψ w'))
  intro z
  rw [map_sub, h z, sub_self]

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

namespace FrobeniusIsometryPair

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
theorem ker_left_eq_bot (B : LinearMap.BilinForm K V)
    (hsymm : ∀ v w, B v w = B w v) {E : Subgroup (V ≃ₗ[K] V)}
    (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) (W W' : Submodule K V)
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W) (hW'E : ∀ x ∈ E, ∀ v ∈ W', x v ∈ W')
    (hminW : ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W)
    (hpair : ∃ v ∈ W, ∃ w ∈ W', B v w ≠ 0) :
    W ⊓ B.orthogonal W' = ⊥ := by
  have hLW : W ⊓ B.orthogonal W' ≤ W := inf_le_left
  have hLE : ∀ x ∈ E, ∀ v ∈ W ⊓ B.orthogonal W', x v ∈ W ⊓ B.orthogonal W' := by
    intro x hx v hv
    rw [Submodule.mem_inf] at hv ⊢
    constructor
    · exact hWE x hx v hv.1
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      have hxinv : x⁻¹ ∈ E := inv_mem hx
      have hxinvW' : (x⁻¹) w ∈ W' := hW'E x⁻¹ hxinv w hw
      change x.symm w ∈ W' at hxinvW'
      have h := hiso x hx ((x⁻¹) w) v
      change (B (x (x.symm w))) (x v) = (B (x.symm w)) v at h
      rw [LinearEquiv.apply_symm_apply] at h
      rw [h]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hv.2) (x.symm w) hxinvW'
  have hLne : W ⊓ B.orthogonal W' ≠ W := by
    intro hEq
    obtain ⟨v, hvW, w, hwW', hBvw⟩ := hpair
    have hvL : v ∈ W ⊓ B.orthogonal W' := by
      rw [hEq]
      exact hvW
    rw [Submodule.mem_inf] at hvL
    have hBwv : B w v = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvL.2) w hwW'
    exact hBvw (by rw [hsymm v w, hBwv])
  rcases hminW (W ⊓ B.orthogonal W') hLW hLE with h | h
  · exact h
  · exact absurd h hLne

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
theorem ker_right_eq_bot (B : LinearMap.BilinForm K V)
    {E : Subgroup (V ≃ₗ[K] V)}
    (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) (W W' : Submodule K V)
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W) (hW'E : ∀ x ∈ E, ∀ v ∈ W', x v ∈ W')
    (hminW' : ∀ U : Submodule K V, U ≤ W' → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W')
    (hpair : ∃ v ∈ W, ∃ w ∈ W', B v w ≠ 0) :
    W' ⊓ B.orthogonal W = ⊥ := by
  have hL'W : W' ⊓ B.orthogonal W ≤ W' := inf_le_left
  have hL'E : ∀ x ∈ E, ∀ v ∈ W' ⊓ B.orthogonal W, x v ∈ W' ⊓ B.orthogonal W := by
    intro x hx v hv
    rw [Submodule.mem_inf] at hv ⊢
    constructor
    · exact hW'E x hx v hv.1
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      have hxinv : x⁻¹ ∈ E := inv_mem hx
      have hxinvW : (x⁻¹) w ∈ W := hWE x⁻¹ hxinv w hw
      change x.symm w ∈ W at hxinvW
      have h := hiso x hx ((x⁻¹) w) v
      change (B (x (x.symm w))) (x v) = (B (x.symm w)) v at h
      rw [LinearEquiv.apply_symm_apply] at h
      rw [h]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hv.2) (x.symm w) hxinvW
  have hL'ne : W' ⊓ B.orthogonal W ≠ W' := by
    intro hEq
    obtain ⟨v, hvW, w, hwW', hBvw⟩ := hpair
    have hwL : w ∈ W' ⊓ B.orthogonal W := by
      rw [hEq]
      exact hwW'
    rw [Submodule.mem_inf] at hwL
    exact hBvw ((LinearMap.BilinForm.mem_orthogonal_iff.mp hwL.2) v hvW)
  rcases hminW' (W' ⊓ B.orthogonal W) hL'W hL'E with h | h
  · exact h
  · exact absurd h hL'ne

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
theorem inf_eq_bot (B : LinearMap.BilinForm K V) (W W' : Submodule K V)
    {E : Subgroup (V ≃ₗ[K] V)}
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W) (hW'E : ∀ x ∈ E, ∀ v ∈ W', x v ∈ W')
    (hminW : ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W)
    (hiW' : ∀ v ∈ W', ∀ w ∈ W', B v w = 0)
    (hpair : ∃ v ∈ W, ∃ w ∈ W', B v w ≠ 0) :
    W ⊓ W' = ⊥ := by
  have hIW : W ⊓ W' ≤ W := inf_le_left
  have hIE : ∀ x ∈ E, ∀ v ∈ W ⊓ W', x v ∈ W ⊓ W' := by
    intro x hx v hv
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨hWE x hx v hv.1, hW'E x hx v hv.2⟩
  have hIne : W ⊓ W' ≠ W := by
    intro hEq
    obtain ⟨v, hvW, w, hwW', hBvw⟩ := hpair
    have hvW' : v ∈ W' := by
      have hvI : v ∈ W ⊓ W' := by
        rw [hEq]
        exact hvW
      exact (Submodule.mem_inf.mp hvI).2
    exact hBvw (hiW' v hvW' w hwW')
  rcases hminW (W ⊓ W') hIW hIE with h | h
  · exact h
  · exact absurd h hIne

omit [Fintype K] [CharP K 2] in
theorem restrict_nondegenerate (B : LinearMap.BilinForm K V)
    (hsymm : ∀ v w, B v w = B w v) (W W' : Submodule K V)
    (hiW : ∀ v ∈ W, ∀ w ∈ W, B v w = 0) (hiW' : ∀ v ∈ W', ∀ w ∈ W', B v w = 0)
    (hkerL : W ⊓ B.orthogonal W' = ⊥)
    (hkerR : W' ⊓ B.orthogonal W = ⊥) :
    (B.restrict (W ⊔ W')).Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx0 : (B.restrict (W ⊔ W')) x = 0 := LinearMap.mem_ker.mp hx
  obtain ⟨v, hvW, w, hwW', hvw⟩ := Submodule.mem_sup.mp x.2
  have hwL : w ∈ W' ⊓ B.orthogonal W := by
    rw [Submodule.mem_inf]
    constructor
    · exact hwW'
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hzW
      have hzU : z ∈ W ⊔ W' := Submodule.mem_sup_left hzW
      have hz : (B.restrict (W ⊔ W')) x ⟨z, hzU⟩ = 0 := by
        rw [hx0]
        rfl
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at hz
      rw [← hvw] at hz
      rw [map_add, LinearMap.add_apply] at hz
      rw [hiW v hvW z hzW, zero_add] at hz
      rw [hsymm w z] at hz
      exact hz
  have hw0 : w = 0 := by
    have hwbot : w ∈ (⊥ : Submodule K V) := by
      rw [← hkerR]
      exact hwL
    exact (Submodule.mem_bot (R := K) (M := V) (x := w)).mp hwbot
  have hvL : v ∈ W ⊓ B.orthogonal W' := by
    rw [Submodule.mem_inf]
    constructor
    · exact hvW
    · rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro z hzW'
      have hzU : z ∈ W ⊔ W' := Submodule.mem_sup_right hzW'
      have hz : (B.restrict (W ⊔ W')) x ⟨z, hzU⟩ = 0 := by
        rw [hx0]
        rfl
      rw [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] at hz
      rw [← hvw] at hz
      rw [map_add, LinearMap.add_apply] at hz
      rw [hiW' w hwW' z hzW', add_zero] at hz
      rw [hsymm v z] at hz
      exact hz
  have hv0 : v = 0 := by
    have hvbot : v ∈ (⊥ : Submodule K V) := by
      rw [← hkerL]
      exact hvL
    exact (Submodule.mem_bot (R := K) (M := V) (x := v)).mp hvbot
  have hx0' : x.1 = 0 := by
    rw [← hvw, hv0, hw0, add_zero]
  exact Subtype.ext hx0'

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
theorem map_eq_self_of_mem {E : Subgroup (V ≃ₗ[K] V)} {W : Submodule K V}
    {x : V ≃ₗ[K] V} (hx : x ∈ E)
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W) :
    W.map (x : V →ₗ[K] V) = W := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact hWE x hx v hv
  · intro v hv
    rw [Submodule.mem_map]
    refine ⟨x.symm v, ?_, ?_⟩
    · have hxinv : x⁻¹ ∈ E := inv_mem hx
      have h := hWE x⁻¹ hxinv v hv
      simpa using h
    · exact LinearEquiv.apply_symm_apply x v

def restrictHom {E : Subgroup (V ≃ₗ[K] V)} {W : Submodule K V}
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W) : E →* (W ≃ₗ[K] W) where
  toFun x := x.1.ofSubmodules W W (map_eq_self_of_mem (x := x.1) x.2 hWE)
  map_one' := by
    ext w
    simp [LinearEquiv.ofSubmodules_apply]
  map_mul' x y := by
    ext w
    simp [LinearEquiv.ofSubmodules_apply]

theorem exists_frobenius_normalizer_on_W {E : Subgroup (V ≃ₗ[K] V)} [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
    (W : Submodule K V) (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W) :
    ∃ φ : W ≃ₗ[K] W, ∀ (x : V ≃ₗ[K] V) (hx : x ∈ E) (v : W),
      (φ ⟨x v, hWE x hx v v.2⟩ : V) = (x ^ Fintype.card K) (φ v : V) := by
  let ρ : E →* (W ≃ₗ[K] W) := restrictHom hWE
  let E_W : Subgroup (W ≃ₗ[K] W) := ρ.range
  have : Finite E_W := Finite.of_surjective
    (fun x : E => (⟨ρ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : E_W))
    (by
      intro y
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
      exact ⟨x, Subtype.ext hx⟩)
  have hcomm_W : ∀ y ∈ E_W, ∀ z ∈ E_W, y * z = z * y := by
    intro y hy z hz
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨x', rfl⟩ := MonoidHom.mem_range.mp hz
    have hcommE : x * x' = x' * x := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hcomm x x.2 x' x'.2
    simpa only [map_mul] using congrArg ρ hcommE
  have hodd_W : Odd (Nat.card E_W) := Odd.of_dvd_nat hodd (Subgroup.card_range_dvd ρ)
  have hcard_W : (Nat.card E_W : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ Nat.card E_W := (CharP.cast_eq_zero_iff K 2 (Nat.card E_W)).mp h
    exact (Nat.not_even_iff_odd.mpr hodd_W) (even_iff_two_dvd.mpr h2)
  obtain ⟨φ, hφ, _⟩ := CFSG.LinearAlgebra.exists_conj_eq_pow_card (K := K) (V := W)
    (E := E_W) hcomm_W hcard_W (δ := 1) one_ne_zero
  refine ⟨φ, ?_⟩
  intro x hx v
  let y : W ≃ₗ[K] W := ρ ⟨x, hx⟩
  have hy : y ∈ E_W := MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
  have h := (LinearEquiv.ext_iff.mp (hφ y hy)) (φ v)
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  change φ (y (φ.symm (φ v))) = (y ^ Fintype.card K) (φ v) at h
  rw [LinearEquiv.symm_apply_apply] at h
  have hyv : (y v : V) = x v :=
    LinearEquiv.ofSubmodules_apply (e := x) (p := W) (q := W)
      (map_eq_self_of_mem (x := x) hx hWE) v
  have hyq : ((y ^ Fintype.card K) (φ v) : V) = (x ^ Fintype.card K) (φ v : V) := by
    have hmap : y ^ Fintype.card K =
        ρ ⟨x ^ Fintype.card K, pow_mem hx (Fintype.card K)⟩ := by
      rw [show y = ρ ⟨x, hx⟩ from rfl, ← map_pow]
      rfl
    rw [hmap]
    exact LinearEquiv.ofSubmodules_apply (e := x ^ Fintype.card K) (p := W) (q := W)
      (map_eq_self_of_mem (x := x ^ Fintype.card K) (pow_mem hx _) hWE) (φ v)
  have hφv : (φ (y v) : V) = (x ^ Fintype.card K) (φ v : V) := by
    rw [congrArg Subtype.val h, hyq]
  have hyveq : y v = ⟨x v, hWE x hx v v.2⟩ := Subtype.ext hyv
  rw [← hyveq]
  exact hφv

end FrobeniusIsometryPair

open FrobeniusIsometryPair in
theorem exists_isometry_pow_card_of_pair (B : LinearMap.BilinForm K V)
    (hsymm : ∀ v w, B v w = B w v) {E : Subgroup (V ≃ₗ[K] V)} [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
    (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) (W W' : Submodule K V)
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W) (hW'E : ∀ x ∈ E, ∀ v ∈ W', x v ∈ W')
    (hminW : ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W)
    (hminW' : ∀ U : Submodule K V, U ≤ W' → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W')
    (hiW : ∀ v ∈ W, ∀ w ∈ W, B v w = 0) (hiW' : ∀ v ∈ W', ∀ w ∈ W', B v w = 0)
    (hpair : ∃ v ∈ W, ∃ w ∈ W', B v w ≠ 0) :
    (B.restrict (W ⊔ W')).Nondegenerate ∧
      ∃ g : V →ₗ[K] V, (∀ v ∈ W ⊔ W', g v ∈ W ⊔ W') ∧
        (∀ v ∈ B.orthogonal (W ⊔ W'), g v = v) ∧
        (∀ v ∈ W ⊔ W', ∀ w ∈ W ⊔ W', B (g v) (g w) = B v w) ∧
        ∀ x ∈ E, ∀ v ∈ W ⊔ W', g (x v) = (x ^ Fintype.card K) (g v) := by
  classical
  have hkerL := ker_left_eq_bot B hsymm hiso W W' hWE hW'E hminW hpair
  have hkerR := ker_right_eq_bot B hiso W W' hWE hW'E hminW' hpair
  have hWW' := inf_eq_bot B W W' hWE hW'E hminW hiW' hpair
  have hnd := restrict_nondegenerate B hsymm W W' hiW hiW' hkerL hkerR
  refine ⟨hnd, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_frobenius_normalizer_on_W hcomm hodd W hWE
  let P : W →ₗ[K] W' →ₗ[K] K := B.compl₁₂ W.subtype W'.subtype
  have hP : ∀ (a : W) (b : W'), P a b = B a b := fun _ _ => rfl
  have hl : ∀ a : W, (∀ b : W', P a b = 0) → a = 0 := fun a ha => by
    have hmem : (a : V) ∈ W ⊓ B.orthogonal W' := ⟨a.2, LinearMap.BilinForm.mem_orthogonal_iff.mpr
      fun b hb => by rw [hsymm]; exact ha ⟨b, hb⟩⟩
    rw [hkerL, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hr : ∀ b : W', (∀ a : W, P a b = 0) → b = 0 := fun b hb => by
    have hmem : (b : V) ∈ W' ⊓ B.orthogonal W := ⟨b.2, LinearMap.BilinForm.mem_orthogonal_iff.mpr
      fun a ha => hb ⟨a, ha⟩⟩
    rw [hkerR, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨ψ, hψ⟩ := exists_pairing_adjoint P hl hr φ
  have hψx : ∀ x (hx : x ∈ E) (b : W'), (ψ ⟨x b, hW'E x hx b b.2⟩ : V) =
      (x ^ Fintype.card K) (ψ b : V) := by
    intro x hx b
    let ρ : E →* (W ≃ₗ[K] W) := restrictHom hWE
    let res' : ∀ y ∈ E, W' →ₗ[K] W' := fun y hy =>
      y.toLinearMap.restrict fun v hv => hW'E y hy v hv
    have hres' : ∀ y (hy : y ∈ E) (b : W'), (res' y hy b : V) = y b := fun _ _ _ => rfl
    have hρ : ∀ y (hy : y ∈ E) (a : W), (ρ ⟨y, hy⟩ a : V) = y a := fun y hy a =>
      LinearEquiv.ofSubmodules_apply (e := y) (p := W) (q := W) (map_eq_self_of_mem hy hWE) a
    have hxq : x ^ Fintype.card K ∈ E := pow_mem hx _
    have hφ' : ∀ a : W, φ (ρ ⟨x, hx⟩ a) = ρ ⟨x ^ Fintype.card K, hxq⟩ (φ a) := fun a => by
      apply Subtype.ext
      rw [show ρ ⟨x, hx⟩ a = ⟨x a, hWE x hx a a.2⟩ from Subtype.ext (hρ x hx a), hφ x hx a,
        hρ _ hxq]
    have key := pairing_adjoint_comm P hr φ (ψ : W' →ₗ[K] W') hψ (ρ ⟨x, hx⟩)
      (ρ ⟨x ^ Fintype.card K, hxq⟩) (res' x hx) (res' _ hxq)
      (fun a b => by rw [hP, hρ x hx, hres' x hx, hiso x hx, hP])
      (fun a b => by rw [hP, hρ _ hxq, hres' _ hxq, hiso _ hxq, hP]) hφ' b
    have h2 := congrArg Subtype.val key
    rw [hres' _ hxq] at h2
    exact h2
  set U := W ⊔ W' with hUdef
  let WU : Submodule K U := W.comap U.subtype
  let W'U : Submodule K U := W'.comap U.subtype
  have hWU : IsCompl WU W'U := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro u hu
      have hm : (u : V) ∈ W ⊓ W' := ⟨hu.1, hu.2⟩
      rw [hWW', Submodule.mem_bot] at hm
      rw [Submodule.mem_bot]
      exact Subtype.ext hm
    · rw [codisjoint_iff, eq_top_iff]
      rintro ⟨u, hu⟩ -
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      exact Submodule.mem_sup.mpr ⟨⟨a, le_sup_left (a := W) ha⟩, ha, ⟨b, le_sup_right (b := W') hb⟩,
        hb, rfl⟩
  let eW : WU ≃ₗ[K] W := Submodule.comapSubtypeEquivOfLe le_sup_left
  let eW' : W'U ≃ₗ[K] W' := Submodule.comapSubtypeEquivOfLe le_sup_right
  let e : (WU × W'U) ≃ₗ[K] U := Submodule.prodEquivOfIsCompl WU W'U hWU
  let gU : U ≃ₗ[K] U :=
    e.symm.trans ((((eW.trans φ).trans eW.symm).prodCongr ((eW'.trans ψ).trans eW'.symm)).trans e)
  have hW1 : ∀ a : W, (((eW.symm a : WU) : U) : V) = a := fun a => by
    have h := Submodule.comapSubtypeEquivOfLe_apply_coe (le_sup_left : W ≤ U) (eW.symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hW2 : ∀ b : W', (((eW'.symm b : W'U) : U) : V) = b := fun b => by
    have h := Submodule.comapSubtypeEquivOfLe_apply_coe (le_sup_right : W' ≤ U) (eW'.symm b)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hgU : ∀ (a : W) (b : W'), ((gU ⟨a + b, Submodule.add_mem_sup a.2 b.2⟩ : U) : V) =
      φ a + ψ b := by
    intro a b
    have hab : (⟨a + b, Submodule.add_mem_sup a.2 b.2⟩ : U) =
        e (eW.symm a, eW'.symm b) := by
      apply Subtype.ext
      simp [e, Submodule.coe_prodEquivOfIsCompl', hW1, hW2]
    rw [hab]
    simp only [gU, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply, LinearEquiv.apply_symm_apply]
    simp [e, Submodule.coe_prodEquivOfIsCompl', hW1, hW2]
  have hUc : IsCompl U (B.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (fun x y h => by rw [hsymm]; exact h) hnd
  let g : V →ₗ[K] V := LinearMap.ofIsCompl hUc (U.subtype ∘ₗ (gU : U →ₗ[K] U))
    (B.orthogonal U).subtype
  have hgu : ∀ u : U, g u = ((gU u : U) : V) := fun u => by
    rw [LinearMap.ofIsCompl_apply_left hUc (u := u)]
    rfl
  have hg2 : ∀ (a : W) (b : W'), g (a + b) = φ a + ψ b := fun a b => by
    have := hgu ⟨a + b, Submodule.add_mem_sup a.2 b.2⟩
    rw [hgU] at this
    exact this
  refine ⟨g, fun v hv => ?_, fun v hv => ?_, fun v hv w hw => ?_, fun x hx v hv => ?_⟩
  · rw [show v = ((⟨v, hv⟩ : U) : V) from rfl, hgu]
    exact (gU ⟨v, hv⟩).2
  · rw [LinearMap.ofIsCompl_apply_right hUc (v := ⟨v, hv⟩)]
    rfl
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hw
    rw [show a + b = ((⟨a, ha⟩ : W) : V) + ((⟨b, hb⟩ : W') : V) from rfl,
      show a' + b' = ((⟨a', ha'⟩ : W) : V) + ((⟨b', hb'⟩ : W') : V) from rfl, hg2, hg2]
    simp only [map_add, LinearMap.add_apply]
    rw [hiW _ (φ _).2 _ (φ _).2, hiW' _ (ψ _).2 _ (ψ _).2, hiW _ ha _ ha', hiW' _ hb _ hb']
    have h1 := hψ ⟨a, ha⟩ ⟨b', hb'⟩
    have h2 := hψ ⟨a', ha'⟩ ⟨b, hb⟩
    rw [hP, hP] at h1 h2
    rw [h1, hsymm (ψ _ : V), h2, hsymm b]
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    have hxa := hφ x hx ⟨a, ha⟩
    have hxb := hψx x hx ⟨b, hb⟩
    rw [map_add, show x a + x b = ((⟨x a, hWE x hx a ha⟩ : W) : V) +
      ((⟨x b, hW'E x hx b hb⟩ : W') : V) from rfl, hg2,
      show a + b = ((⟨a, ha⟩ : W) : V) + ((⟨b, hb⟩ : W') : V) from rfl, hg2, map_add]
    rw [hxb]
    congr 1

end CFSG.LinearAlgebra
