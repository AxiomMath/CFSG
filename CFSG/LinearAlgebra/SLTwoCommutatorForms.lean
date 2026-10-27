module

public import CFSG.LinearAlgebra.SymTwoCongruenceInvariant
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.LinearAlgebra

open LinearMap Matrix

private abbrev linSubOne {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (u : E ≃ₗ[K] E) : E →ₗ[K] E := u.toLinearMap - 1

section Basic

variable {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E] [Module K E]

private lemma bilin_comm (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    (a b : E) : B a b = B b a := by
  have h : -B b a = B a b :=
    LinearMap.BilinForm.IsAlt.neg_eq (show B.IsAlt from hBalt) b a
  rw [CharTwo.neg_eq] at h
  exact h.symm

private lemma mem_orthogonal_iff_left (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E} {e : E} :
    (∀ v ∈ V, B e v = 0) ↔ e ∈ B.orthogonal V := by
  constructor
  · intro h v hv
    simpa [bilin_comm B hBalt e v] using h v hv
  · intro h v hv
    have h' := (LinearMap.BilinForm.mem_orthogonal_iff.mp h) v hv
    simpa [bilin_comm B hBalt e v] using h'

private lemma linSubOne_mem_orthogonal (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E}
    {u : E ≃ₗ[K] E} (hu : ∀ e f, B (u e) (u f) = B e f)
    (huV : ∀ v ∈ V, u v = v) (e : E) :
    linSubOne u e ∈ B.orthogonal V := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  rw [bilin_comm B hBalt]
  have h := hu e v
  rw [huV v hv] at h
  rw [linSubOne, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    LinearMap.sub_apply]
  exact sub_eq_zero.mpr h

private lemma linSubOne_comp_linSubOne_mem (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E}
    {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {u : E ≃ₗ[K] E} (hu : ∀ e f, B (u e) (u f) = B e f)
    (huV : ∀ v ∈ V, u v = v) (huτ : ∀ e, u (τ e) = τ (u e)) (e : E) :
    linSubOne u (linSubOne τ e) ∈ V := by
  have hmem : linSubOne u e ∈ B.orthogonal V :=
    linSubOne_mem_orthogonal B hBalt hu huV e
  have hNV' : τ (linSubOne u e) - linSubOne u e ∈ V :=
    hNV (linSubOne u e) ((mem_orthogonal_iff_left B hBalt).mpr hmem)
  have hcomm : linSubOne u (linSubOne τ e) = linSubOne τ (linSubOne u e) := by
    change u (τ e - e) - (τ e - e) = τ (u e - e) - (u e - e)
    rw [map_sub, map_sub, huτ e]
    abel
  rw [hcomm]
  exact hNV'

private lemma linSubOne_comp_linSubOne_eq_zero (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E} {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {u : E ≃ₗ[K] E} (huV : ∀ v ∈ V, u v = v)
    {f : E} (hf : f ∈ B.orthogonal V) :
    linSubOne u (linSubOne τ f) = 0 := by
  have hmem : linSubOne τ f ∈ V :=
    hNV f ((mem_orthogonal_iff_left B hBalt).mpr hf)
  change u (linSubOne τ f) - linSubOne τ f = 0
  rw [huV _ hmem, sub_self]

private lemma eq_sum_of_mem_dual (B : LinearMap.BilinForm K E) {V : Submodule K E}
    (b : Module.Basis (Fin 2) K V) {e : Fin 2 → E}
    (he : ∀ i j, B (e i) (b j) = if i = j then 1 else 0)
    {v : E} (hv : v ∈ V) :
    v = ∑ i, B (e i) v • (b i : E) := by
  let w : V := ⟨v, hv⟩
  have hrepr : ∀ i, B (e i) (w : E) = b.repr w i := by
    intro i
    conv_lhs => rw [← b.sum_repr w]
    push_cast
    rw [map_sum]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    fin_cases i <;> simp [he, Fin.sum_univ_two]
  have hw : w = ∑ i, B (e i) (w : E) • b i := by
    conv_lhs => rw [← b.sum_equivFun w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.equivFun_apply, ← hrepr i]
  simpa using congrArg Subtype.val hw

private lemma sub_sum_smul_mem_orthogonal (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E}
    (b : Module.Basis (Fin 2) K V) {e : Fin 2 → E}
    (he : ∀ i j, B (e i) (b j) = if i = j then 1 else 0) (x : E) :
    x - ∑ j, B x (b j) • (e j) ∈ B.orthogonal V := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro v hv
  rw [bilin_comm B hBalt]
  let w : V := ⟨v, hv⟩
  have hw : v = ∑ k, b.repr w k • (b k : E) := by
    change (w : E) = ∑ k, b.repr w k • (b k : E)
    conv_lhs => rw [← b.sum_repr w]
    push_cast
    rfl
  conv_lhs => rw [hw]
  rw [map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk : B (x - ∑ j, B x (b j) • e j) (b k) = 0 := by
    simp only [map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply]
    fin_cases k <;> simp [he, Fin.sum_univ_two]
  rw [map_smul, hk, smul_zero]

private abbrev formMatrix (B : LinearMap.BilinForm K E) {V : Submodule K E}
    (b : Module.Basis (Fin 2) K V) (τ : E ≃ₗ[K] E) (e : Fin 2 → E) (u : E ≃ₗ[K] E) :
    Matrix (Fin 2) (Fin 2) K :=
  fun i j => B (e i) (linSubOne u (linSubOne τ (e j)))


private lemma linSubOne_symm_comp (u : E ≃ₗ[K] E) (x : E) :
    linSubOne u.symm x = - u.symm (linSubOne u x) := by
  change u.symm x - x = -(u.symm (u x - x))
  rw [map_sub, u.symm_apply_apply, neg_sub]

private lemma linSubOne_comp_linSubOne_adjoint (B : LinearMap.BilinForm K E)
    {τ : E ≃ₗ[K] E} (hτB : ∀ e f, B (τ e) (τ f) = B e f) (hτ2 : ∀ e, τ (τ e) = e)
    {u : E ≃ₗ[K] E} (hu : ∀ e f, B (u e) (u f) = B e f)
    (huτ : ∀ e, u (τ e) = τ (u e)) (x y : E) :
    B x (linSubOne u (linSubOne τ y)) =
      B (linSubOne u.symm (linSubOne τ x)) y := by
  have hNadj : ∀ a b, B a (linSubOne τ b) = B (linSubOne τ a) b := by
    intro a b
    have hτadj : B a (τ b) = B (τ a) b := by
      have h := hτB (τ a) b
      rwa [hτ2 a] at h
    change B a (τ b - b) = B (τ a - a) b
    rw [map_sub, map_sub, LinearMap.sub_apply, hτadj]
  have huadj : ∀ a b, B a (u b) = B (u.symm a) b := by
    intro a b
    simpa using hu (u.symm a) b
  have huτinv : ∀ z, u.symm (τ z) = τ (u.symm z) := by
    intro z
    apply u.injective
    simpa using (huτ (u.symm z)).symm
  have hcomm : linSubOne u.symm (linSubOne τ x) =
      linSubOne τ (u.symm x) - linSubOne τ x := by
    change u.symm (τ x - x) - (τ x - x) =
      τ (u.symm x) - u.symm x - (τ x - x)
    rw [map_sub, huτinv x]
  have hsplit : B x (linSubOne u (linSubOne τ y)) =
      B x (u (linSubOne τ y)) - B x (linSubOne τ y) := by
    change B x (u (linSubOne τ y) - linSubOne τ y) =
      B x (u (linSubOne τ y)) - B x (linSubOne τ y)
    rw [map_sub]
  have h1 : B x (u (linSubOne τ y)) = B (u.symm x) (linSubOne τ y) :=
    huadj x (linSubOne τ y)
  have h2 : B (u.symm x) (linSubOne τ y) =
      B (linSubOne τ (u.symm x)) y := hNadj (u.symm x) y
  have h3 : B x (linSubOne τ y) = B (linSubOne τ x) y := hNadj x y
  have h4 : B (linSubOne u.symm (linSubOne τ x)) y =
      B (linSubOne τ (u.symm x)) y - B (linSubOne τ x) y := by
    rw [hcomm, map_sub, LinearMap.sub_apply]
  rw [hsplit, h1, h3, h2, h4]

private lemma formMatrix_transpose (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    {V : Submodule K E} (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    (hτB : ∀ e f, B (τ e) (τ f) = B e f) (hτ2 : ∀ e, τ (τ e) = e)
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {u : E ≃ₗ[K] E} (hu : ∀ e f, B (u e) (u f) = B e f)
    (huV : ∀ v ∈ V, u v = v) (huτ : ∀ e, u (τ e) = τ (u e))
    {e : Fin 2 → E} (i j : Fin 2) :
    formMatrix B b τ e u i j = formMatrix B b τ e u j i := by
  have hmem : linSubOne u (linSubOne τ (e i)) ∈ V :=
    linSubOne_comp_linSubOne_mem B hBalt hNV hu huV huτ (e i)
  have huVinv : ∀ v ∈ V, u.symm v = v := by
    intro v hv
    apply u.injective
    simpa [huV v hv] using u.apply_symm_apply v
  have hcomm : linSubOne u.symm (linSubOne τ (e i)) =
      linSubOne u (linSubOne τ (e i)) := by
    have h1 : linSubOne u.symm (linSubOne τ (e i)) =
        - u.symm (linSubOne u (linSubOne τ (e i))) :=
      linSubOne_symm_comp u (linSubOne τ (e i))
    have hxx : linSubOne u (linSubOne τ (e i)) +
        linSubOne u (linSubOne τ (e i)) = 0 := by
      have h : (2 : K) • linSubOne u (linSubOne τ (e i)) = 0 := by
        rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2]
        exact zero_smul K _
      simpa [two_smul] using h
    have hneg : - linSubOne u (linSubOne τ (e i)) =
        linSubOne u (linSubOne τ (e i)) :=
      (eq_neg_of_add_eq_zero_right hxx).symm
    rw [h1, huVinv _ hmem, hneg]
  have hsymm : ∀ a b : E, B a b = B b a := by
    intro a b
    have h : -B b a = B a b :=
      LinearMap.BilinForm.IsAlt.neg_eq (show B.IsAlt from hBalt) b a
    rw [CharTwo.neg_eq] at h
    exact h.symm
  have hadj := linSubOne_comp_linSubOne_adjoint B hτB hτ2 hu huτ (e i) (e j)
  calc formMatrix B b τ e u i j
      = B (linSubOne u.symm (linSubOne τ (e i))) (e j) := hadj
    _ = B (linSubOne u (linSubOne τ (e i))) (e j) := by rw [hcomm]
    _ = B (e j) (linSubOne u (linSubOne τ (e i))) := hsymm _ _
    _ = formMatrix B b τ e u j i := rfl


private lemma linSubOne_one (x : E) : linSubOne (1 : E ≃ₗ[K] E) x = 0 := by
  change x - x = 0
  rw [sub_self]

private lemma formMatrix_one (B : LinearMap.BilinForm K E) {V : Submodule K E}
    (b : Module.Basis (Fin 2) K V) (τ : E ≃ₗ[K] E) (e : Fin 2 → E) :
    formMatrix B b τ e (1 : E ≃ₗ[K] E) = 0 := by
  ext i j
  simp [formMatrix, linSubOne_one]

private lemma linSubOne_mul_apply {V : Submodule K E} {τ : E ≃ₗ[K] E}
    {u v : E ≃ₗ[K] E} (huV : ∀ w ∈ V, u w = w)
    (hNv : ∀ x, linSubOne v (linSubOne τ x) ∈ V) (x : E) :
    linSubOne (u * v) (linSubOne τ x) =
      linSubOne u (linSubOne τ x) + linSubOne v (linSubOne τ x) := by
  change (u * v) (linSubOne τ x) - linSubOne τ x =
    (u (linSubOne τ x) - linSubOne τ x) + (v (linSubOne τ x) - linSubOne τ x)
  rw [LinearEquiv.mul_apply]
  have h2 : u (v (linSubOne τ x) - linSubOne τ x) =
      v (linSubOne τ x) - linSubOne τ x := huV _ (hNv x)
  rw [map_sub] at h2
  calc u (v (linSubOne τ x)) - linSubOne τ x
      = (u (v (linSubOne τ x)) - u (linSubOne τ x)) +
        (u (linSubOne τ x) - linSubOne τ x) := by abel
    _ = (v (linSubOne τ x) - linSubOne τ x) +
        (u (linSubOne τ x) - linSubOne τ x) := by rw [h2]
    _ = (u (linSubOne τ x) - linSubOne τ x) +
        (v (linSubOne τ x) - linSubOne τ x) := by rw [add_comm]


private lemma linSubOne_conj {τ : E ≃ₗ[K] E} {u w : E ≃ₗ[K] E}
    (huτ : ∀ e, u (τ e) = τ (u e)) (hwτ : ∀ e, w (τ e) = τ (w e)) (x : E) :
    linSubOne (u * w * u.symm) (linSubOne τ x) =
      u (linSubOne w (linSubOne τ (u.symm x))) := by
  have huinv : ∀ z, u.symm (τ z) = τ (u.symm z) := by
    intro z
    apply u.injective
    simpa using (huτ (u.symm z)).symm
  change (u * w * u.symm) (τ x - x) - (τ x - x) =
    u (w (τ (u.symm x) - u.symm x) - (τ (u.symm x) - u.symm x))
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [map_sub]
  rw [huinv x, huτ, hwτ, huτ, LinearEquiv.apply_symm_apply]


private lemma formMatrix_eq_left (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    {V : Submodule K E} {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {H : Type*} [Group H] {ρ : H →* (E ≃ₗ[K] E)}
    (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {D : Subgroup H} (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    {d : H} (hd : d ∈ D) {x x' y : E}
    (hx : x - x' ∈ B.orthogonal V) :
    B x (linSubOne (ρ d) (linSubOne τ y)) =
      B x' (linSubOne (ρ d) (linSubOne τ y)) := by
  have hmem : linSubOne (ρ d) (linSubOne τ y) ∈ V :=
    linSubOne_comp_linSubOne_mem B hBalt hNV (hρB d) (hDV d hd) (hDτ d hd) y
  have h0 : B (x - x') (linSubOne (ρ d) (linSubOne τ y)) = 0 :=
    ((mem_orthogonal_iff_left B hBalt).mpr hx) _ hmem
  rw [map_sub, LinearMap.sub_apply] at h0
  exact sub_eq_zero.mp h0

private lemma formMatrix_eq_right (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    {V : Submodule K E} {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {H : Type*} [Group H] {ρ : H →* (E ≃ₗ[K] E)}
    {D : Subgroup H} (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    {d : H} (hd : d ∈ D) {x y y' : E}
    (hy : y - y' ∈ B.orthogonal V) :
    B x (linSubOne (ρ d) (linSubOne τ y)) =
      B x (linSubOne (ρ d) (linSubOne τ y')) := by
  have hzero : linSubOne (ρ d) (linSubOne τ (y - y')) = 0 :=
    linSubOne_comp_linSubOne_eq_zero B hBalt hNV (hDV d hd) hy
  have hsub : linSubOne (ρ d) (linSubOne τ y) -
      linSubOne (ρ d) (linSubOne τ y') =
      linSubOne (ρ d) (linSubOne τ (y - y')) := by
    change ρ d (τ y - y) - (τ y - y) - (ρ d (τ y' - y') - (τ y' - y')) =
      ρ d (τ (y - y') - (y - y')) - (τ (y - y') - (y - y'))
    simp only [map_sub]
    abel
  have h0 : B x (linSubOne (ρ d) (linSubOne τ y)) -
      B x (linSubOne (ρ d) (linSubOne τ y')) = 0 := by
    rw [← map_sub, hsub, hzero, map_zero]
  exact sub_eq_zero.mp h0

private lemma formMatrix_congr (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    {V : Submodule K E} {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {H : Type*} [Group H] {ρ : H →* (E ≃ₗ[K] E)}
    (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {D : Subgroup H} (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    {d : H} (hd : d ∈ D) {x x' y y' : E}
    (hx : x - x' ∈ B.orthogonal V) (hy : y - y' ∈ B.orthogonal V) :
    B x (linSubOne (ρ d) (linSubOne τ y)) =
      B x' (linSubOne (ρ d) (linSubOne τ y')) := by
  rw [formMatrix_eq_left B hBalt hNV hρB hDV hDτ hd hx]
  exact formMatrix_eq_right B hBalt hNV hDV hDτ hd hy


private lemma formMatrix_conj_mod (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E} (b : Module.Basis (Fin 2) K V)
    {H : Type*} [Group H] {ρ : H →* (E ≃ₗ[K] E)}
    (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {e : Fin 2 → E} (he : ∀ i j, B (e i) (b j) = if i = j then 1 else 0)
    {r : H} {A : Matrix (Fin 2) (Fin 2) K}
    (hA : ∀ j, ρ r (b j) = ∑ i, A i j • (b i : E)) :
    ∀ a : Fin 2, (ρ r).symm (e a) - ∑ k, A a k • e k ∈ B.orthogonal V := by
  have hdual : ∀ a : Fin 2, ∀ k : Fin 2,
      B ((ρ r).symm (e a)) (b k) = A a k := by
    intro a k
    have h := hρB r ((ρ r).symm (e a)) (b k)
    rw [LinearEquiv.apply_symm_apply] at h
    rw [← h, hA k, map_sum]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    fin_cases a <;> simp [he, Fin.sum_univ_two]
  intro a
  have hsum : ∑ k, B ((ρ r).symm (e a)) (b k) • e k = ∑ k, A a k • e k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hdual a k]
  have h := sub_sum_smul_mem_orthogonal B hBalt b he ((ρ r).symm (e a))
  rwa [hsum] at h

private lemma formMatrix_conj (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    {V : Submodule K E} {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {H : Type*} [Group H] {ρ : H →* (E ≃ₗ[K] E)}
    (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {D : Subgroup H} (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    {Γ : Set H} (hΓτ : ∀ r ∈ Γ, ∀ e, ρ r (τ e) = τ (ρ r e))
    (hΓD : ∀ r ∈ Γ, ∀ d ∈ D, r * d * r⁻¹ ∈ D)
    {b : Module.Basis (Fin 2) K V} {e : Fin 2 → E}
    (he : ∀ i j, B (e i) (b j) = if i = j then 1 else 0)
    {r : H} (hr : r ∈ Γ)
    {A : Matrix (Fin 2) (Fin 2) K}
    (hA : ∀ j, ρ r (b j) = ∑ i, A i j • (b i : E))
    {d : H} (hd : d ∈ D) (i j : Fin 2) :
    formMatrix B b τ e (ρ (r * d * r⁻¹)) i j =
      ∑ k, ∑ l, (A i k * formMatrix B b τ e (ρ d) k l * A j l) := by
  have hρconj : ρ (r * d * r⁻¹) = ρ r * ρ d * (ρ r).symm := by
    rw [map_mul, map_mul, map_inv]
    rfl
  have hisoadj : ∀ a z : E, B a (ρ r z) = B ((ρ r).symm a) z := by
    intro a z
    have h := hρB r ((ρ r).symm a) z
    rwa [LinearEquiv.apply_symm_apply] at h
  have hmod := formMatrix_conj_mod B hBalt b hρB he hA
  have hconj : linSubOne (ρ (r * d * r⁻¹)) (linSubOne τ (e j)) =
      ρ r (linSubOne (ρ d) (linSubOne τ ((ρ r).symm (e j)))) := by
    rw [hρconj]
    exact linSubOne_conj (hΓτ r hr) (hDτ d hd) (e j)
  have hFcongr : B ((ρ r).symm (e i)) (linSubOne (ρ d) (linSubOne τ ((ρ r).symm (e j)))) =
      B (∑ k, A i k • e k)
        (linSubOne (ρ d) (linSubOne τ (∑ l, A j l • e l))) :=
    formMatrix_congr B hBalt hNV hρB hDV hDτ hd (hmod i) (hmod j)
  have hsum : B (∑ k, A i k • e k)
      (linSubOne (ρ d) (linSubOne τ (∑ l, A j l • e l))) =
      ∑ k, ∑ l, (A i k * formMatrix B b τ e (ρ d) k l * A j l) := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, formMatrix,
      smul_eq_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc formMatrix B b τ e (ρ (r * d * r⁻¹)) i j
      = B (e i) (linSubOne (ρ (r * d * r⁻¹)) (linSubOne τ (e j))) := rfl
    _ = B (e i) (ρ r (linSubOne (ρ d) (linSubOne τ ((ρ r).symm (e j))))) := by
        rw [hconj]
    _ = B ((ρ r).symm (e i))
        (linSubOne (ρ d) (linSubOne τ ((ρ r).symm (e j)))) := hisoadj _ _
    _ = B (∑ k, A i k • e k)
        (linSubOne (ρ d) (linSubOne τ (∑ l, A j l • e l))) := hFcongr
    _ = ∑ k, ∑ l, (A i k * formMatrix B b τ e (ρ d) k l * A j l) := hsum


private lemma formMatrix_mul (B : LinearMap.BilinForm K E)
    {V : Submodule K E} (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    {u v : E ≃ₗ[K] E} (huV : ∀ w ∈ V, u w = w)
    (hvN : ∀ x, linSubOne v (linSubOne τ x) ∈ V)
    {e : Fin 2 → E} (i j : Fin 2) :
    formMatrix B b τ e (u * v) i j =
      formMatrix B b τ e u i j + formMatrix B b τ e v i j := by
  simp only [formMatrix]
  rw [linSubOne_mul_apply huV hvN (e j), map_add]


private def formHom (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    {V : Submodule K E} (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {H : Type*} [Group H] {ρ : H →* (E ≃ₗ[K] E)}
    (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {D : Subgroup H} (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    {e : Fin 2 → E} :
    Additive D →+ Matrix (Fin 2) (Fin 2) K where
  toFun d := formMatrix B b τ e (ρ ((Additive.toMul d : D) : H))
  map_zero' := by
    have h : ((Additive.toMul (0 : Additive D) : D) : H) = 1 := rfl
    rw [h, map_one]
    exact formMatrix_one B b τ e
  map_add' d d' := by
    ext i j
    change formMatrix B b τ e
        (ρ (((Additive.toMul d : D) : H) * ((Additive.toMul d' : D) : H))) i j =
      formMatrix B b τ e (ρ ((Additive.toMul d : D) : H)) i j +
        formMatrix B b τ e (ρ ((Additive.toMul d' : D) : H)) i j
    rw [map_mul]
    exact formMatrix_mul B b (hDV _ (Additive.toMul d).2)
      (fun x => linSubOne_comp_linSubOne_mem B hBalt hNV (hρB _)
        (hDV _ (Additive.toMul d').2) (hDτ _ (Additive.toMul d').2) x) i j


private lemma card_sym_two_le_of_injective {K D G₀ : Type*} [Field K] [Finite K]
    [Group D] [Finite D] [Finite G₀]
    (φ : Additive D →+ Matrix (Fin 2) (Fin 2) K)
    (f : G₀ → φ.ker) (hf : Function.Injective f)
    (hsym : ∀ t : Matrix (Fin 2) (Fin 2) K, tᵀ = t → t ∈ φ.range) :
    Nat.card K ^ 3 * Nat.card G₀ ≤ Nat.card D := by
  have hker : Nat.card G₀ ≤ Nat.card φ.ker :=
    Nat.card_le_card_of_injective f hf
  have hrange : Nat.card K ^ 3 ≤ Nat.card φ.range := by
    have hle : Nat.card (Fin 3 → K) ≤ Nat.card φ.range := by
      refine Nat.card_le_card_of_injective
        (fun x : Fin 3 → K =>
          ⟨!![x 0, x 1; x 1, x 2], hsym (!![x 0, x 1; x 1, x 2]) ?_⟩) ?_
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
      · intro x y h
        have hm : (!![x 0, x 1; x 1, x 2] : Matrix (Fin 2) (Fin 2) K) =
            !![y 0, y 1; y 1, y 2] := Subtype.ext_iff.mp h
        funext i
        fin_cases i
        · simpa using congrFun (congrFun hm 0) 0
        · simpa using congrFun (congrFun hm 0) 1
        · simpa using congrFun (congrFun hm 1) 1
    simpa [Nat.card_fun, Nat.card_fin] using hle
  calc Nat.card K ^ 3 * Nat.card G₀ ≤ Nat.card φ.range * Nat.card φ.ker :=
        Nat.mul_le_mul hrange hker
    _ = Nat.card φ.ker * Nat.card φ.range := Nat.mul_comm _ _
    _ = Nat.card (Additive D) := AddSubgroup.card_ker_mul_card_range φ
    _ = Nat.card D := Nat.card_congr (Additive.ofMul (α := D))

private lemma formMatrix_eq_zero_of_mem_D₀ {V : Submodule K E}
    {τ : E ≃ₗ[K] E} (B : LinearMap.BilinForm K E)
    {H : Type*} [Group H] {ρ : H →* (E ≃ₗ[K] E)}
    {D₀ : Subgroup H} (hD₀U : ∀ d ∈ D₀, ∀ e, ρ d (τ e - e) = τ e - e)
    {d : H} (hd : d ∈ D₀) {b : Module.Basis (Fin 2) K V} {e : Fin 2 → E} :
    formMatrix B b τ e (ρ d) = 0 := by
  have hzero : ∀ k : Fin 2, linSubOne (ρ d) (linSubOne τ (e k)) = 0 := by
    intro k
    change ρ d (τ (e k) - e k) - (τ (e k) - e k) = 0
    rw [hD₀U d hd (e k), sub_self]
  ext i j
  simp only [formMatrix, Matrix.zero_apply, hzero, map_zero]

private lemma linSubOne_comp_linSubOne_eq_sum (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E}
    (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {u : E ≃ₗ[K] E} (hu : ∀ e f, B (u e) (u f) = B e f)
    (huV : ∀ v ∈ V, u v = v) (huτ : ∀ e, u (τ e) = τ (u e))
    {e : Fin 2 → E} (he : ∀ i j, B (e i) (b j) = if i = j then 1 else 0) (x : E) :
    linSubOne u (linSubOne τ x) =
      ∑ i, ∑ j, (formMatrix B b τ e u i j * B x (b j)) • (b i : E) := by
  let w : E := x - ∑ j, B x (b j) • e j
  have hw : w ∈ B.orthogonal V :=
    sub_sum_smul_mem_orthogonal B hBalt b he x
  have hzero : linSubOne u (linSubOne τ w) = 0 :=
    linSubOne_comp_linSubOne_eq_zero B hBalt hNV huV hw
  have hx : x = w + ∑ j, B x (b j) • e j := by
    simp only [w]
    abel
  have hstep : linSubOne u (linSubOne τ x) =
      ∑ j, B x (b j) • linSubOne u (linSubOne τ (e j)) := by
    conv_lhs => rw [hx]
    simp only [map_add, map_sum, map_smul, hzero, zero_add]
  calc linSubOne u (linSubOne τ x)
      = ∑ j, B x (b j) • linSubOne u (linSubOne τ (e j)) := hstep
    _ = ∑ j, B x (b j) • ∑ i, formMatrix B b τ e u i j • (b i : E) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [eq_sum_of_mem_dual B b he
          (linSubOne_comp_linSubOne_mem B hBalt hNV hu huV huτ (e j))]
    _ = ∑ i, ∑ j, (formMatrix B b τ e u i j * B x (b j)) • (b i : E) := by
        simp_rw [Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, mul_comm]

private lemma formMatrix_eq_smul_of_zero_diag (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E}
    (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {u : E ≃ₗ[K] E} (hu : ∀ e f, B (u e) (u f) = B e f)
    (huV : ∀ v ∈ V, u v = v) (huτ : ∀ e, u (τ e) = τ (u e))
    {e : Fin 2 → E} (he : ∀ i j, B (e i) (b j) = if i = j then 1 else 0)
    (h00 : formMatrix B b τ e u 0 0 = 0)
    (h11 : formMatrix B b τ e u 1 1 = 0)
    (h01 : formMatrix B b τ e u 1 0 = formMatrix B b τ e u 0 1) (x : E) :
    linSubOne u (linSubOne τ x) =
      formMatrix B b τ e u 0 1 •
        (B x (b 1) • (b 0 : E) + B x (b 0) • (b 1 : E)) := by
  rw [linSubOne_comp_linSubOne_eq_sum B hBalt b hNV hu huV huτ he x]
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h00, h11, h01]
  simp [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]




end Basic

theorem exists_apply_basis_eq {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Module.Finite K E] {ι : Type*} (B : LinearMap.BilinForm K E)
    (hBnd : ∀ e, (∀ f, B e f = 0) → e = 0) (V : Submodule K E) (b : Module.Basis ι K V)
    (x : ι → K) : ∃ e, ∀ j, B e (b j) = x j := by
  have hnd : B.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hBnd
  let φ : V →ₗ[K] K := b.constr K x
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
  refine ⟨(B.toDual hnd).symm g, fun j => ?_⟩
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  have := LinearMap.congr_fun hg (b j)
  simpa [φ] using this

section Main

variable {K E H : Type*} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup E] [Module K E] [Module.Finite K E] [Group H] [Finite H]

private lemma formHom_transpose (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    {V : Submodule K E} (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    (hτB : ∀ e f, B (τ e) (τ f) = B e f) (hτ2 : ∀ e, τ (τ e) = e)
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {ρ : H →* (E ≃ₗ[K] E)} (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {D : Subgroup H} (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    {e : Fin 2 → E} :
    ∀ s ∈ (formHom B hBalt b hNV hρB hDV hDτ (D := D) (e := e)).range, sᵀ = s := by
  intro s hs
  rcases AddMonoidHom.mem_range.mp hs with ⟨d, rfl⟩
  ext i j
  rw [Matrix.transpose_apply]
  change formMatrix B b τ e (ρ ((Additive.toMul d : D) : H)) j i =
    formMatrix B b τ e (ρ ((Additive.toMul d : D) : H)) i j
  exact formMatrix_transpose B hBalt b hτB hτ2 hNV (hρB _) (hDV _ (Additive.toMul d).2)
    (hDτ _ (Additive.toMul d).2) j i

private lemma formHom_invariant (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    {V : Submodule K E} (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {ρ : H →* (E ≃ₗ[K] E)} (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {D : Subgroup H} (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    {e : Fin 2 → E} (he : ∀ i j, B (e i) (b j) = if i = j then 1 else 0)
    {Γ : Set H} (hΓτ : ∀ r ∈ Γ, ∀ e, ρ r (τ e) = τ (ρ r e))
    (hΓD : ∀ r ∈ Γ, ∀ d ∈ D, r * d * r⁻¹ ∈ D)
    (hΓ : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, ∃ r ∈ Γ, ∀ j,
      ρ r (b j) = ∑ i, (A : Matrix (Fin 2) (Fin 2) K) i j • (b i : E)) :
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      ∀ s ∈ (formHom B hBalt b hNV hρB hDV hDτ (D := D) (e := e)).range,
      (g : Matrix (Fin 2) (Fin 2) K) * s * (g : Matrix (Fin 2) (Fin 2) K)ᵀ ∈
        (formHom B hBalt b hNV hρB hDV hDτ (D := D) (e := e)).range := by
  intro g s hs
  rcases AddMonoidHom.mem_range.mp hs with ⟨a, rfl⟩
  obtain ⟨r, hr, hA⟩ := hΓ g
  let b' : D := ⟨r * (Additive.toMul a : D) * r⁻¹,
    hΓD r hr _ (Additive.toMul a).2⟩
  refine AddMonoidHom.mem_range.mpr ⟨Additive.ofMul b', ?_⟩
  ext i j
  change formMatrix B b τ e (ρ ((b' : D) : H)) i j =
    ((g : Matrix (Fin 2) (Fin 2) K) *
      formMatrix B b τ e (ρ ((Additive.toMul a : D) : H)) *
      (g : Matrix (Fin 2) (Fin 2) K)ᵀ) i j
  rw [show ((b' : D) : H) = r * (Additive.toMul a : D) * r⁻¹ from rfl]
  rw [formMatrix_conj B hBalt hNV hρB hDV hDτ hΓτ hΓD he hr hA
    (Additive.toMul a).2 i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]
  conv_rhs => rw [Finset.sum_comm]

private lemma exists_mu_of_zero_diag (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E}
    (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    (hτB : ∀ e f, B (τ e) (τ f) = B e f) (hτ2 : ∀ e, τ (τ e) = e)
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {ρ : H →* (E ≃ₗ[K] E)} (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {D : Subgroup H} (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    {e : Fin 2 → E} (he : ∀ i j, B (e i) (b j) = if i = j then 1 else 0)
    (hzero : ∀ s ∈ (formHom B hBalt b hNV hρB hDV hDτ (D := D) (e := e)).range,
      s 0 0 = 0 ∧ s 1 1 = 0) :
    ∃ μ : H → K, ∀ d ∈ D, ∀ x : E,
      ρ d (τ x - x) - (τ x - x) =
        μ d • (B x (b 1) • (b 0 : E) + B x (b 0) • (b 1 : E)) := by
  refine ⟨fun d => formMatrix B b τ e (ρ d) 0 1, ?_⟩
  intro d hd x
  let d' : D := ⟨d, hd⟩
  have hmem : formMatrix B b τ e (ρ d) ∈
      (formHom B hBalt b hNV hρB hDV hDτ (D := D) (e := e)).range :=
    AddMonoidHom.mem_range.mpr ⟨Additive.ofMul d', rfl⟩
  have h00 := (hzero _ hmem).1
  have h11 := (hzero _ hmem).2
  have h01 : formMatrix B b τ e (ρ d) 1 0 = formMatrix B b τ e (ρ d) 0 1 :=
    formMatrix_transpose B hBalt b hτB hτ2 hNV (hρB d) (hDV d hd) (hDτ d hd) 1 0
  have hformula := formMatrix_eq_smul_of_zero_diag B hBalt b hNV (hρB d) (hDV d hd)
    (hDτ d hd) he h00 h11 h01 x
  simpa [linSubOne] using hformula

private lemma false_of_symmetric_range (B : LinearMap.BilinForm K E)
    (hBalt : ∀ e, B e e = 0) {V : Submodule K E}
    (b : Module.Basis (Fin 2) K V) {τ : E ≃ₗ[K] E}
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    {ρ : H →* (E ≃ₗ[K] E)} (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    {D D₀ : Subgroup H} (hD₀ : D₀ ≤ D)
    (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e))
    (hD₀U : ∀ d ∈ D₀, ∀ e, ρ d (τ e - e) = τ e - e)
    {e : Fin 2 → E}
    (hall : ∀ s : Matrix (Fin 2) (Fin 2) K, sᵀ = s →
      s ∈ (formHom B hBalt b hNV hρB hDV hDτ (D := D) (e := e)).range)
    (hcard : Nat.card D < Nat.card K ^ 3 * Nat.card D₀) : False := by
  let φ : Additive D →+ Matrix (Fin 2) (Fin 2) K :=
    formHom B hBalt b hNV hρB hDV hDτ (D := D) (e := e)
  let f : D₀ → φ.ker := fun d =>
    ⟨Additive.ofMul ⟨(d : H), hD₀ d.2⟩, by
      change formMatrix B b τ e (ρ (d : H)) = 0
      exact formMatrix_eq_zero_of_mem_D₀ B hD₀U d.2⟩
  have hf : Function.Injective f := by
    intro d₁ d₂ h
    have h' : Additive.ofMul (⟨(d₁ : H), hD₀ d₁.2⟩ : D) =
        Additive.ofMul (⟨(d₂ : H), hD₀ d₂.2⟩ : D) := Subtype.ext_iff.mp h
    have h'' : (⟨(d₁ : H), hD₀ d₁.2⟩ : D) = ⟨(d₂ : H), hD₀ d₂.2⟩ :=
      Additive.ofMul.injective h'
    have hH : (d₁ : H) = (d₂ : H) :=
      congrArg (fun x : D => (x : H)) h''
    exact Subtype.ext hH
  have hle := card_sym_two_le_of_injective φ f hf hall
  omega

end Main

theorem exists_sub_one_mul_sub_one_eq_smul {K E H : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 2 < Nat.card K) [AddCommGroup E] [Module K E] [Module.Finite K E] [Group H]
    [Finite H]
    (B : LinearMap.BilinForm K E) (hBalt : ∀ e, B e e = 0)
    (hBnd : ∀ e, (∀ f, B e f = 0) → e = 0)
    (ρ : H →* (E ≃ₗ[K] E)) (hρB : ∀ h e f, B (ρ h e) (ρ h f) = B e f)
    (τ : E ≃ₗ[K] E) (hτB : ∀ e f, B (τ e) (τ f) = B e f) (hτ2 : ∀ e, τ (τ e) = e)
    (V : Submodule K E) (b : Module.Basis (Fin 2) K V)
    (hNV : ∀ e, (∀ v ∈ V, B e v = 0) → τ e - e ∈ V)
    (D D₀ : Subgroup H) (hD₀ : D₀ ≤ D)
    (hDτ : ∀ d ∈ D, ∀ e, ρ d (τ e) = τ (ρ d e)) (hDV : ∀ d ∈ D, ∀ v ∈ V, ρ d v = v)
    (hD₀U : ∀ d ∈ D₀, ∀ e, ρ d (τ e - e) = τ e - e)
    (hcard : Nat.card D < Nat.card K ^ 3 * Nat.card D₀)
    (Γ : Set H) (hΓτ : ∀ r ∈ Γ, ∀ e, ρ r (τ e) = τ (ρ r e))
    (hΓD : ∀ r ∈ Γ, ∀ d ∈ D, r * d * r⁻¹ ∈ D)
    (hΓ : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K, ∃ r ∈ Γ, ∀ j,
      ρ r (b j) = ∑ i, (A : Matrix (Fin 2) (Fin 2) K) i j • (b i : E)) :
    ∃ μ : H → K, ∀ d ∈ D, ∀ e,
      ρ d (τ e - e) - (τ e - e) =
        μ d • (B e (b 1) • (b 0 : E) + B e (b 0) • (b 1 : E)) := by
  choose e he using fun i : Fin 2 =>
    exists_apply_basis_eq B hBnd V b (fun j => if i = j then 1 else 0)
  let φ : Additive D →+ Matrix (Fin 2) (Fin 2) K :=
    formHom B hBalt b hNV hρB hDV hDτ (D := D) (e := e)
  rcases sym_two_congr_invariant_dichotomy hK φ.range
    (formHom_transpose B hBalt b hτB hτ2 hNV hρB hDV hDτ)
    (formHom_invariant B hBalt b hNV hρB hDV hDτ he hΓτ hΓD hΓ)
    with hzero | hall
  · exact exists_mu_of_zero_diag B hBalt b hτB hτ2 hNV hρB hDV hDτ he hzero
  · exact False.elim
      (false_of_symmetric_range B hBalt b hNV hρB hD₀ hDV hDτ hD₀U hall hcard)

end CFSG.LinearAlgebra
