module

public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.FieldTheory.Finite.GaloisField
public import CFSG.LinearAlgebra.SLCocycleVanishing
public import CFSG.LinearAlgebra.GLTwoCocycle

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open Matrix
open Module

variable {k V : Type} [Field k] [Finite k] [CharP k 2] [AddCommGroup V] [Module k V]
  [Module.Finite k V]

private lemma equivFun_toLin_apply {N : ℕ} (b : Module.Basis (Fin N) k V)
    (M : Matrix (Fin N) (Fin N) k) (x : V) :
    b.equivFun (Matrix.toLin b b M x) = M *ᵥ b.equivFun x := by
  have h := LinearMap.toMatrix_mulVec_repr b b (Matrix.toLin b b M) x
  rw [LinearMap.toMatrix_toLin] at h
  simpa only [Basis.equivFun_apply] using h.symm

private theorem matrix_cocycle_coboundary {N : ℕ} (hN : 4 ≤ N)
    (c : Matrix.SpecialLinearGroup (Fin N) k → Fin N → k)
    (hc : ∀ g h : Matrix.SpecialLinearGroup (Fin N) k,
      c (g * h) = c g + (g : Matrix (Fin N) (Fin N) k) *ᵥ c h) :
    ∃ a : Fin N → k, ∀ g : Matrix.SpecialLinearGroup (Fin N) k,
      c g = (g : Matrix (Fin N) (Fin N) k) *ᵥ a - a := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hnprime, hcard⟩ := FiniteField.card k 2
  have hpos : 0 < (n : ℕ) := n.pos
  rcases lt_or_ge (n : ℕ) 2 with hn | hn
  ·
    have hcard2 : Fintype.card k = 2 := by
      have hn1 : (n : ℕ) = 1 := by omega
      rw [hcard, hn1]
      norm_num
    let φ : k ≃+* ZMod 2 :=
      FiniteField.ringEquivOfCardEq (K := k) (K' := ZMod 2) (by rw [hcard2, ZMod.card])
    have hmap_mulVec : ∀ (M : Matrix (Fin N) (Fin N) k) (x : Fin N → k) (i : Fin N),
        φ ((M *ᵥ x) i) = ((φ : k →+* ZMod 2).mapMatrix M *ᵥ (φ ∘ x)) i := by
      intro M x i
      simpa using RingHom.map_mulVec (φ : k →+* ZMod 2) M x i
    have hsymm_mulVec : ∀ (M : Matrix (Fin N) (Fin N) (ZMod 2)) (x : Fin N → k) (i : Fin N),
        φ (((φ.symm : ZMod 2 →+* k).mapMatrix M *ᵥ x) i) = (M *ᵥ (φ ∘ x)) i := by
      intro M x i
      have hmap : ((φ.symm : ZMod 2 →+* k).mapMatrix M).map (φ : k →+* ZMod 2) = M := by
        ext a b
        simp [RingHom.mapMatrix_apply, Matrix.map_apply]
      have h := RingHom.map_mulVec (φ : k →+* ZMod 2)
        ((φ.symm : ZMod 2 →+* k).mapMatrix M) x i
      rw [hmap] at h
      exact h
    have hmap_symm : ∀ M : Matrix.SpecialLinearGroup (Fin N) k,
        Matrix.SpecialLinearGroup.map (φ.symm : ZMod 2 →+* k)
          (Matrix.SpecialLinearGroup.map (φ : k →+* ZMod 2) M) = M := by
      intro M
      apply Subtype.ext
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    let d : Matrix.SpecialLinearGroup (Fin N) (ZMod 2) → Fin N → ZMod 2 :=
      fun M => φ ∘ c (Matrix.SpecialLinearGroup.map (φ.symm : ZMod 2 →+* k) M)
    have hd : ∀ M M' : Matrix.SpecialLinearGroup (Fin N) (ZMod 2),
        d (M * M') = d M + M *ᵥ d M' := by
      intro M M'
      funext i
      have hmap := map_mul (Matrix.SpecialLinearGroup.map (φ.symm : ZMod 2 →+* k)) M M'
      have hMk : (Matrix.SpecialLinearGroup.map (φ.symm : ZMod 2 →+* k) M :
          Matrix (Fin N) (Fin N) k) =
          (φ.symm : ZMod 2 →+* k).mapMatrix (M : Matrix (Fin N) (Fin N) (ZMod 2)) :=
        Matrix.SpecialLinearGroup.map_apply_coe _ M
      have h4 : φ (((φ.symm : ZMod 2 →+* k).mapMatrix
          (M : Matrix (Fin N) (Fin N) (ZMod 2)) *ᵥ
          c (Matrix.SpecialLinearGroup.map (φ.symm : ZMod 2 →+* k) M')) i) =
          (M *ᵥ d M') i := by
        have h := hsymm_mulVec (M : Matrix (Fin N) (Fin N) (ZMod 2))
          (c (Matrix.SpecialLinearGroup.map (φ.symm : ZMod 2 →+* k) M')) i
        simpa [d] using h
      simp only [d, Function.comp_apply, Pi.add_apply]
      rw [hmap, hc, Pi.add_apply, map_add, hMk, h4]
    have hρ : ∀ i j : Fin N, i ≠ j → ∃ γ : Matrix.SpecialLinearGroup (Fin N) (ZMod 2),
        ((Matrix.SpecialLinearGroup.toGL γ : Matrix (Fin N) (Fin N) (ZMod 2))) =
          Matrix.transvection i j 1 := by
      intro i j hij
      refine ⟨Matrix.SpecialLinearGroup.transvection hij 1, ?_⟩
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        Matrix.SpecialLinearGroup.transvection_coe]
      rfl
    have hker : ∀ g : Matrix.SpecialLinearGroup (Fin N) (ZMod 2),
        Matrix.SpecialLinearGroup.toGL g = 1 → d g = 0 := by
      intro g hg
      have hg1 : g = 1 :=
        Matrix.SpecialLinearGroup.toGL_injective (by rw [hg, map_one])
      rw [hg1]
      have h := hd 1 1
      rw [mul_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
      exact add_left_cancel (a := d 1) (by rw [add_zero]; exact h.symm)
    obtain ⟨a'', ha''⟩ := CFSG.LinearAlgebra.exists_eq_mulVec_sub_of_cocycle (n := N)
      (by omega) Matrix.SpecialLinearGroup.toGL hρ d hd hker
    refine ⟨fun i => φ.symm (a'' i), fun M => ?_⟩
    have ha'φ : φ ∘ (fun i => φ.symm (a'' i)) = a'' := by
      funext j
      simp
    have hM₂ := hmap_symm M
    have h := ha'' (Matrix.SpecialLinearGroup.map (φ : k →+* ZMod 2) M)
    have hd_eq : d (Matrix.SpecialLinearGroup.map (φ : k →+* ZMod 2) M) = φ ∘ c M := by
      dsimp only [d]
      rw [hM₂]
    have h1 : ∀ i, φ (c M i) =
        ((φ : k →+* ZMod 2).mapMatrix (M : Matrix (Fin N) (Fin N) k) *ᵥ a'' - a'') i := by
      intro i
      have h2 : φ ∘ c M =
          (φ : k →+* ZMod 2).mapMatrix (M : Matrix (Fin N) (Fin N) k) *ᵥ a'' - a'' := by
        rw [← hd_eq, h, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
          Matrix.SpecialLinearGroup.map_apply_coe]
      simpa [Function.comp_apply] using congrFun h2 i
    funext i
    apply φ.injective
    rw [h1 i, Pi.sub_apply, Pi.sub_apply, map_sub, hmap_mulVec, ha'φ]
    simp
  ·
    refine CFSG.LinearAlgebra.exists_eq_mulVec_sub_of_cocycle_sl ?_ (by omega) c hc
    rw [hcard]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := pow_le_pow_right' (by norm_num) hn

private theorem exists_eq_sub_of_cocycle_natural_aux {N : ℕ} (b : Module.Basis (Fin N) k V)
    (hN : 4 ≤ N) (c : SpecialLinearGroup k V → V)
    (hc : ∀ g h : SpecialLinearGroup k V, c (g * h) = c g + g (c h)) :
    ∃ a : V, ∀ g : SpecialLinearGroup k V, c g = g a - a := by
  classical
  let e : Matrix.SpecialLinearGroup (Fin N) k ≃* SpecialLinearGroup k V :=
    Matrix.SpecialLinearGroup.toLin_equiv b
  let c' : Matrix.SpecialLinearGroup (Fin N) k → Fin N → k := fun M => b.equivFun (c (e M))
  have hc' : ∀ M M' : Matrix.SpecialLinearGroup (Fin N) k,
      c' (M * M') = c' M + (M : Matrix (Fin N) (Fin N) k) *ᵥ c' M' := by
    intro M M'
    have hkey : b.equivFun ((e M) (c (e M'))) =
        (M : Matrix (Fin N) (Fin N) k) *ᵥ b.equivFun (c (e M')) := by
      have h := LinearMap.toMatrix_mulVec_repr b b (e M : V →ₗ[k] V) (c (e M'))
      rw [← Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq b (e M),
        e.symm_apply_apply] at h
      have h2 : b.equivFun ((e M : V →ₗ[k] V) (c (e M'))) =
          (M : Matrix (Fin N) (Fin N) k) *ᵥ b.equivFun (c (e M')) := by
        simpa only [← Basis.equivFun_apply] using h.symm
      exact h2
    change b.equivFun (c (e (M * M'))) =
      b.equivFun (c (e M)) + (M : Matrix (Fin N) (Fin N) k) *ᵥ b.equivFun (c (e M'))
    rw [map_mul e M M', hc (e M) (e M'), map_add, hkey]
  obtain ⟨a', ha'⟩ := matrix_cocycle_coboundary hN c' hc'
  refine ⟨b.equivFun.symm a', fun g => ?_⟩
  apply b.equivFun.injective
  have hval : b.equivFun (c g) =
      (e.symm g : Matrix (Fin N) (Fin N) k) *ᵥ a' - a' := by
    have h := ha' (e.symm g)
    change b.equivFun (c (e (e.symm g))) = _ at h
    rwa [e.apply_symm_apply] at h
  have hga : b.equivFun (g (b.equivFun.symm a')) =
      (e.symm g : Matrix (Fin N) (Fin N) k) *ᵥ a' := by
    have h := LinearMap.toMatrix_mulVec_repr b b (g : V →ₗ[k] V) (b.equivFun.symm a')
    rw [← Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq b g] at h
    have h2 : b.equivFun ((g : V →ₗ[k] V) (b.equivFun.symm a')) =
        (e.symm g : Matrix (Fin N) (Fin N) k) *ᵥ a' := by
      simpa only [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply] using h.symm
    exact h2
  rw [map_sub, hval, hga, LinearEquiv.apply_symm_apply]

theorem exists_eq_sub_of_cocycle_natural (hV : 4 ≤ Module.finrank k V)
    (c : SpecialLinearGroup k V → V)
    (hc : ∀ g h : SpecialLinearGroup k V, c (g * h) = c g + g (c h)) :
    ∃ a : V, ∀ g : SpecialLinearGroup k V, c g = g a - a :=
  exists_eq_sub_of_cocycle_natural_aux (Module.finBasis k V) hV c hc

private lemma dualBasis_equivFun_comp {N : ℕ} (b : Module.Basis (Fin N) k V)
    (u : V ≃ₗ[k] V) (f : Module.Dual k V) :
    b.dualBasis.equivFun (f ∘ₗ u.toLinearMap) =
      (LinearMap.toMatrix b b u.toLinearMap)ᵀ *ᵥ b.dualBasis.equivFun f := by
  rw [← Module.Dual.transpose_apply u.toLinearMap f,
    Basis.equivFun_apply b.dualBasis (Module.Dual.transpose (R := k) u.toLinearMap f),
    ← LinearMap.toMatrix_mulVec_repr b.dualBasis b.dualBasis
      (Module.Dual.transpose (R := k) u.toLinearMap) f,
    LinearMap.toMatrix_transpose, Basis.equivFun_apply b.dualBasis f]

private lemma transpose_mul' {N : ℕ} (A B : Matrix.SpecialLinearGroup (Fin N) k) :
    Matrix.SpecialLinearGroup.transpose (A * B) =
      Matrix.SpecialLinearGroup.transpose B * Matrix.SpecialLinearGroup.transpose A := by
  apply Subtype.ext
  change ((A : Matrix (Fin N) (Fin N) k) * (B : Matrix (Fin N) (Fin N) k))ᵀ =
    (B : Matrix (Fin N) (Fin N) k)ᵀ * (A : Matrix (Fin N) (Fin N) k)ᵀ
  rw [Matrix.transpose_mul]

private lemma transpose_one' {N : ℕ} :
    Matrix.SpecialLinearGroup.transpose (1 : Matrix.SpecialLinearGroup (Fin N) k) = 1 := by
  apply Subtype.ext
  change ((1 : Matrix (Fin N) (Fin N) k))ᵀ = 1
  rw [Matrix.transpose_one]

private lemma transpose_inv' {N : ℕ} (A : Matrix.SpecialLinearGroup (Fin N) k) :
    Matrix.SpecialLinearGroup.transpose A⁻¹ =
      (Matrix.SpecialLinearGroup.transpose A)⁻¹ := by
  have h : Matrix.SpecialLinearGroup.transpose A *
      Matrix.SpecialLinearGroup.transpose A⁻¹ = 1 := by
    rw [← transpose_mul', inv_mul_cancel, transpose_one']
  exact eq_inv_of_mul_eq_one_right h

private lemma transpose_transpose' {N : ℕ} (A : Matrix.SpecialLinearGroup (Fin N) k) :
    Matrix.SpecialLinearGroup.transpose (Matrix.SpecialLinearGroup.transpose A) = A := by
  apply Subtype.ext
  change ((A : Matrix (Fin N) (Fin N) k)ᵀ)ᵀ = (A : Matrix (Fin N) (Fin N) k)
  rw [Matrix.transpose_transpose]

private noncomputable def inverseTransposeEquiv {N : ℕ} :
    Matrix.SpecialLinearGroup (Fin N) k ≃* Matrix.SpecialLinearGroup (Fin N) k where
  toFun M := Matrix.SpecialLinearGroup.transpose M⁻¹
  invFun M := Matrix.SpecialLinearGroup.transpose M⁻¹
  left_inv M := by
    change Matrix.SpecialLinearGroup.transpose
      (Matrix.SpecialLinearGroup.transpose M⁻¹)⁻¹ = M
    rw [transpose_inv', transpose_transpose', inv_inv]
  right_inv M := by
    change Matrix.SpecialLinearGroup.transpose
      (Matrix.SpecialLinearGroup.transpose M⁻¹)⁻¹ = M
    rw [transpose_inv', transpose_transpose', inv_inv]
  map_mul' M M' := by
    change Matrix.SpecialLinearGroup.transpose (M * M')⁻¹ =
      Matrix.SpecialLinearGroup.transpose M⁻¹ * Matrix.SpecialLinearGroup.transpose M'⁻¹
    rw [_root_.mul_inv_rev, transpose_mul']

private lemma inverseTransposeEquiv_coe {N : ℕ} (M : Matrix.SpecialLinearGroup (Fin N) k) :
    ((inverseTransposeEquiv (k := k) (N := N) M : Matrix.SpecialLinearGroup (Fin N) k) :
      Matrix (Fin N) (Fin N) k) =
      (((M⁻¹ : Matrix.SpecialLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k))ᵀ := rfl

theorem exists_eq_sub_of_cocycle_dual (hV : 4 ≤ Module.finrank k V)
    (c : SpecialLinearGroup k V → Module.Dual k V)
    (hc : ∀ g h : SpecialLinearGroup k V,
      c (g * h) = c g + c h ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) :
    ∃ f : Module.Dual k V, ∀ g : SpecialLinearGroup k V,
      c g = f ∘ₗ (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap - f := by
  classical
  let N := Module.finrank k V
  let b : Module.Basis (Fin N) k V := Module.finBasis k V
  let e : Matrix.SpecialLinearGroup (Fin N) k ≃* SpecialLinearGroup k V :=
    Matrix.SpecialLinearGroup.toLin_equiv b
  let eD : Matrix.SpecialLinearGroup (Fin N) k ≃* SpecialLinearGroup k (Module.Dual k V) :=
    Matrix.SpecialLinearGroup.toLin_equiv b.dualBasis
  let it : Matrix.SpecialLinearGroup (Fin N) k ≃* Matrix.SpecialLinearGroup (Fin N) k :=
    inverseTransposeEquiv
  let Φ : SpecialLinearGroup k V ≃* SpecialLinearGroup k (Module.Dual k V) :=
    (e.symm.trans it).trans eD
  have hΦ : ∀ (g : SpecialLinearGroup k V) (f : Module.Dual k V),
      Φ g f = f.comp (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap := by
    intro g f
    let M : Matrix.SpecialLinearGroup (Fin N) k := e.symm g
    have hΦg : Φ g = eD (it M) := rfl
    have h1 : b.dualBasis.equivFun (eD (it M) f) =
        (it M : Matrix (Fin N) (Fin N) k) *ᵥ b.dualBasis.equivFun f := by
      change b.dualBasis.equivFun
        ((eD (it M) : Module.Dual k V →ₗ[k] Module.Dual k V) f) = _
      rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq b.dualBasis (it M)]
      exact equivFun_toLin_apply (V := Module.Dual k V) b.dualBasis (it M) f
    have h2 : b.dualBasis.equivFun
          (f.comp (SpecialLinearGroup.toLinearEquiv g⁻¹).toLinearMap) =
        (((M⁻¹ : Matrix.SpecialLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k))ᵀ *ᵥ
          b.dualBasis.equivFun f := by
      rw [dualBasis_equivFun_comp b (SpecialLinearGroup.toLinearEquiv g⁻¹) f]
      change (LinearMap.toMatrix b b ((g⁻¹ : SpecialLinearGroup k V) : V →ₗ[k] V))ᵀ *ᵥ
          b.dualBasis.equivFun f = _
      rw [← Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq b g⁻¹, map_inv]
    apply b.dualBasis.equivFun.injective
    rw [hΦg, h1, h2]
    rw [show (it M : Matrix (Fin N) (Fin N) k) =
        (((M⁻¹ : Matrix.SpecialLinearGroup (Fin N) k) : Matrix (Fin N) (Fin N) k))ᵀ from
      inverseTransposeEquiv_coe M]
  let c₂ : SpecialLinearGroup k (Module.Dual k V) → Module.Dual k V := fun u => c (Φ.symm u)
  have hc₂ : ∀ u u' : SpecialLinearGroup k (Module.Dual k V),
      c₂ (u * u') = c₂ u + u (c₂ u') := by
    intro u u'
    have h := hc (Φ.symm u) (Φ.symm u')
    rw [← map_mul Φ.symm u u'] at h
    dsimp only [c₂]
    rw [h]
    congr 1
    have hΦ' := hΦ (Φ.symm u) (c (Φ.symm u'))
    rw [Φ.apply_symm_apply u] at hΦ'
    exact hΦ'.symm
  have hVd : 4 ≤ Module.finrank k (Module.Dual k V) := by
    rw [Subspace.dual_finrank_eq]
    exact hV
  obtain ⟨a, ha⟩ := exists_eq_sub_of_cocycle_natural (V := Module.Dual k V) hVd c₂ hc₂
  refine ⟨a, fun g => ?_⟩
  have h := ha (Φ g)
  rw [show c₂ (Φ g) = c g from by simp [c₂]] at h
  rw [h, hΦ g a]

end CFSG.LinearAlgebra.RootGroupSL
