module

public import CFSG.GF2Type.Widths1112.Co2Module.BlockData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Widths1112.Co2Module

open Finset

section Main

variable {Γ : Type*} [Group Γ] {ι : AddChar F3Vec Γ} (D : BlockData ι)
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) Γ V)

theorem exists_adapted_basis (hV : Module.finrank (ZMod 2) V = 22) (hnt : ∃ v, ρ (ι v) ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι D.w₁)) = 2 ∧
    Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)) = 2 ∧
    ∃ (x : V) (v0 : Module.Basis (Fin 2) (ZMod 2) (LinearMap.range (piE ρ ι)))
      (b : Module.Basis BIdx (ZMod 2) V),
      x ∈ LinearMap.range (eK ρ ι D.w₁) ∧ ρ D.t x = x ∧
      (∀ a, b (Sum.inl a) = ((v0 a : LinearMap.range (piE ρ ι)) : V)) ∧
      ∀ i j, b (Sum.inr (i, j)) = ρ (D.r i) ((ρ (ι D.v₀) ^ (j : ℕ)) x) := by
  haveI : FiniteDimensional (ZMod 2) V := finiteDimensional_of_finrank_eq_22 hV
  have hconst : ∀ w ∈ lineReps, ∀ w' ∈ lineReps, D.cls w = D.cls w' →
      Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w)) =
        Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι w')) :=
    fun w hw w' hw' hc => finrank_range_eK_eq_of_eqvGen ρ D.n D.An D.hn (D.horbit w hw w' hw' hc)
  obtain ⟨hE, hdim⟩ := finrank_piE_and_eK22 ρ ι hV isLineReps_lineReps D.cls D.h0 D.h1 hconst hnt
  have hw : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι D.w₁)) = 2 := by
    rw [hdim D.w₁ D.hw₁R, if_pos D.hw₁cls]
  have hne : LinearMap.range (eK ρ ι D.w₁) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hw
    omega
  obtain ⟨x, hx, hx0, htx⟩ := exists_fixed_mem_range_eK ρ ι D.ht D.ht2 (c := D.ct) D.hct D.hwt hne
  obtain ⟨b, hb0, hb1⟩ := exists_basis_of_orbits22 ρ ι hV isLineReps_lineReps D.cls D.h0 D.h1
    hconst hnt D.w D.hwinj D.hwR D.hwcls D.hw₁R D.hw₁cls D.hv₀ hx hx0 D.r D.Ar D.cr D.hr D.hcr D.hwA
    (Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range (piE ρ ι)) hE)
  exact ⟨hw, hE, x, Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range (piE ρ ι)) hE, b, hx, htx,
    hb0, hb1⟩

theorem closure_p_fixes [FiniteDimensional (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) (LinearMap.range (eK ρ ι D.w₁)) = 2) :
    ∀ q ∈ Subgroup.closure (Set.range D.p), ∀ y ∈ LinearMap.range (eK ρ ι D.w₁), ρ q y = y := by
  have hS : Set.range D.p ⊆ (stabSubgroup ι D.w₁ : Set Γ) := by
    rw [Set.range_subset_iff]
    intro j
    exact D.hpstab j
  have h2 : ∀ s ∈ Set.range D.p, ∃ k : ℕ, s ^ (2 ^ k) = 1 := by
    rintro s ⟨j, rfl⟩
    exact D.hp2 j
  exact closure_fixes_block ρ hdim D.hv₀ hS h2

theorem exists_theta (v0 : Module.Basis (Fin 2) (ZMod 2) (LinearMap.range (piE ρ ι))) {g : Γ}
    (hg : g ∈ normSubgroup ι) :
    ∃ θ : Matrix (Fin 2) (Fin 2) (ZMod 2), ∀ a,
      ρ g ((v0 a : LinearMap.range (piE ρ ι)) : V) =
        ∑ a', θ a' a • ((v0 a' : LinearMap.range (piE ρ ι)) : V) := by
  have hW : ∀ y ∈ LinearMap.range (piE ρ ι), ρ g y ∈ LinearMap.range (piE ρ ι) :=
    fun y hy => norm_apply_mem_range_piE ρ hg hy
  refine ⟨LinearMap.toMatrix v0 v0 ((ρ g).restrict hW), fun a => ?_⟩
  have h1 : (ρ g).restrict hW (v0 a) =
      ∑ a', LinearMap.toMatrix v0 v0 ((ρ g).restrict hW) a' a • v0 a' := by
    calc (ρ g).restrict hW (v0 a)
        = ∑ a', v0.repr ((ρ g).restrict hW (v0 a)) a' • v0 a' := (v0.sum_repr _).symm
      _ = ∑ a', LinearMap.toMatrix v0 v0 ((ρ g).restrict hW) a' a • v0 a' := by
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [LinearMap.toMatrix_apply]
  have h2 := congrArg (fun w : LinearMap.range (piE ρ ι) => (w : V)) h1
  simpa only [LinearMap.coe_restrict_apply, Submodule.coe_sum, Submodule.coe_smul] using h2

theorem theta_one (hdim : Module.finrank (ZMod 2) (LinearMap.range (piE ρ ι)) = 2)
    {g : Γ} (hg : g ∈ D.Ninf) (y : V) (hy : y ∈ LinearMap.range (piE ρ ι)) : ρ g y = y := by
  have hPW : ∀ p ∈ D.Ninf, ∀ y ∈ LinearMap.range (piE ρ ι), ρ p y ∈ LinearMap.range (piE ρ ι) :=
    fun p hp y hy => norm_apply_mem_range_piE ρ (D.hNnorm hp) hy
  exact perfect_fixes_plane ρ (LinearMap.range (piE ρ ι)) hdim D.Ninf D.hNperf hPW g hg y hy

theorem theta_eq_one (v0 : Module.Basis (Fin 2) (ZMod 2) (LinearMap.range (piE ρ ι))) {g : Γ}
    (θ : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (hθ : ∀ a, ρ g ((v0 a : LinearMap.range (piE ρ ι)) : V) =
      ∑ a', θ a' a • ((v0 a' : LinearMap.range (piE ρ ι)) : V))
    (hfix : ∀ y ∈ LinearMap.range (piE ρ ι), ρ g y = y) : θ = 1 := by
  have key : ∀ a, v0 a = ∑ a', θ a' a • v0 a' := fun a => by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact (hfix _ (v0 a).2).symm.trans (hθ a)
  refine Matrix.ext fun i j => ?_
  have hj := congrArg (fun w : LinearMap.range (piE ρ ι) => v0.repr w i) (key j)
  simp only [Module.Basis.repr_self, map_sum, map_smul, Finsupp.finset_sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hj
  rw [Matrix.one_apply, ← hj]
  by_cases h : i = j
  · simp [h]
  · have h' : j ≠ i := fun h' => h h'.symm
    simp [h, h']

theorem isUnit_Qfin {S : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hS : IsUnit S) : IsUnit (Qfin S) := by
  have hQ : Qmat S = Matrix.fromBlocks S 0 0 1 := by
    ext r c
    rcases r with a | p <;> rcases c with a' | p' <;> simp [Qmat, Matrix.one_apply]
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  rw [Qfin, Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, hQ,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  exact hdet

theorem toMatrix_rho (v0 : Module.Basis (Fin 2) (ZMod 2) (LinearMap.range (piE ρ ι)))
    (b : Module.Basis BIdx (ZMod 2) V) (x : V)
    (hb0 : ∀ a, b (Sum.inl a) = ((v0 a : LinearMap.range (piE ρ ι)) : V))
    (hb1 : ∀ i j, b (Sum.inr (i, j)) = ρ (D.r i) ((ρ (ι D.v₀) ^ (j : ℕ)) x))
    (hx : x ∈ LinearMap.range (eK ρ ι D.w₁)) (htx : ρ D.t x = x)
    (hP : ∀ q ∈ Subgroup.closure (Set.range D.p), ρ q x = x) (k : Fin 8)
    (θ : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (hθ : ∀ a, ρ (D.m k) ((v0 a : LinearMap.range (piE ρ ι)) : V) =
      ∑ a', θ a' a • ((v0 a' : LinearMap.range (piE ρ ι)) : V)) :
    LinearMap.toMatrix b b (ρ (D.m k)) = Xmat θ (D.σ k) (cfTab D.w₁ D.v₀ (D.u k)) := by
  have hpow : ∀ n : ℕ, ρ (D.t ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, htx, ih]
  have hs : ∀ (i : Fin 10) (j : Fin 2), ρ (D.t ^ D.ε k i j * D.pp k i j) x = x := by
    intro i j
    rw [map_mul, Module.End.mul_apply, hP (D.pp k i j) (D.hpp k i j), hpow]
  have hdec' : ∀ (i : Fin 10) (j : Fin 2), D.m k * D.r i * ι D.v₀ ^ (j : ℕ) =
      D.r (D.σ k i) * ι (D.u k i j) * (D.t ^ D.ε k i j * D.pp k i j) := by
    intro i j
    rw [D.hdec k i j]
    exact mul_assoc _ _ _
  have hcol : ∀ a, ρ (D.m k) (b (Sum.inl a)) = ∑ a', θ a' a • b (Sum.inl a') := by
    intro a
    rw [hb0 a, hθ a]
    simp only [hb0]
  ext r c
  rw [LinearMap.toMatrix_apply]
  rcases c with a | ⟨i, j⟩
  · rw [hcol a, map_sum]
    rcases r with a' | ⟨i', c'⟩
    · fin_cases a' <;> simp [Xmat, Module.Basis.repr_self, Finsupp.single_apply, map_smul]
    · simp [Xmat, Module.Basis.repr_self, Finsupp.single_apply, map_smul]
  · rw [rho_apply_basis22 ρ ι b D.hv₀ hb1 hx (n := D.m k) (r := D.r) (σ := D.σ k)
      (u := D.u k) (s := fun i j => D.t ^ D.ε k i j * D.pp k i j) hdec' hs i j]
    rw [map_add, map_smul, map_smul]
    rcases r with a' | ⟨i', c'⟩
    · simp [Xmat, Module.Basis.repr_self, Finsupp.single_apply]
    · rcases eq_or_ne (D.σ k i) i' with h | h
      · subst h
        fin_cases c' <;> simp [Xmat, cfTab, Module.Basis.repr_self, Finsupp.single_apply]
      · fin_cases c' <;>
          simp [Xmat, cfTab, Module.Basis.repr_self, Finsupp.single_apply, h, Ne.symm h]

theorem toMatrix_reindex {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂]
    [DecidableEq ι₂] (b : Module.Basis ι₁ (ZMod 2) V) (e : ι₁ ≃ ι₂)
    (f : Module.End (ZMod 2) V) :
    LinearMap.toMatrix (b.reindex e) (b.reindex e) f =
      Matrix.reindex e e (LinearMap.toMatrix b b f) := by
  ext r c
  simp only [LinearMap.toMatrix_apply, Module.Basis.reindex_apply,
    Module.Basis.repr_reindex_apply, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem exists_basis_change (b : Module.Basis (Fin 22) (ZMod 2) V)
    (Q : Matrix (Fin 22) (Fin 22) (ZMod 2)) (hQ : IsUnit Q) :
    ∃ b' : Module.Basis (Fin 22) (ZMod 2) V, ∀ f : Module.End (ZMod 2) V,
      Q * LinearMap.toMatrix b b f = LinearMap.toMatrix b' b' f * Q := by
  have hdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hQi : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hdet
  have hQQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hdet
  have h₁ : (Matrix.toLin b b Q⁻¹).comp (Matrix.toLin b b Q) = LinearMap.id := by
    rw [← Matrix.toLin_mul b b b, hQi, Matrix.toLin_one]
  have h₂ : (Matrix.toLin b b Q).comp (Matrix.toLin b b Q⁻¹) = LinearMap.id := by
    rw [← Matrix.toLin_mul b b b, hQQi, Matrix.toLin_one]
  obtain ⟨phi, hphi, hphis⟩ : ∃ phi : V ≃ₗ[ZMod 2] V, (∀ x : V, phi x = Matrix.toLin b b Q⁻¹ x) ∧
      (∀ x : V, phi.symm x = Matrix.toLin b b Q x) :=
    ⟨LinearEquiv.ofLinearMap (Matrix.toLin b b Q⁻¹) (Matrix.toLin b b Q) h₁ h₂,
      fun x => rfl, fun x => rfl⟩
  refine ⟨b.map phi, fun f => ?_⟩
  have key : LinearMap.toMatrix (b.map phi) (b.map phi) f =
      LinearMap.toMatrix b b (LinearMap.comp (Matrix.toLin b b Q)
        (LinearMap.comp f (Matrix.toLin b b Q⁻¹))) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Module.Basis.map_apply, Module.Basis.map_repr,
      LinearEquiv.trans_apply, hphi, hphis, LinearMap.comp_apply]
  rw [key, LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_comp b b b,
    LinearMap.toMatrix_toLin, LinearMap.toMatrix_toLin]
  simp only [Matrix.mul_assoc, hQi, Matrix.mul_one]

theorem normal_form (hV : Module.finrank (ZMod 2) V = 22) (hnt : ∃ v, ρ (ι v) ≠ 1) :
    ∃ b : Module.Basis (Fin 22) (ZMod 2) V,
      (∀ s, LinearMap.toMatrix b b (ρ (D.n s)) = D.X0 s) ∧
      LinearMap.toMatrix b b (ρ D.g) = D.M0 := by
  haveI := finiteDimensional_of_finrank_eq_22 hV
  obtain ⟨hd1, hd0, x, v0, b, hx, htx, hb0, hb1⟩ := exists_adapted_basis D ρ hV hnt
  have hPx : ∀ q ∈ Subgroup.closure (Set.range D.p), ρ q x = x :=
    fun q hq => closure_p_fixes D ρ hd1 q hq x hx
  have hmem : ∀ k, D.m k ∈ normSubgroup ι := fun k => (mem_normSubgroup ι).mpr ⟨D.Am k, D.hm k⟩
  choose θ hθ using fun k => exists_theta ρ v0 (hmem k)
  have hθ1 : ∀ k : Fin 3, θ (iY k) = 1 := fun k =>
    theta_eq_one ρ v0 (θ (iY k)) (hθ (iY k)) (fun y hy => theta_one D ρ hd0 (D.hy k) y hy)
  have hθ2 : ∀ k : Fin 3, θ (iZ k) = 1 := fun k =>
    theta_eq_one ρ v0 (θ (iZ k)) (hθ (iZ k)) (fun y hy => theta_one D ρ hd0 (D.hz k) y hy)
  obtain ⟨R, hR⟩ : ∃ R : Γ → Matrix (Fin 22) (Fin 22) (ZMod 2),
      ∀ γ, R γ = LinearMap.toMatrix (b.reindex idxEquiv) (b.reindex idxEquiv) (ρ γ) :=
    ⟨fun γ => LinearMap.toMatrix (b.reindex idxEquiv) (b.reindex idxEquiv) (ρ γ), fun _ => rfl⟩
  have hRmul : ∀ γ δ : Γ, R (γ * δ) = R γ * R δ := by
    intro γ δ
    rw [hR, hR, hR, map_mul, LinearMap.toMatrix_mul]
  have hR1 : R 1 = 1 := by
    rw [hR, map_one, LinearMap.toMatrix_one]
  have hRpow : ∀ (γ : Γ) (n : ℕ), R (γ ^ n) = R γ ^ n := by
    intro γ n
    induction n with
    | zero => rw [pow_zero, pow_zero, hR1]
    | succ k ih => rw [pow_succ, pow_succ, hRmul, ih]
  have hRm : ∀ k, R (D.m k) = Xfin (θ k) (D.σ k) (cfTab D.w₁ D.v₀ (D.u k)) := by
    intro k
    rw [hR, toMatrix_reindex b idxEquiv (ρ (D.m k)),
      toMatrix_rho D ρ v0 b x hb0 hb1 hx htx hPx k (θ k) (hθ k)]
    rfl
  have hRn : ∀ s, R (D.n s) = Xfin (θ (iN s)) (D.σ (iN s)) (cfTab D.w₁ D.v₀ (D.u (iN s))) :=
    fun s => (congrArg R (D.hmn s).symm).trans (hRm (iN s))
  have hRy : ∀ k : Fin 3, R (D.m (iY k)) = Xfin 1 (D.σ (iY k)) (cfTab D.w₁ D.v₀ (D.u (iY k))) :=
    fun k => by rw [hRm, hθ1 k]
  have hRz : ∀ k : Fin 3, R (D.m (iZ k)) = Xfin 1 (D.σ (iZ k)) (cfTab D.w₁ D.v₀ (D.u (iZ k))) :=
    fun k => by rw [hRm, hθ2 k]
  have hgm : ∀ k : Fin 3, D.g * D.m (iY k) = D.m (iZ k) * D.g := fun k => by
    rw [D.hzdef k, inv_mul_cancel_right]
  have h1 : ∀ k : Fin 3, R D.g * Xfin 1 (D.σ (iY k)) (cfTab D.w₁ D.v₀ (D.u (iY k))) =
      Xfin 1 (D.σ (iZ k)) (cfTab D.w₁ D.v₀ (D.u (iZ k))) * R D.g := by
    intro k
    rw [← hRy k, ← hRz k, ← hRmul, ← hRmul, hgm k]
  have h2 : R D.g ^ 3 = 1 := by
    rw [← hRpow, D.hg3, hR1]
  have hwp : ∀ w : List (Fin 2 × ℕ),
      wordProd (fun s => Xfin (θ (iN s)) (D.σ (iN s)) (cfTab D.w₁ D.v₀ (D.u (iN s)))) w =
        R (wordProd D.n w) := by
    intro w
    induction w with
    | nil => simp only [wordProd, List.map_nil, List.prod_nil, hR1]
    | cons q w ih =>
      simp only [wordProd, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih, hRmul, hRpow, ← hRn q.1]
  have h3 : ∀ j, (wordProd (fun s => Xfin (θ (iN s)) (D.σ (iN s)) (cfTab D.w₁ D.v₀ (D.u (iN s))))
      (D.tw j) * R D.g) ^ D.kk j = 1 := by
    intro j
    rw [hwp (D.tw j), ← hRmul, ← hRpow, D.hrel j, hR1]
  obtain ⟨S, hS, hSX, hSM⟩ := D.hEnum (fun s => θ (iN s)) (R D.g) h1 h2 h3
  have hQ : IsUnit (Qfin S) := isUnit_Qfin hS
  obtain ⟨b', hb'⟩ := exists_basis_change (b.reindex idxEquiv) (Qfin S) hQ
  have key : ∀ γ : Γ, Qfin S * R γ = LinearMap.toMatrix b' b' (ρ γ) * Qfin S := fun γ => by
    rw [hR]
    exact hb' (ρ γ)
  have hSX' : ∀ s, Qfin S * R (D.n s) = D.X0 s * Qfin S := fun s => by
    rw [hRn s]
    exact hSX s
  refine ⟨b', fun s => ?_, ?_⟩
  · have e1 := key (D.n s)
    rw [hSX' s] at e1
    exact (hQ.mul_right_cancel e1).symm
  · have e2 := key D.g
    rw [hSM] at e2
    exact (hQ.mul_right_cancel e2).symm

private theorem intertwine_of_toMatrix_eq {ι₀ : Type*} [Fintype ι₀] [DecidableEq ι₀]
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]
    (f : V₁ ≃ₗ[ZMod 2] V₂) (b : Module.Basis ι₀ (ZMod 2) V₁) (b' : Module.Basis ι₀ (ZMod 2) V₂)
    (hf : ∀ i, f (b i) = b' i) (g : Module.End (ZMod 2) V₁) (g' : Module.End (ZMod 2) V₂)
    (h : LinearMap.toMatrix b b g = LinearMap.toMatrix b' b' g') :
    ∀ v, f (g v) = g' (f v) := by
  have key : (f : V₁ →ₗ[ZMod 2] V₂).comp g = g'.comp (f : V₁ →ₗ[ZMod 2] V₂) := by
    apply b.ext
    intro i
    have e1 : g (b i) = ∑ j, LinearMap.toMatrix b b g j i • b j := by
      simp only [LinearMap.toMatrix_apply, Module.Basis.sum_repr]
    have e2 : g' (b' i) = ∑ j, LinearMap.toMatrix b' b' g' j i • b' j := by
      simp only [LinearMap.toMatrix_apply, Module.Basis.sum_repr]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hf i, e2, e1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hf j, h]
  intro v
  exact LinearMap.congr_fun key v

include D in
theorem exists_equiv {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    (ρ' : Representation (ZMod 2) Γ V') (hV : Module.finrank (ZMod 2) V = 22)
    (hV' : Module.finrank (ZMod 2) V' = 22) (hnt : ∃ v, ρ (ι v) ≠ 1) (hnt' : ∃ v, ρ' (ι v) ≠ 1) :
    ∃ ψ : V ≃ₗ[ZMod 2] V', ∀ γ v, ψ (ρ γ v) = ρ' γ (ψ v) := by
  obtain ⟨b, hb1, hb2⟩ := normal_form D ρ hV hnt
  obtain ⟨b', hb1', hb2'⟩ := normal_form D ρ' hV' hnt'
  obtain ⟨f, hf⟩ : ∃ f : V ≃ₗ[ZMod 2] V', ∀ i, f (b i) = b' i :=
    ⟨b.equiv b' (Equiv.refl _), fun i => by simp⟩
  have hS : ∀ s ∈ ({D.n 0, D.n 1, D.g} : Set Γ), ∀ v, f (ρ s v) = ρ' s (f v) := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact intertwine_of_toMatrix_eq f b b' hf (ρ (D.n 0)) (ρ' (D.n 0))
        ((hb1 0).trans (hb1' 0).symm)
    · exact intertwine_of_toMatrix_eq f b b' hf (ρ (D.n 1)) (ρ' (D.n 1))
        ((hb1 1).trans (hb1' 1).symm)
    · exact intertwine_of_toMatrix_eq f b b' hf (ρ D.g) (ρ' D.g) (hb2.trans hb2'.symm)
  obtain ⟨ψ, hψ⟩ := CFSG.Monster.GMS.Griess13.exists_equiv_of_closure_eq_top ρ ρ' f D.hgen hS
  exact ⟨ψ, hψ⟩

end Main

end CFSG.GF2Type.Widths1112.Co2Module
