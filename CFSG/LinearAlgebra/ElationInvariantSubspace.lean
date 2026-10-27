module

public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.LinearAlgebra

open Matrix Module
open scoped Pointwise

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def shiftEnd (t : GL (Fin n) K) : Module.End K ((Fin n → K)) :=
  Matrix.toLin' ((t : Matrix (Fin n) (Fin n) K) - 1)

@[expose] def glToLinHom : GL (Fin n) K →* ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K ((Fin n → K))).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin).toMonoidHom

@[expose] def glStabilizer (U : Submodule K ((Fin n → K))) : Subgroup (GL (Fin n) K) :=
  (MulAction.stabilizer ((Fin n → K) ≃ₗ[K] (Fin n → K)) U).comap glToLinHom

theorem mem_glStabilizer_iff {U : Submodule K ((Fin n → K))} {x : GL (Fin n) K} :
    x ∈ glStabilizer U ↔
      Submodule.map (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K)) U = U := by
  rw [glStabilizer, Subgroup.mem_comap, Submodule.mem_stabilizer_submodule_iff_map_eq]
  have h : (DistribSMul.toLinearMap K ((Fin n → K)) (glToLinHom x)) =
      Matrix.toLin' (x : Matrix (Fin n) (Fin n) K) := by
    refine LinearMap.ext fun v => ?_
    change (glToLinHom x) v = Matrix.mulVecLin (x : Matrix (Fin n) (Fin n) K) v
    rw [glToLinHom, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MulEquiv.coe_toMonoidHom]
    change (LinearMap.GeneralLinearGroup.generalLinearEquiv K ((Fin n → K))
        (Matrix.GeneralLinearGroup.toLin x) : (Fin n → K) →ₗ[K] (Fin n → K)) v =
      Matrix.mulVecLin (x : Matrix (Fin n) (Fin n) K) v
    rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.toLin_apply]
  rw [h]

private theorem finrank_map_toLin' (g : GL (Fin n) K) (p : Submodule K ((Fin n → K))) :
    finrank K (Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) p) =
      finrank K p := by
  have h : (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) =
      ((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv : (Fin n → K) →ₗ[K] (Fin n → K)) := by
    refine LinearMap.ext fun v => ?_
    change Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) K) v =
      (Matrix.GeneralLinearGroup.toLin g : (Fin n → K) →ₗ[K] (Fin n → K)) v
    rw [Matrix.GeneralLinearGroup.toLin_apply]
  rw [h, LinearEquiv.finrank_map_eq]

theorem mem_glStabilizer_of_map_le {U : Submodule K ((Fin n → K))} {x : GL (Fin n) K}
    (h : Submodule.map (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K)) U ≤ U) :
    x ∈ glStabilizer U := by
  rw [mem_glStabilizer_iff]
  exact Submodule.eq_of_le_of_finrank_eq h (by rw [finrank_map_toLin'])

private theorem mulVec_eq_add_shiftEnd (x : GL (Fin n) K) (u : (Fin n → K)) :
    (x : Matrix (Fin n) (Fin n) K) *ᵥ u = u + shiftEnd x u := by
  have hx : Matrix.toLin' (x : Matrix (Fin n) (Fin n) K) = shiftEnd x + 1 := by
    have h : ((x : Matrix (Fin n) (Fin n) K) - 1) + 1 = (x : Matrix (Fin n) (Fin n) K) :=
      sub_add_cancel _ _
    calc Matrix.toLin' (x : Matrix (Fin n) (Fin n) K) =
        Matrix.toLin' (((x : Matrix (Fin n) (Fin n) K) - 1) + 1) := by rw [h]
      _ = shiftEnd x + 1 := by
            rw [map_add, shiftEnd, Matrix.toLin'_one]
            rfl
  rw [← Matrix.toLin'_apply, hx]
  simp [add_comm]

private theorem mem_glStabilizer_of_range_le {U p : Submodule K ((Fin n → K))} (hpU : p ≤ U)
    {x : GL (Fin n) K} (hx : LinearMap.range (shiftEnd x) ≤ p) : x ∈ glStabilizer U := by
  apply mem_glStabilizer_of_map_le
  rintro w ⟨u, hu, rfl⟩
  rw [Matrix.toLin'_apply, mulVec_eq_add_shiftEnd]
  exact U.add_mem hu (hpU (hx ⟨u, rfl⟩))

private theorem finrank_sup_map_toLin'_le_two (g : GL (Fin n) K)
    {p : Submodule K ((Fin n → K))} (hp : finrank K p = 1) :
    finrank K (p ⊔ Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) p :
      Submodule K ((Fin n → K))) ≤ 2 := by
  have hgp : finrank K (Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) p) = 1 := by
    rw [finrank_map_toLin', hp]
  calc finrank K (p ⊔ Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) p :
        Submodule K ((Fin n → K))) ≤
      finrank K p + finrank K (Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) p) :=
        Submodule.finrank_add_le_finrank_add_finrank p _
    _ = 1 + 1 := by rw [hp, hgp]
    _ = 2 := by norm_num

private theorem shiftEnd_conj (g t : GL (Fin n) K) :
    shiftEnd (g * t * g⁻¹) =
      Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) * shiftEnd t *
        Matrix.toLin' ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hgg : (g : Matrix (Fin n) (Fin n) K) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa using congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) (mul_inv_cancel g)
  have hsub : ((g * t * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
      (g : Matrix (Fin n) (Fin n) K) * ((t : Matrix (Fin n) (Fin n) K) - 1) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_mul, Units.val_mul]
    calc (g : Matrix (Fin n) (Fin n) K) * t *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1 =
        (g : Matrix (Fin n) (Fin n) K) * t *
            ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
          (g : Matrix (Fin n) (Fin n) K) * 1 *
            ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [mul_one, hgg]
      _ = (g : Matrix (Fin n) (Fin n) K) * ((t : Matrix (Fin n) (Fin n) K) - 1) *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by noncomm_ring
  rw [shiftEnd, shiftEnd, hsub, Matrix.toLin'_mul, Matrix.toLin'_mul]
  simp only [Module.End.mul_eq_comp, LinearMap.comp_assoc]

private theorem range_shiftEnd_conj_le (g t : GL (Fin n) K) :
    LinearMap.range (shiftEnd (g * t * g⁻¹)) ≤
      Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K))
        (LinearMap.range (shiftEnd t)) := by
  rw [shiftEnd_conj]
  rintro y ⟨u, rfl⟩
  exact ⟨shiftEnd t (Matrix.toLin' ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) u),
    ⟨_, rfl⟩, rfl⟩

private theorem mem_glStabilizer_of_ker_le {U l : Submodule K ((Fin n → K))}
    (hlU : U ≤ l) {x : GL (Fin n) K} (hx : l ≤ LinearMap.ker (shiftEnd x)) :
    x ∈ glStabilizer U := by
  apply mem_glStabilizer_of_map_le
  rintro w ⟨u, hu, rfl⟩
  have hzero : shiftEnd x u = 0 := by
    have := hx (hlU hu)
    rwa [LinearMap.mem_ker] at this
  rw [Matrix.toLin'_apply, mulVec_eq_add_shiftEnd, hzero, add_zero]
  exact hu

theorem exists_invariant_of_common_centre (hn : 3 ≤ n) (T : Subgroup (GL (Fin n) K))
    (g : GL (Fin n) K) {p : Submodule K ((Fin n → K))} (hp : finrank K p = 1)
    (hcent : ∀ t ∈ T, LinearMap.range (shiftEnd t) ≤ p) :
    ∃ U : Submodule K ((Fin n → K)), U ≠ ⊥ ∧ U ≠ ⊤ ∧
      ∀ x ∈ T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T, ∀ u ∈ U,
        (x : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ U := by
  let U : Submodule K ((Fin n → K)) :=
    p ⊔ Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) p
  have hUbot : U ≠ ⊥ := by
    have hpbot : p ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hp
      omega
    intro h
    exact hpbot (le_bot_iff.mp (h ▸ le_sup_left))
  have hUtop : U ≠ ⊤ := by
    intro h
    have hle := finrank_sup_map_toLin'_le_two (K := K) g hp
    have hUle : finrank K U ≤ 2 := hle
    have h3 : finrank K U = n := by
      rw [h, finrank_top, Module.finrank_fin_fun (R := K) (n := n)]
    omega
  have hTpres : T ≤ glStabilizer U := fun a ha =>
    mem_glStabilizer_of_range_le (U := U) (p := p) le_sup_left (hcent a ha)
  have hconjpres : CFSG.CGT.Timmesfeld75.conjSubgroup g T ≤ glStabilizer U := by
    intro b hb
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup] at hb
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
    simp only [MulEquiv.coe_toMonoidHom]
    have hconj : (MulAut.conj g t : GL (Fin n) K) = g * t * g⁻¹ := by
      simp only [MulAut.conj_apply]
    refine mem_glStabilizer_of_range_le (U := U)
      (p := Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) p) le_sup_right ?_
    rw [hconj]
    exact (range_shiftEnd_conj_le g t).trans (Submodule.map_mono (hcent t ht))
  refine ⟨U, hUbot, hUtop, ?_⟩
  intro x hx u hu
  have hx' : x ∈ glStabilizer U := (sup_le hTpres hconjpres) hx
  have hmap := mem_glStabilizer_iff.mp hx'
  have hmem : Matrix.toLin' (x : Matrix (Fin n) (Fin n) K) u ∈
      Submodule.map (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K)) U :=
    ⟨u, hu, rfl⟩
  rw [hmap] at hmem
  simpa only [Matrix.toLin'_apply] using hmem

theorem permMatrixHom_conj_apply {m : ℕ} (σ : Equiv.Perm (Fin m))
    (M : Matrix (Fin m) (Fin m) K) (a b : Fin m) :
    (Matrix.permMatrixHom (R := K) σ⁻¹ * M * Matrix.permMatrixHom (R := K) σ) a b =
      M (σ a) (σ b) := by
  simp only [Matrix.permMatrixHom_apply, inv_inv]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [Matrix.submatrix_apply, Equiv.Perm.inv_def]

theorem exists_invariant_of_common_axis (hn : 3 ≤ n) (T : Subgroup (GL (Fin n) K))
    (g : GL (Fin n) K) {l : Submodule K ((Fin n → K))} (hl : finrank K l = n - 1)
    (haxis : ∀ t ∈ T, l ≤ LinearMap.ker (shiftEnd t)) :
    ∃ U : Submodule K ((Fin n → K)), U ≠ ⊥ ∧ U ≠ ⊤ ∧
      ∀ x ∈ T ⊔ CFSG.CGT.Timmesfeld75.conjSubgroup g T, ∀ u ∈ U,
        (x : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ U := by
  let gl : Submodule K ((Fin n → K)) :=
    Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) l
  let U : Submodule K ((Fin n → K)) := l ⊓ gl
  have hgl : finrank K gl = n - 1 := by
    change finrank K (Submodule.map (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K)) l) = n - 1
    rw [finrank_map_toLin', hl]
  have hUbot : U ≠ ⊥ := by
    intro h
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq l gl
    have hsup : finrank K (l ⊔ gl : Submodule K ((Fin n → K))) ≤ n := by
      calc finrank K (l ⊔ gl : Submodule K ((Fin n → K))) ≤ finrank K ((Fin n → K)) :=
            Submodule.finrank_le _
        _ = n := Module.finrank_fin_fun (R := K) (n := n)
    have hzero : finrank K U = 0 := by rw [h, finrank_bot]
    have hzero' : finrank K (l ⊓ gl : Submodule K ((Fin n → K))) = 0 := hzero
    omega
  have hUtop : U ≠ ⊤ := by
    have hl_top : l ≠ ⊤ := by
      intro htop
      rw [htop, finrank_top, Module.finrank_fin_fun (R := K) (n := n)] at hl
      omega
    intro h
    change (l ⊓ gl : Submodule K ((Fin n → K))) = ⊤ at h
    have htop' : (⊤ : Submodule K ((Fin n → K))) ≤ l := by
      rw [← h]
      exact inf_le_left
    exact hl_top (top_le_iff.mp htop')
  have hTpres : T ≤ glStabilizer U := fun a ha =>
    mem_glStabilizer_of_ker_le (U := U) (l := l) inf_le_left (haxis a ha)
  have hconjpres : CFSG.CGT.Timmesfeld75.conjSubgroup g T ≤ glStabilizer U := by
    intro b hb
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup] at hb
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
    simp only [MulEquiv.coe_toMonoidHom]
    have hconj : (MulAut.conj g t : GL (Fin n) K) = g * t * g⁻¹ := by
      simp only [MulAut.conj_apply]
    refine mem_glStabilizer_of_ker_le (U := U) (l := gl) inf_le_right ?_
    rw [hconj]
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [shiftEnd_conj]
    simp [Module.End.mul_apply]
    have hvt : shiftEnd t v = 0 := by
      have := haxis t ht hv
      rwa [LinearMap.mem_ker] at this
    rw [hvt]
    simp
  refine ⟨U, hUbot, hUtop, ?_⟩
  intro x hx u hu
  have hx' : x ∈ glStabilizer U := (sup_le hTpres hconjpres) hx
  have hmap := mem_glStabilizer_iff.mp hx'
  have hmem : Matrix.toLin' (x : Matrix (Fin n) (Fin n) K) u ∈
      Submodule.map (Matrix.toLin' (x : Matrix (Fin n) (Fin n) K)) U :=
    ⟨u, hu, rfl⟩
  rw [hmap] at hmem
  simpa only [Matrix.toLin'_apply] using hmem

end CFSG.LinearAlgebra

end
