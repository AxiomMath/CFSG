module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3ExtExcludes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.ComponentClassification Matrix

theorem single_mul_single_self : ∀ i j : Fin 3, i ≠ j →
    ((1 : Mat3) + Matrix.single i j 1) * (1 + Matrix.single i j 1) = 1 := by
  decide

@[expose] def transvecGL (i j : Fin 3) (h : i ≠ j) : GL32 :=
  ⟨1 + Matrix.single i j 1, 1 + Matrix.single i j 1, single_mul_single_self i j h,
    single_mul_single_self i j h⟩

theorem transvecGL_val (i j : Fin 3) (h : i ≠ j) :
    (transvecGL i j h : Mat3) = 1 + Matrix.single i j 1 := rfl

theorem transvecGL_inv_val (i j : Fin 3) (h : i ≠ j) :
    ((transvecGL i j h)⁻¹ : GL32) = transvecGL i j h := rfl

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem comm_six : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 0 1 1 =
      Matrix.single 0 1 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 1 0 1 =
      Matrix.single 1 0 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 0 2 1 =
      Matrix.single 0 2 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 2 0 1 =
      Matrix.single 2 0 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 1 2 1 =
      Matrix.single 1 2 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 2 1 1 =
      Matrix.single 2 1 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] : Mat3) = 0 ∨ (!![a, b, c; d, e, f; g, h, i] : Mat3) = 1 := by
  decide

theorem twist_six : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 0 1 1 =
      Matrix.single 1 0 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 1 0 1 =
      Matrix.single 0 1 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 0 2 1 =
      Matrix.single 2 0 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 2 0 1 =
      Matrix.single 0 2 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 1 2 1 =
      Matrix.single 2 1 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] * Matrix.single 2 1 1 =
      Matrix.single 1 2 1 * !![a, b, c; d, e, f; g, h, i]) →
    (!![a, b, c; d, e, f; g, h, i] : Mat3) = 0 := by
  decide

theorem eq_zero_or_one_of_comm (M : Mat3)
    (h : ∀ i j : Fin 3, i ≠ j → M * Matrix.single i j 1 = Matrix.single i j 1 * M) :
    M = 0 ∨ M = 1 := by
  have e := Matrix.eta_fin_three M
  have key := comm_six (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2)
    (by rw [← e]; exact h 0 1 (by decide)) (by rw [← e]; exact h 1 0 (by decide))
    (by rw [← e]; exact h 0 2 (by decide)) (by rw [← e]; exact h 2 0 (by decide))
    (by rw [← e]; exact h 1 2 (by decide)) (by rw [← e]; exact h 2 1 (by decide))
  rcases key with h0 | h1
  · exact Or.inl (e.trans h0)
  · exact Or.inr (e.trans h1)

theorem eq_zero_of_twist (M : Mat3)
    (h : ∀ i j : Fin 3, i ≠ j → M * Matrix.single i j 1 = Matrix.single j i 1 * M) : M = 0 := by
  have e := Matrix.eta_fin_three M
  have key := twist_six (M 0 0) (M 0 1) (M 0 2) (M 1 0) (M 1 1) (M 1 2) (M 2 0) (M 2 1) (M 2 2)
    (by rw [← e]; exact h 0 1 (by decide)) (by rw [← e]; exact h 1 0 (by decide))
    (by rw [← e]; exact h 0 2 (by decide)) (by rw [← e]; exact h 2 0 (by decide))
    (by rw [← e]; exact h 1 2 (by decide)) (by rw [← e]; exact h 2 1 (by decide))
  exact e.trans key

theorem single_mem_traceZero {i j : Fin 3} (hij : i ≠ j) :
    (Matrix.single i j (1 : ZMod 2) : Mat3) ∈ traceZero := by
  rw [mem_traceZero_iff_trace]
  revert i j
  decide

theorem toMatrix_intertwine (f : Vec3 →ₗ[ZMod 2] Vec3) (A B : Mat3)
    (h : ∀ u, f (A *ᵥ u) = B *ᵥ f u) : LinearMap.toMatrix' f * A = B * LinearMap.toMatrix' f := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.comp_apply, Matrix.toLin'_apply]
  exact h u

theorem repA_injective : Function.Injective repA := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hcomm : ∀ i j : Fin 3, i ≠ j →
      (g : Mat3) * Matrix.single i j 1 = Matrix.single i j 1 * (g : Mat3) := by
    intro i j hij
    have h1 := congrArg (fun φ : traceZero ≃ₗ[ZMod 2] traceZero =>
      ((φ ⟨Matrix.single i j 1, single_mem_traceZero hij⟩ : traceZero) : Mat3)) hg
    have h2 : (g : Mat3) * Matrix.single i j 1 * ((g⁻¹ : GL32) : Mat3) =
        Matrix.single i j 1 := h1
    have h3 := congrArg (fun M => M * (g : Mat3)) h2
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at h3
    exact h3
  rcases eq_zero_or_one_of_comm (g : Mat3) hcomm with h0 | h1
  · exfalso
    have h4 : (g : Mat3) * ((g⁻¹ : GL32) : Mat3) = 1 := Units.mul_inv g
    rw [h0, Matrix.zero_mul] at h4
    exact zero_ne_one h4
  · exact Units.ext h1

theorem repV_injective : Function.Injective repV := fun _ _ hgh =>
  Matrix.GeneralLinearGroup.toLin.injective
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vec3).injective hgh)

theorem repDual_injective : Function.Injective repDual :=
  repV_injective.comp (Function.Involutive.injective tauHom_tauHom)

theorem repPS_injective : Function.Injective repPS := by
  intro g h hgh
  apply repV_injective
  refine LinearEquiv.ext fun u => ?_
  have := congrArg (fun φ : P6 ≃ₗ[ZMod 2] P6 => (φ (u, 0)).1) hgh
  simpa [repPS_apply] using this

theorem toMatrix_one_apply (f : Vec3 →ₗ[ZMod 2] Vec3) (h : LinearMap.toMatrix' f = 1) (u : Vec3) :
    f u = u := by
  have h1 := Matrix.toLin'_toMatrix' f
  rw [h, Matrix.toLin'_one] at h1
  exact (LinearMap.congr_fun h1 u).symm

theorem toMatrix_zero_apply (f : Vec3 →ₗ[ZMod 2] Vec3) (h : LinearMap.toMatrix' f = 0) (u : Vec3) :
    f u = 0 := by
  have h1 := Matrix.toLin'_toMatrix' f
  rw [h, map_zero] at h1
  exact (LinearMap.congr_fun h1 u).symm

theorem transvec_conj_comm (M : Mat3) (i j : Fin 3) (hij : i ≠ j)
    (h : M * (transvecGL i j hij : Mat3) = (transvecGL i j hij : Mat3) * M) :
    M * Matrix.single i j 1 = Matrix.single i j 1 * M := by
  rw [transvecGL_val, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  exact add_left_cancel h

theorem transvec_conj_twist (M : Mat3) (i j : Fin 3) (hij : i ≠ j)
    (h : M * (transvecGL i j hij : Mat3) = (((transvecGL i j hij)⁻¹ : GL32) : Mat3)ᵀ * M) :
    M * Matrix.single i j 1 = Matrix.single j i 1 * M := by
  rw [transvecGL_inv_val, transvecGL_val, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h
  exact add_left_cancel h

theorem centralizer_repPS (N : P6 ≃ₗ[ZMod 2] P6)
    (hN : ∀ g x, N (repPS g x) = repPS g (N x)) : N = 1 := by
  let a : Vec3 →ₗ[ZMod 2] Vec3 := LinearMap.fst (ZMod 2) Vec3 Vec3 ∘ₗ (N : P6 →ₗ[ZMod 2] P6) ∘ₗ
    LinearMap.inl (ZMod 2) Vec3 Vec3
  let b : Vec3 →ₗ[ZMod 2] Vec3 := LinearMap.fst (ZMod 2) Vec3 Vec3 ∘ₗ (N : P6 →ₗ[ZMod 2] P6) ∘ₗ
    LinearMap.inr (ZMod 2) Vec3 Vec3
  let c : Vec3 →ₗ[ZMod 2] Vec3 := LinearMap.snd (ZMod 2) Vec3 Vec3 ∘ₗ (N : P6 →ₗ[ZMod 2] P6) ∘ₗ
    LinearMap.inl (ZMod 2) Vec3 Vec3
  let d : Vec3 →ₗ[ZMod 2] Vec3 := LinearMap.snd (ZMod 2) Vec3 Vec3 ∘ₗ (N : P6 →ₗ[ZMod 2] P6) ∘ₗ
    LinearMap.inr (ZMod 2) Vec3 Vec3
  have hNu : ∀ u : Vec3, N (u, 0) = (a u, c u) := fun u => rfl
  have hNw : ∀ w : Vec3, N (0, w) = (b w, d w) := fun w => rfl
  have hdec : ∀ u w, N (u, w) = (a u + b w, c u + d w) := by
    intro u w
    have h : ((u, w) : P6) = (u, 0) + (0, w) := by simp
    rw [h, map_add, hNu, hNw, Prod.mk_add_mk]
  have eqa : ∀ (g : GL32) (u : Vec3), a ((g : Mat3) *ᵥ u) = (g : Mat3) *ᵥ a u := by
    intro g u
    have h1 := hN g (u, 0)
    rw [repPS_apply, map_zero, hNu, hNu, repPS_apply] at h1
    exact congrArg Prod.fst h1
  have eqc : ∀ (g : GL32) (u : Vec3), c ((g : Mat3) *ᵥ u) = ((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ c u := by
    intro g u
    have h1 := hN g (u, 0)
    rw [repPS_apply, map_zero, hNu, hNu, repPS_apply] at h1
    exact congrArg Prod.snd h1
  have eqb : ∀ (g : GL32) (w : Vec3), b (((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ w) = (g : Mat3) *ᵥ b w := by
    intro g w
    have h1 := hN g (0, w)
    rw [repPS_apply, map_zero, hNw, hNw, repPS_apply] at h1
    exact congrArg Prod.fst h1
  have eqd : ∀ (g : GL32) (w : Vec3),
      d (((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ w) = ((g⁻¹ : GL32) : Mat3)ᵀ *ᵥ d w := by
    intro g w
    have h1 := hN g (0, w)
    rw [repPS_apply, map_zero, hNw, hNw, repPS_apply] at h1
    exact congrArg Prod.snd h1
  have hMa : ∀ g : GL32, LinearMap.toMatrix' a * (g : Mat3) = (g : Mat3) * LinearMap.toMatrix' a :=
    fun g => toMatrix_intertwine a _ _ (eqa g)
  have hMc : ∀ g : GL32, LinearMap.toMatrix' c * (g : Mat3) =
      ((g⁻¹ : GL32) : Mat3)ᵀ * LinearMap.toMatrix' c := fun g => toMatrix_intertwine c _ _ (eqc g)
  have hMb : ∀ g : GL32, LinearMap.toMatrix' b * ((g⁻¹ : GL32) : Mat3)ᵀ =
      (g : Mat3) * LinearMap.toMatrix' b := fun g => toMatrix_intertwine b _ _ (eqb g)
  have hMd : ∀ g : GL32, LinearMap.toMatrix' d * ((g⁻¹ : GL32) : Mat3)ᵀ =
      ((g⁻¹ : GL32) : Mat3)ᵀ * LinearMap.toMatrix' d := fun g => toMatrix_intertwine d _ _ (eqd g)
  have hc0 : LinearMap.toMatrix' c = 0 := eq_zero_of_twist _ fun i j hij =>
    transvec_conj_twist _ i j hij (hMc _)
  have hb0 : LinearMap.toMatrix' b = 0 := eq_zero_of_twist _ fun i j hij => by
    have h1 := hMb (transvecGL j i hij.symm)
    rw [transvecGL_inv_val, transvecGL_val, Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_single, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    exact add_left_cancel h1
  have hMa' : LinearMap.toMatrix' a = 0 ∨ LinearMap.toMatrix' a = 1 :=
    eq_zero_or_one_of_comm _ fun i j hij => transvec_conj_comm _ i j hij (hMa _)
  have hMd' : LinearMap.toMatrix' d = 0 ∨ LinearMap.toMatrix' d = 1 :=
    eq_zero_or_one_of_comm _ fun i j hij => by
      have h1 := hMd (transvecGL j i hij.symm)
      rw [transvecGL_inv_val, transvecGL_val, Matrix.transpose_add, Matrix.transpose_one,
        Matrix.transpose_single, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.one_mul] at h1
      exact add_left_cancel h1
  have hne : (Pi.single 0 1 : Vec3) ≠ 0 := by decide
  have ha1 : LinearMap.toMatrix' a = 1 := by
    rcases hMa' with h | h
    · exfalso
      have h1 : N (Pi.single 0 1, 0) = N 0 := by
        rw [hNu, toMatrix_zero_apply a h, toMatrix_zero_apply c hc0, map_zero]
        rfl
      have h2 := N.injective h1
      exact hne (congrArg Prod.fst h2)
    · exact h
  have hd1 : LinearMap.toMatrix' d = 1 := by
    rcases hMd' with h | h
    · exfalso
      have h1 : N (0, Pi.single 0 1) = N 0 := by
        rw [hNw, toMatrix_zero_apply d h, toMatrix_zero_apply b hb0, map_zero]
        rfl
      have h2 := N.injective h1
      exact hne (congrArg Prod.snd h2)
    · exact h
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, w⟩ := x
  rw [hdec, toMatrix_one_apply a ha1, toMatrix_one_apply d hd1, toMatrix_zero_apply b hb0,
    toMatrix_zero_apply c hc0, add_zero, zero_add]
  rfl

theorem glGraphAut_eq_tauAut : CatalogueBGraphForm.glGraphAut 3 (ZMod 2) = tauAut :=
  MulEquiv.ext fun g => Units.ext
    ((CatalogueBGraphForm.glGraphAut_matrix 3 (ZMod 2) g).trans (tauHom_val g).symm)

section GoodRep

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (ρ : H32 →* (E ≃ₗ[ZMod 2] E))

structure GoodRep : Prop where
  faithful : Function.Injective (ρ.comp sIncl)
  centralizer : ∀ φ : E ≃ₗ[ZMod 2] E,
    (∀ g : GL32, φ * ρ (sIncl g) = ρ (sIncl g) * φ) → φ = 1

variable {ρ}

theorem GoodRep.injective (hρ : GoodRep ρ) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro h hh
  rcases exists_eq_sIncl_mul h with h1 | h1
  · rw [h1] at hh ⊢
    have h2 : (ρ.comp sIncl) h.left = (ρ.comp sIncl) 1 := by
      rw [map_one]
      exact hh
    rw [hρ.faithful h2, map_one]
  · exfalso
    rw [h1, map_mul] at hh
    have ht : ρ tGen = (ρ (sIncl h.left))⁻¹ := eq_inv_of_mul_eq_one_right hh
    have hτ : ∀ g : GL32, tauHom g = (h.left)⁻¹ * g * (h.left)⁻¹⁻¹ := by
      intro g
      apply hρ.faithful
      show ρ (sIncl (tauHom g)) = ρ (sIncl ((h.left)⁻¹ * g * (h.left)⁻¹⁻¹))
      rw [← tGen_conj]
      simp [ht]
    refine glGraphAut_ne_conj (h.left)⁻¹ ?_
    rw [glGraphAut_eq_tauAut]
    exact MulEquiv.ext fun g => by rw [MulAut.conj_apply]; exact hτ g

theorem GoodRep.mem_range_of_normalizes (hρ : GoodRep ρ) {φ : E ≃ₗ[ZMod 2] E}
    (hφ : ∀ g : GL32, ∃ g' : GL32, φ * ρ (sIncl g) * φ⁻¹ = ρ (sIncl g')) : φ ∈ ρ.range := by
  choose α hα using hφ
  have hmul : ∀ g h, α (g * h) = α g * α h := by
    intro g h
    apply hρ.faithful
    show ρ (sIncl (α (g * h))) = ρ (sIncl (α g * α h))
    rw [← hα (g * h), map_mul, map_mul, map_mul, map_mul, ← hα g, ← hα h]
    group
  have hinj : Function.Injective α := by
    intro g h hgh
    apply hρ.faithful
    show ρ (sIncl g) = ρ (sIncl h)
    have e1 := hα g
    have e2 := hα h
    rw [hgh] at e1
    exact mul_left_cancel (mul_right_cancel (e1.trans e2.symm))
  have hbij : Function.Bijective α := Finite.injective_iff_bijective.1 hinj
  let αe : MulAut GL32 := MulEquiv.ofBijective (MonoidHom.mk' α hmul) hbij
  have hαe : ∀ g, αe g = α g := fun g => rfl
  rcases aut_GL32_cases αe with ⟨s, hs⟩ | ⟨s, hs⟩
  · have hαg : ∀ g, α g = s * g * s⁻¹ := fun g => by
      rw [← hαe, hs, MulAut.conj_apply]
    have hcomm : ∀ g : GL32, (ρ (sIncl s))⁻¹ * φ * ρ (sIncl g) =
        ρ (sIncl g) * ((ρ (sIncl s))⁻¹ * φ) := by
      intro g
      have h1 := hα g
      rw [hαg g] at h1
      have h2 : φ * ρ (sIncl g) = ρ (sIncl (s * g * s⁻¹)) * φ := by
        rw [← h1]
        group
      calc (ρ (sIncl s))⁻¹ * φ * ρ (sIncl g) = (ρ (sIncl s))⁻¹ * (φ * ρ (sIncl g)) := by group
        _ = (ρ (sIncl s))⁻¹ * (ρ (sIncl (s * g * s⁻¹)) * φ) := by rw [h2]
        _ = ρ (sIncl g) * ((ρ (sIncl s))⁻¹ * φ) := by
          simp only [map_mul, map_inv]
          group
    have h3 := hρ.centralizer _ hcomm
    exact ⟨sIncl s, inv_mul_eq_one.1 h3⟩
  · have hαg : ∀ g, α g = s * tauHom g * s⁻¹ := fun g => by
      rw [← hαe, hs, MulAut.mul_apply, glGraphAut_eq_tauAut, MulAut.conj_apply]
      rfl
    have hcomm : ∀ g : GL32, (ρ (sIncl s * tGen))⁻¹ * φ * ρ (sIncl g) =
        ρ (sIncl g) * ((ρ (sIncl s * tGen))⁻¹ * φ) := by
      intro g
      have h1 := hα g
      rw [hαg g] at h1
      have h4 : ρ (sIncl (tauHom g)) = ρ tGen * ρ (sIncl g) * (ρ tGen)⁻¹ := by
        rw [← tGen_conj]
        simp
      have h2 : φ * ρ (sIncl g) =
          ρ (sIncl s) * (ρ tGen * ρ (sIncl g) * (ρ tGen)⁻¹) * (ρ (sIncl s))⁻¹ * φ := by
        have h5 : ρ (sIncl (s * tauHom g * s⁻¹)) =
            ρ (sIncl s) * (ρ tGen * ρ (sIncl g) * (ρ tGen)⁻¹) * (ρ (sIncl s))⁻¹ := by
          simp only [map_mul, map_inv] at h4 ⊢
          rw [h4]
        rw [← h5, ← h1]
        group
      calc (ρ (sIncl s * tGen))⁻¹ * φ * ρ (sIncl g)
          = (ρ (sIncl s * tGen))⁻¹ * (φ * ρ (sIncl g)) := by group
        _ = ρ (sIncl g) * ((ρ (sIncl s * tGen))⁻¹ * φ) := by
          rw [h2]
          simp only [map_mul]
          group
    have h3 := hρ.centralizer _ hcomm
    exact ⟨sIncl s * tGen, inv_mul_eq_one.1 h3⟩

theorem GoodRep.excludes [Finite E] (hρ : GoodRep ρ) {Ā : Subgroup (E ≃ₗ[ZMod 2] E)}
    (hn : ∀ a ∈ Ā, ∀ g : GL32, ∃ g' : GL32, a * ρ (sIncl g) * a⁻¹ = ρ (sIncl g'))
    (h0 : Ā ≠ ⊥) (hcomm : ∀ a ∈ Ā, ∀ b ∈ Ā, a * b = b * a) (hsq : ∀ a ∈ Ā, a ^ 2 = 1) :
    Nat.card Ā * Nat.card (fixedSub (MonoidHom.id (E ≃ₗ[ZMod 2] E)) Ā) < Nat.card E := by
  have hinj := hρ.injective
  have hle : Ā ≤ ρ.range := fun a ha => hρ.mem_range_of_normalizes (hn a ha)
  have hBmap : (Ā.comap ρ).map ρ = Ā := Subgroup.map_comap_eq_self hle
  have hBcard : Nat.card (Ā.comap ρ) = Nat.card Ā := by
    conv_rhs => rw [← hBmap]
    exact (Subgroup.card_map_of_injective hinj).symm
  have hfix : fixedSub ρ (Ā.comap ρ) = fixedSub (MonoidHom.id (E ≃ₗ[ZMod 2] E)) Ā := by
    ext x
    simp only [mem_fixedSub]
    constructor
    · intro h a ha
      obtain ⟨b, hb, rfl⟩ : a ∈ (Ā.comap ρ).map ρ := by rw [hBmap]; exact ha
      exact h b hb
    · intro h b hb
      exact h (ρ b) hb
  have hS : ∃ (g : GL32) (x : E), ρ (sIncl g) x ≠ x := by
    by_contra hcon
    push Not at hcon
    have h1 : lowerGL = 1 := by
      apply hρ.faithful
      show ρ (sIncl lowerGL) = ρ (sIncl 1)
      rw [map_one, map_one]
      exact LinearEquiv.ext fun x => hcon lowerGL x
    have h2 := congrArg (fun x : GL32 => (x : Mat3) 1 0) h1
    simp [lowerGL] at h2
  have hB0 : Ā.comap ρ ≠ ⊥ := by
    intro h
    apply h0
    rw [← hBmap, h, Subgroup.map_bot]
  have hBcomm : ∀ a ∈ Ā.comap ρ, ∀ b ∈ Ā.comap ρ, a * b = b * a := by
    intro a ha b hb
    apply hinj
    rw [map_mul, map_mul]
    exact hcomm _ ha _ hb
  have hBsq : ∀ a ∈ Ā.comap ρ, a ^ 2 = 1 := by
    intro a ha
    apply hinj
    rw [map_pow, map_one]
    exact hsq _ ha
  have := GL3_ext_excludes_FF ρ hS (Ā.comap ρ) hB0 hBcomm hBsq
  rwa [hBcard, hfix] at this

end GoodRep

theorem goodRep_repQ : GoodRep repQ where
  faithful := by
    rw [repQ_comp_sIncl]
    exact repA_injective
  centralizer φ h := endS_traceZero φ fun g X => by
    have h1 := congrArg (fun m : traceZero ≃ₗ[ZMod 2] traceZero => m X) (h g)
    simpa [repQ_sIncl] using h1

theorem goodRep_repP : GoodRep repP where
  faithful := by
    rw [repP_comp_sIncl]
    exact repPS_injective
  centralizer φ h := centralizer_repPS φ fun g x => by
    have h1 := congrArg (fun m : P6 ≃ₗ[ZMod 2] P6 => m x) (h g)
    simpa [repP_sIncl] using h1

end CFSG.QuasithinUnique.Setup.Family
