module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.LinearGroups

open scoped IsMulCommutative

variable {F : Type*} [Field F]

section Coordinates

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem range_le_ker_of_mul_self_eq_zero {N : Module.End F V} (hN : N * N = 0) :
    LinearMap.range N ≤ LinearMap.ker N := by
  rintro _ ⟨v, rfl⟩
  rw [LinearMap.mem_ker, ← Module.End.mul_apply, hN, LinearMap.zero_apply]

@[expose] def quadCoord (N M : Module.End F V) :
    (LinearMap.ker M × LinearMap.ker M) →ₗ[F] V :=
  (N ∘ₗ (LinearMap.ker M).subtype).coprod (LinearMap.ker M).subtype

theorem quadCoord_apply (N M : Module.End F V) (w₁ w₂ : LinearMap.ker M) :
    quadCoord N M (w₁, w₂) = N w₁ + w₂ := by
  simp [quadCoord]

variable [FiniteDimensional F V] {N M : Module.End F V}

theorem quadCoord_bijective (hN : N * N = 0) (hM : M * M = 0)
    (hUW : LinearMap.ker N ⊓ LinearMap.ker M = ⊥) :
    Function.Bijective (quadCoord N M) ∧
      Module.finrank F V = 2 * Module.finrank F (LinearMap.ker M) ∧
      Module.finrank F (LinearMap.ker N) = Module.finrank F (LinearMap.ker M) := by
  have hdimN : Module.finrank F V ≤ 2 * Module.finrank F (LinearMap.ker N) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker N
    have h2 := Submodule.finrank_mono (range_le_ker_of_mul_self_eq_zero hN)
    omega
  have hdimM : Module.finrank F V ≤ 2 * Module.finrank F (LinearMap.ker M) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker M
    have h2 := Submodule.finrank_mono (range_le_ker_of_mul_self_eq_zero hM)
    omega
  have hsum : Module.finrank F (LinearMap.ker N) + Module.finrank F (LinearMap.ker M) ≤
      Module.finrank F V := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker N) (LinearMap.ker M)
    rw [hUW, finrank_bot] at h1
    have h2 := Submodule.finrank_le (LinearMap.ker N ⊔ LinearMap.ker M)
    omega
  have hinj : Function.Injective (quadCoord N M) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨w₁, w₂⟩ h0
    rw [quadCoord_apply] at h0
    have hNw : N w₁ = -(w₂ : V) := eq_neg_of_add_eq_zero_left h0
    have hmemN : N w₁ ∈ LinearMap.ker N := range_le_ker_of_mul_self_eq_zero hN ⟨_, rfl⟩
    have hmemM : N w₁ ∈ LinearMap.ker M := by
      rw [hNw]
      exact (LinearMap.ker M).neg_mem w₂.2
    have hNw0 : N w₁ = 0 := by
      have : N w₁ ∈ LinearMap.ker N ⊓ LinearMap.ker M := ⟨hmemN, hmemM⟩
      rwa [hUW, Submodule.mem_bot] at this
    have hw₂ : (w₂ : V) = 0 := by rw [← neg_eq_zero, ← hNw, hNw0]
    have hw₁ : (w₁ : V) = 0 := by
      have : (w₁ : V) ∈ LinearMap.ker N ⊓ LinearMap.ker M := ⟨hNw0, w₁.2⟩
      rwa [hUW, Submodule.mem_bot] at this
    exact Prod.ext (Subtype.ext hw₁) (Subtype.ext hw₂)
  have hdim : Module.finrank F V = 2 * Module.finrank F (LinearMap.ker M) := by omega
  refine ⟨⟨hinj, ?_⟩, hdim, by omega⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  rw [Module.finrank_prod, hdim]
  ring

end Coordinates

section Operator

variable {V : Type*} [AddCommGroup V] [Module F V] {N M : Module.End F V}

@[expose] def quadOp (N M : Module.End F V) (hM : M * M = 0) : Module.End F (LinearMap.ker M) :=
  (M * N).restrict fun w _ =>
    range_le_ker_of_mul_self_eq_zero hM (LinearMap.mem_range.mpr ⟨N w, rfl⟩)

theorem coe_quadOp_apply (hM : M * M = 0) (w : LinearMap.ker M) :
    (quadOp N M hM w : V) = M (N w) :=
  rfl

theorem quadCoord_N (hN : N * N = 0) (w₁ w₂ : LinearMap.ker M) :
    N (quadCoord N M (w₁, w₂)) = quadCoord N M (w₂, 0) := by
  rw [quadCoord_apply, quadCoord_apply, map_add, ← Module.End.mul_apply, hN]
  simp

theorem quadCoord_M (hM : M * M = 0) (w₁ w₂ : LinearMap.ker M) :
    M (quadCoord N M (w₁, w₂)) = quadCoord N M (0, quadOp N M hM w₁) := by
  rw [quadCoord_apply, quadCoord_apply, map_add, LinearMap.mem_ker.mp w₂.2, coe_quadOp_apply]
  simp

variable [FiniteDimensional F V]

theorem quadOp_irreducible (hN : N * N = 0) (hM : M * M = 0)
    (hUW : LinearMap.ker N ⊓ LinearMap.ker M = ⊥)
    (hirr : ∀ P : Submodule F V, (∀ v ∈ P, N v ∈ P) → (∀ v ∈ P, M v ∈ P) → P = ⊥ ∨ P = ⊤)
    (L : Submodule F (LinearMap.ker M)) (hL : ∀ w ∈ L, quadOp N M hM w ∈ L) :
    L = ⊥ ∨ L = ⊤ := by
  obtain ⟨hbij, -, -⟩ := quadCoord_bijective hN hM hUW
  have hPN : ∀ v ∈ (L.prod L).map (quadCoord N M), N v ∈ (L.prod L).map (quadCoord N M) := by
    rintro _ ⟨⟨l₁, l₂⟩, ⟨-, h₂⟩, rfl⟩
    exact ⟨(l₂, 0), ⟨h₂, L.zero_mem⟩, (quadCoord_N hN l₁ l₂).symm⟩
  have hPM : ∀ v ∈ (L.prod L).map (quadCoord N M), M v ∈ (L.prod L).map (quadCoord N M) := by
    rintro _ ⟨⟨l₁, l₂⟩, ⟨h₁, -⟩, rfl⟩
    exact ⟨(0, quadOp N M hM l₁), ⟨L.zero_mem, hL l₁ h₁⟩, (quadCoord_M hM l₁ l₂).symm⟩
  rcases hirr _ hPN hPM with hbot | htop
  · left
    rw [eq_bot_iff]
    intro l hl
    have hmem : quadCoord N M (0, l) ∈ (L.prod L).map (quadCoord N M) :=
      ⟨(0, l), ⟨L.zero_mem, hl⟩, rfl⟩
    rw [hbot, Submodule.mem_bot, ← (quadCoord N M).map_zero] at hmem
    rw [Submodule.mem_bot]
    exact congrArg Prod.snd (hbij.1 hmem)
  · right
    rw [eq_top_iff]
    intro w _
    have hmem : quadCoord N M (0, w) ∈ (L.prod L).map (quadCoord N M) := by
      rw [htop]
      trivial
    obtain ⟨⟨l₁, l₂⟩, ⟨-, h₂⟩, heq⟩ := hmem
    have := congrArg Prod.snd (hbij.1 heq)
    simp only at this
    rw [← this]
    exact h₂

omit [FiniteDimensional F V] in
theorem quadOp_injective (hN : N * N = 0) (hM : M * M = 0)
    (hUW : LinearMap.ker N ⊓ LinearMap.ker M = ⊥) : Function.Injective (quadOp N M hM) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have h1 : M (N w) = 0 := by rw [← coe_quadOp_apply hM, hw]; rfl
  have hNw : N w = 0 := by
    have : N w ∈ LinearMap.ker N ⊓ LinearMap.ker M :=
      ⟨range_le_ker_of_mul_self_eq_zero hN ⟨_, rfl⟩, h1⟩
    rwa [hUW, Submodule.mem_bot] at this
  have : (w : V) ∈ LinearMap.ker N ⊓ LinearMap.ker M := ⟨hNw, w.2⟩
  rw [hUW, Submodule.mem_bot] at this
  exact Subtype.ext this

theorem ker_eq_bot_of_mem_adjoin_quadOp (hN : N * N = 0) (hM : M * M = 0)
    (hUW : LinearMap.ker N ⊓ LinearMap.ker M = ⊥)
    (hirr : ∀ P : Submodule F V, (∀ v ∈ P, N v ∈ P) → (∀ v ∈ P, M v ∈ P) → P = ⊥ ∨ P = ⊤)
    {s : Module.End F (LinearMap.ker M)} (hs : s ∈ Algebra.adjoin F {quadOp N M hM})
    (hs0 : s ≠ 0) : LinearMap.ker s = ⊥ := by
  have hcomm : Commute (quadOp N M hM) s :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hs (by simp)
  rcases quadOp_irreducible hN hM hUW hirr (LinearMap.ker s) (fun w hw => by
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply,
      LinearMap.mem_ker.mp hw, map_zero]) with h | h
  · exact h
  · exfalso
    apply hs0
    ext w
    have : w ∈ LinearMap.ker s := by rw [h]; trivial
    simpa using LinearMap.mem_ker.mp this

end Operator

section SpecialLinear

open Matrix

variable {V : Type*} [AddCommGroup V] [Module F V]

@[expose] def slUpper (K : Type*) [CommRing K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def slLower {K : Type*} [CommRing K] (lam : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; lam, 1], by simp [Matrix.det_fin_two_of]⟩

theorem slUpper_mulVec {K : Type*} [CommRing K] (u v : K) :
    ((slUpper K : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![u, v] =
      ![u + v, v] := by
  ext i
  fin_cases i <;> simp [slUpper, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem slLower_mulVec {K : Type*} [CommRing K] (lam u v : K) :
    ((slLower lam : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ ![u, v] =
      ![u, v + lam * u] := by
  ext i
  fin_cases i <;> simp [slLower, Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_comm]

variable (F) in
@[expose] noncomputable def slToGL (K : Type*) [CommRing K] [Algebra F K] :
    Matrix.SpecialLinearGroup (Fin 2) K →* LinearMap.GeneralLinearGroup F (Fin 2 → K) where
  toFun A :=
    { val := (Matrix.mulVecLin (A : Matrix (Fin 2) (Fin 2) K)).restrictScalars F
      inv := (Matrix.mulVecLin ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)).restrictScalars F
      val_inv := LinearMap.ext fun w => by
        rw [Module.End.mul_apply, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply,
          Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
          Matrix.one_mulVec, Module.End.one_apply]
      inv_val := LinearMap.ext fun w => by
        rw [Module.End.mul_apply, LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply,
          Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
          Matrix.one_mulVec, Module.End.one_apply] }
  map_one' := Units.ext (LinearMap.ext fun w => by
    rw [Units.val_one, Module.End.one_apply]
    change (((1 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) = w
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec])
  map_mul' A B := Units.ext (LinearMap.ext fun w => by
    rw [Units.val_mul, Module.End.mul_apply]
    change (((A * B : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) =
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ ((B : Matrix (Fin 2) (Fin 2) K) *ᵥ w)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec])

theorem slToGL_apply (K : Type*) [CommRing K] [Algebra F K]
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (w : Fin 2 → K) :
    ((slToGL F K A : LinearMap.GeneralLinearGroup F (Fin 2 → K)) : (Fin 2 → K) →ₗ[F] Fin 2 → K) w =
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w :=
  rfl

theorem slToGL_injective (K : Type*) [CommRing K] [Algebra F K] :
    Function.Injective (slToGL F K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup F (Fin 2 → K) =>
    ((g : (Fin 2 → K) →ₗ[F] Fin 2 → K) (Pi.single j 1)) i) hA
  simp only [slToGL_apply, Units.val_one, Module.End.one_apply, Matrix.mulVec_single_one] at h1
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h1

theorem exists_closure_mulEquiv_of_conj {K : Type*} [CommRing K] [Algebra F K]
    (h : V ≃ₗ[F] (Fin 2 → K)) (X Y : LinearMap.GeneralLinearGroup F V)
    (A B : Matrix.SpecialLinearGroup (Fin 2) K)
    (hXA : ∀ w, h ((X : V →ₗ[F] V) (h.symm w)) = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w)
    (hYB : ∀ w, h ((Y : V →ₗ[F] V) (h.symm w)) = (B : Matrix (Fin 2) (Fin 2) K) *ᵥ w) :
    ∃ ψ : Subgroup.closure ({X, Y} : Set (LinearMap.GeneralLinearGroup F V)) ≃*
        Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) K)),
      ∀ (g : Subgroup.closure ({X, Y} : Set (LinearMap.GeneralLinearGroup F V))) (w : Fin 2 → K),
        h (((g : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) (h.symm w)) =
          (((ψ g : Matrix.SpecialLinearGroup (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ w := by
  let κ : LinearMap.GeneralLinearGroup F V →* LinearMap.GeneralLinearGroup F (Fin 2 → K) :=
    Units.map (LinearEquiv.conjRingEquiv h).toMonoidHom
  have hκ : ∀ g w, ((κ g : LinearMap.GeneralLinearGroup F (Fin 2 → K)) :
      (Fin 2 → K) →ₗ[F] Fin 2 → K) w = h ((g : V →ₗ[F] V) (h.symm w)) := fun g w => rfl
  have hκinj : Function.Injective κ :=
    Units.map_injective (LinearEquiv.conjRingEquiv h).injective
  have hκX : κ X = slToGL F K A := Units.ext (LinearMap.ext fun w => by
    rw [hκ, hXA, slToGL_apply])
  have hκY : κ Y = slToGL F K B := Units.ext (LinearMap.ext fun w => by
    rw [hκ, hYB, slToGL_apply])
  have heq : (Subgroup.closure ({X, Y} : Set (LinearMap.GeneralLinearGroup F V))).map κ =
      (Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) K))).map
        (slToGL F K) := by
    rw [MonoidHom.map_closure, MonoidHom.map_closure, Set.image_pair, Set.image_pair, hκX, hκY]
  let e₁ := Subgroup.equivMapOfInjective
    (Subgroup.closure ({X, Y} : Set (LinearMap.GeneralLinearGroup F V))) κ hκinj
  let e₂ := Subgroup.equivMapOfInjective
    (Subgroup.closure ({A, B} : Set (Matrix.SpecialLinearGroup (Fin 2) K))) _
    (slToGL_injective (F := F) K)
  refine ⟨e₁.trans ((MulEquiv.subgroupCongr heq).trans e₂.symm), fun g w => ?_⟩
  have hcomp : slToGL F K (((e₁.trans ((MulEquiv.subgroupCongr heq).trans e₂.symm)) g :
      Matrix.SpecialLinearGroup (Fin 2) K)) = κ g := by
    have h1 := Subgroup.coe_equivMapOfInjective_apply _ (slToGL F K) (slToGL_injective (F := F) K)
      ((e₁.trans ((MulEquiv.subgroupCongr heq).trans e₂.symm)) g)
    rw [← h1]
    simp [e₁, e₂, MulEquiv.trans_apply, Subgroup.coe_equivMapOfInjective_apply]
  rw [← hκ, ← hcomp, slToGL_apply]

end SpecialLinear

section Main

universe v

open Matrix

theorem irreducible_two_quadratic_generators_field_embedding {V : Type v} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Nontrivial V]
    (X Y : LinearMap.GeneralLinearGroup F V) (hX1 : X ≠ 1) (_hY1 : Y ≠ 1)
    (hX : ((X : V →ₗ[F] V) - 1) ^ 2 = 0) (hY : ((Y : V →ₗ[F] V) - 1) ^ 2 = 0)
    (hirr : ∀ W : Submodule F V, (∀ w ∈ W, (X : V →ₗ[F] V) w ∈ W) →
      (∀ w ∈ W, (Y : V →ₗ[F] V) w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ (K : Type v) (_ : Field K) (_ : Algebra F K) (lam : K) (h : V ≃ₗ[F] (Fin 2 → K)),
      FiniteDimensional F K ∧ 1 ≤ Module.finrank F K ∧ lam ≠ 0 ∧ Algebra.adjoin F {lam} = ⊤ ∧
      Module.finrank F V = 2 * Module.finrank F K ∧
      (∀ u v : K, h ((X : V →ₗ[F] V) (h.symm ![u, v])) = ![u + v, v]) ∧
      (∀ u v : K, h ((Y : V →ₗ[F] V) (h.symm ![u, v])) = ![u, v + lam * u]) ∧
      (∃ ψ : Subgroup.closure ({X, Y} : Set (LinearMap.GeneralLinearGroup F V)) ≃*
          Subgroup.closure ({slUpper K, slLower lam} : Set (SpecialLinearGroup (Fin 2) K)),
        ∀ (g : Subgroup.closure ({X, Y} : Set (LinearMap.GeneralLinearGroup F V)))
          (w : Fin 2 → K), h (((g : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) (h.symm w)) =
            ((ψ g : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) ∧
      (Finite F → Finite K) := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N : Module.End F V, N = (X : V →ₗ[F] V) - 1 := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : Module.End F V, M = (Y : V →ₗ[F] V) - 1 := ⟨_, rfl⟩
  have hN : N * N = 0 := by rw [hNdef, ← sq]; exact hX
  have hM : M * M = 0 := by rw [hMdef, ← sq]; exact hY
  have hXN : ∀ v, (X : V →ₗ[F] V) v = v + N v := fun v => by
    rw [hNdef, LinearMap.sub_apply, Module.End.one_apply]
    abel
  have hYM : ∀ v, (Y : V →ₗ[F] V) v = v + M v := fun v => by
    rw [hMdef, LinearMap.sub_apply, Module.End.one_apply]
    abel
  have hN0 : N ≠ 0 := by
    intro h0
    apply hX1
    apply Units.ext
    rw [hNdef, sub_eq_zero] at h0
    rw [h0, Units.val_one]
  have hirr' : ∀ P : Submodule F V, (∀ v ∈ P, N v ∈ P) → (∀ v ∈ P, M v ∈ P) →
      P = ⊥ ∨ P = ⊤ := fun P hPN hPM =>
    hirr P (fun v hv => by rw [hXN]; exact P.add_mem hv (hPN v hv))
      (fun v hv => by rw [hYM]; exact P.add_mem hv (hPM v hv))
  have hUW : LinearMap.ker N ⊓ LinearMap.ker M = ⊥ := by
    rcases hirr' (LinearMap.ker N ⊓ LinearMap.ker M)
      (fun v hv => by rw [LinearMap.mem_ker.mp hv.1]; exact Submodule.zero_mem _)
      (fun v hv => by rw [LinearMap.mem_ker.mp hv.2]; exact Submodule.zero_mem _) with h | h
    · exact h
    · exfalso
      apply hN0
      ext v
      have : v ∈ LinearMap.ker N ⊓ LinearMap.ker M := by rw [h]; trivial
      exact this.1
  obtain ⟨hbij, hdim, -⟩ := quadCoord_bijective hN hM hUW
  have hWpos : 0 < Module.finrank F (LinearMap.ker M) := by
    have := Module.finrank_pos (R := F) (M := V)
    omega
  have : Nontrivial (LinearMap.ker M) := Module.nontrivial_of_finrank_pos hWpos
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : LinearMap.ker M)
  obtain ⟨R, hR⟩ : ∃ R, R = quadOp N M hM := ⟨_, rfl⟩
  have hker : ∀ s ∈ Algebra.adjoin F {R}, s ≠ 0 → LinearMap.ker s = ⊥ := fun s hs hs0 =>
    ker_eq_bot_of_mem_adjoin_quadOp hN hM hUW hirr' (hR ▸ hs) hs0
  have hRirr : ∀ L : Submodule F (LinearMap.ker M), (∀ w ∈ L, R w ∈ L) → L = ⊥ ∨ L = ⊤ :=
    fun L hL => quadOp_irreducible hN hM hUW hirr' L (hR ▸ hL)
  have hRinj : Function.Injective R := hR ▸ quadOp_injective hN hM hUW
  have : NoZeroDivisors (Algebra.adjoin F {R}) := ⟨fun {a b} hab => by
    by_contra hne
    push Not at hne
    have ha := hker a a.2 (fun h0 => hne.1 (Subtype.ext h0))
    apply hne.2
    apply Subtype.ext
    refine LinearMap.ext fun w => ?_
    have h1 : (a : Module.End F (LinearMap.ker M)) ((b : Module.End F (LinearMap.ker M)) w) =
        0 := by
      have := congrArg (fun x : Algebra.adjoin F {R} => (x : Module.End F (LinearMap.ker M)) w) hab
      simpa using this
    simpa using LinearMap.ker_eq_bot'.mp ha _ h1⟩
  have : IsDomain (Algebra.adjoin F {R}) := NoZeroDivisors.to_isDomain (Algebra.adjoin F {R})
  have : FiniteDimensional F (Algebra.adjoin F {R}) :=
    Module.Finite.of_injective (Algebra.adjoin F {R}).val.toLinearMap Subtype.val_injective
  let _ : Field (Algebra.adjoin F {R}) := fieldOfFiniteDimensional F _
  let lam : Algebra.adjoin F {R} := ⟨R, Algebra.self_mem_adjoin_singleton F R⟩
  let ev : Algebra.adjoin F {R} →ₗ[F] LinearMap.ker M :=
    { toFun := fun s => (s : Module.End F (LinearMap.ker M)) w₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ s, ev s = (s : Module.End F (LinearMap.ker M)) w₀ := fun _ => rfl
  have hevlam : ∀ s, ev (lam * s) = R (ev s) := fun _ => rfl
  have hevinj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    by_contra hs0
    exact hw₀ (LinearMap.ker_eq_bot'.mp (hker s s.2 fun h0 => hs0 (Subtype.ext h0)) w₀ hs)
  have hevsurj : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top]
    have hinv : ∀ w ∈ LinearMap.range ev, R w ∈ LinearMap.range ev := by
      rintro _ ⟨s, rfl⟩
      exact ⟨lam * s, hevlam s⟩
    rcases hRirr _ hinv with hbot | htop
    · exfalso
      have : w₀ ∈ LinearMap.range ev := ⟨1, rfl⟩
      rw [hbot, Submodule.mem_bot] at this
      exact hw₀ this
    · exact htop
  let evE : Algebra.adjoin F {R} ≃ₗ[F] LinearMap.ker M :=
    LinearEquiv.ofBijective ev ⟨hevinj, hevsurj⟩
  have hfin : Module.finrank F (Algebra.adjoin F {R}) = Module.finrank F (LinearMap.ker M) :=
    evE.finrank_eq
  let Φe : (LinearMap.ker M × LinearMap.ker M) ≃ₗ[F] V := LinearEquiv.ofBijective _ hbij
  let h : V ≃ₗ[F] (Fin 2 → Algebra.adjoin F {R}) :=
    Φe.symm.trans ((evE.symm.prodCongr evE.symm).trans
      (LinearEquiv.finTwoArrow F (Algebra.adjoin F {R})).symm)
  have hsymm : ∀ u v, h.symm ![u, v] = quadCoord N M (ev u, ev v) := fun u v => rfl
  have happly : ∀ u v, h (quadCoord N M (ev u, ev v)) = ![u, v] := fun u v => by
    rw [← hsymm]
    exact h.apply_symm_apply _
  have hXf : ∀ u v, h ((X : V →ₗ[F] V) (h.symm ![u, v])) = ![u + v, v] := fun u v => by
    rw [hsymm, hXN, quadCoord_N hN, ← map_add, Prod.mk_add_mk, add_zero, ← map_add, happly]
  have hYf : ∀ u v, h ((Y : V →ₗ[F] V) (h.symm ![u, v])) = ![u, v + lam * u] := fun u v => by
    rw [hsymm, hYM, quadCoord_M hM, ← hR, ← map_add, Prod.mk_add_mk, add_zero, ← hevlam,
      ← map_add, happly]
  have hvec : ∀ w : Fin 2 → Algebra.adjoin F {R}, w = ![w 0, w 1] := fun w => by
    ext i
    fin_cases i <;> rfl
  obtain ⟨ψ, hψ⟩ := exists_closure_mulEquiv_of_conj h X Y (slUpper _) (slLower lam)
    (fun w => by rw [hvec w, hXf, slUpper_mulVec]) (fun w => by rw [hvec w, hYf, slLower_mulVec])
  have hlam0 : lam ≠ 0 := by
    intro h0
    have : R w₀ = 0 := by
      have := congrArg (fun x : Algebra.adjoin F {R} => (x : Module.End F (LinearMap.ker M)) w₀) h0
      simpa [lam] using this
    exact hw₀ (hRinj (this.trans (map_zero R).symm))
  have hadj : Algebra.adjoin F {lam} = ⊤ := by
    apply Subalgebra.map_injective (f := (Algebra.adjoin F {R}).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, Subalgebra.range_val]
    rfl
  refine ⟨Algebra.adjoin F {R}, inferInstance, inferInstance, lam, h, inferInstance, ?_, hlam0,
    hadj, by rw [hfin]; exact hdim, hXf, hYf, ⟨ψ, hψ⟩, fun _ => Module.finite_of_finite F⟩
  rw [hfin]
  exact hWpos

end Main

end CFSG.LinearGroups
