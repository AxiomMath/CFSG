module

public import CFSG.LinearAlgebra.FrobeniusIsometryNormalizer
public import Mathlib.RingTheory.Trace.Basic

public section

namespace CFSG.LinearAlgebra

open Module

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

namespace FrobeniusIsometryInverse

theorem exists_field_model [Finite K] [FiniteDimensional K V] {E : Subgroup (V ≃ₗ[K] V)}
    [Finite E] (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
    {W : Submodule K V} (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W)
    (hmin : ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W)
    (hW0 : W ≠ ⊥) :
    ∃ (F : Type (max u v)) (_ : Field F) (_ : Finite F) (_ : Algebra K F)
      (_ : FiniteDimensional K F) (eK : W ≃ₗ[K] F) (χ : E →* Fˣ) (t : F),
      (∀ (x : E) (w : W), eK ⟨(x : V ≃ₗ[K] V) (w : V), hWE (x : V ≃ₗ[K] V) x.2 w w.2⟩ =
        (χ x : F) * eK w) ∧ (∃ x₀ : E, (χ x₀ : F) = t) ∧
      Algebra.adjoin K ({t} : Set F) = ⊤ := by
  classical
  let : CommGroup E :=
    { (inferInstance : Group E) with
      mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  let ρ : E →* (W →ₗ[K] W) :=
    { toFun := fun x => LinearMap.codRestrict W
        (((x : V ≃ₗ[K] V) : V →ₗ[K] V) ∘ₗ W.subtype)
        (fun w => hWE x x.2 w.1 w.2)
      map_one' := by
        ext w
        rfl
      map_mul' := by
        intro x y
        ext w
        rfl }
  have hρ : ∀ (x : E) (w : W), ((ρ x w : W) : V) = (x : V ≃ₗ[K] V) (w : V) :=
    fun x w => rfl
  let L : MonoidAlgebra K E →ₐ[K] (W →ₗ[K] W) := MonoidAlgebra.lift K (W →ₗ[K] W) E ρ
  let : Module (MonoidAlgebra K E) W := Module.compHom W L.toRingHom
  have hsmul : ∀ (b : MonoidAlgebra K E) (w : W), b • w = L b w := fun _ _ => rfl
  have : IsScalarTower K (MonoidAlgebra K E) W :=
    ⟨fun c b w => by rw [hsmul, hsmul, map_smul]; rfl⟩
  have hof : ∀ (x : E) (w : W), MonoidAlgebra.of K E x • w = ρ x w := fun x w => by
    rw [hsmul, MonoidAlgebra.lift_of]
  have : IsSimpleModule (MonoidAlgebra K E) W :=
    isSimpleModule_restrict hmin hW0 ρ hρ hof
  obtain ⟨I, hI, ⟨e⟩⟩ :=
    isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule (MonoidAlgebra K E) W›
  let F := MonoidAlgebra K E ⧸ I
  let : Field F := Ideal.Quotient.field I
  have : FiniteDimensional K W := Module.Finite.of_injective W.subtype Subtype.val_injective
  let eK : W ≃ₗ[K] F := e.restrictScalars K
  have : FiniteDimensional K F := eK.finiteDimensional
  have : Finite F := Module.finite_of_finite K
  let ψ : MonoidAlgebra K E →ₐ[K] F := Ideal.Quotient.mkₐ K I
  have hψ : Function.Surjective ψ := Ideal.Quotient.mkₐ_surjective K I
  have hψmk : ∀ a : MonoidAlgebra K E, ψ a = Ideal.Quotient.mk I a := by
    intro a
    rw [show ψ a = Ideal.Quotient.mkₐ K I a from rfl, Ideal.Quotient.mkₐ_eq_mk]
  have hunit : ∀ x : E, IsUnit (ψ (MonoidAlgebra.of K E x)) := by
    intro x
    refine IsUnit.of_mul_eq_one (ψ (MonoidAlgebra.of K E x⁻¹)) ?_
    have h1 : MonoidAlgebra.of K E x * MonoidAlgebra.of K E x⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [← map_mul, h1, map_one]
  let χ : E →* Fˣ :=
    MonoidHom.mk' (fun x => Units.mk0 (ψ (MonoidAlgebra.of K E x)) (hunit x).ne_zero)
      (fun x y => by
        ext
        change ψ (MonoidAlgebra.of K E (x * y)) =
          ψ (MonoidAlgebra.of K E x) * ψ (MonoidAlgebra.of K E y)
        rw [map_mul, map_mul])
  have hχ : ∀ x : E, (χ x : F) = ψ (MonoidAlgebra.of K E x) := fun x => rfl
  have hmk : ∀ (a : MonoidAlgebra K E) (y : F),
      a • y = Ideal.Quotient.mk I a * y := by
    intro a y
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  have he_act : ∀ (x : E) (w : W), e (ρ x w) = (χ x : F) * e w := by
    intro x w
    rw [← hof x w, e.map_smul, hmk, hχ x, hψmk]
  obtain ⟨t, x₀, hx₀, -, -, hgen⟩ := exists_adjoin_eq_top_of_surjective ψ hψ χ hχ hodd
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, eK, χ, t,
    fun x w => he_act x w, ⟨x₀, by rw [hx₀]⟩, hgen⟩

theorem field_form_props (B : LinearMap.BilinForm K V) (hsymm : ∀ v w, B v w = B w v)
    {E : Subgroup (V ≃ₗ[K] V)} (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w)
    {W : Submodule K V} (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W) (hWnd : (B.restrict W).Nondegenerate)
    {F : Type*} [Field F] [Algebra K F] (eK : W ≃ₗ[K] F) (χ : E →* Fˣ)
    (hact : ∀ (x : E) (w : W), eK ⟨(x : V ≃ₗ[K] V) (w : V), hWE (x : V ≃ₗ[K] V) x.2 w w.2⟩ =
      (χ x : F) * eK w) :
    let b : F →ₗ[K] F →ₗ[K] K := B.compl₁₂ (W.subtype ∘ₗ (eK.symm : F →ₗ[K] W))
      (W.subtype ∘ₗ (eK.symm : F →ₗ[K] W))
    (∀ a a', b a a' = b a' a) ∧ (∀ a, (∀ a', b a a' = 0) → a = 0) ∧
      ∀ x : E, ∀ a a', b ((χ x : F) * a) ((χ x : F) * a') = b a a' := by
  intro b
  let i : F →ₗ[K] V := W.subtype ∘ₗ (eK.symm : F →ₗ[K] W)
  have hb : ∀ a a', b a a' = B (i a) (i a') := fun a a' => LinearMap.compl₁₂_apply B i i a a'
  have hi : ∀ w : W, i (eK w) = (w : V) := fun w => by
    change W.subtype (eK.symm (eK w)) = (w : V)
    rw [LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨fun a a' => by rw [hb, hb, hsymm], fun a ha => ?_, fun x a a' => ?_⟩
  · have hzeroW : eK.symm a = 0 := by
      apply hWnd.1
      intro w
      have h := ha (eK w)
      rw [hb, hi] at h
      exact h
    have := congrArg (fun w : W => eK w) hzeroW
    simpa using this
  · have hshift : ∀ c : F, i ((χ x : F) * c) = (x : V ≃ₗ[K] V) (i c) := by
      intro c
      have h1W : eK.symm ((χ x : F) * c) =
          ⟨(x : V ≃ₗ[K] V) ((eK.symm c : W) : V),
            hWE (x : V ≃ₗ[K] V) x.2 ((eK.symm c : W) : V) (eK.symm c).2⟩ := by
        refine eK.injective ?_
        rw [LinearEquiv.apply_symm_apply, hact x (eK.symm c), LinearEquiv.apply_symm_apply]
      change W.subtype (eK.symm ((χ x : F) * c)) = (x : V ≃ₗ[K] V) (i c)
      rw [h1W]
      rfl
    rw [hb, hb, hshift, hshift]
    exact hiso x x.2 (i a) (i a')

theorem exists_isometry_inv_of_minimal [Finite K] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hsymm : ∀ v w, B v w = B w v) {E : Subgroup (V ≃ₗ[K] V)}
    [Finite E] (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
    (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) (W : Submodule K V)
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W)
    (hmin : ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W)
    (hW0 : W ≠ ⊥) (hWnd : (B.restrict W).Nondegenerate) :
    ∃ g : V →ₗ[K] V, (∀ v ∈ W, g v ∈ W) ∧ (∀ v ∈ B.orthogonal W, g v = v) ∧
      (∀ v ∈ W, ∀ w ∈ W, B (g v) (g w) = B v w) ∧ ∀ x ∈ E, ∀ v ∈ W, g (x v) = x⁻¹ (g v) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨F, _, _, _, _, eK, χ, t, hact, ⟨x₀, hx₀⟩, hgen⟩ :=
    exists_field_model hcomm hodd hWE hmin hW0
  obtain ⟨hb_symm, hb_nd, hb_iso⟩ := field_form_props B hsymm hiso hWE hWnd eK χ hact
  let i : F →ₗ[K] V := W.subtype ∘ₗ (eK.symm : F →ₗ[K] W)
  let b : F →ₗ[K] F →ₗ[K] K := B.compl₁₂ i i
  have hb : ∀ a a', b a a' = B (i a) (i a') := fun a a' => LinearMap.compl₁₂_apply B i i a a'
  have hi : ∀ w : W, i (eK w) = (w : V) := fun w => by
    change W.subtype (eK.symm (eK w)) = (w : V)
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have ht0 : t ≠ 0 := by
    rw [← hx₀]
    exact (χ x₀).ne_zero
  have hbt : ∀ a a', b (t * a) (t * a') = b a a' := by
    rw [← hx₀]
    exact hb_iso x₀
  obtain ⟨τ, -, hτiso, hτinv⟩ := exists_algHom_inv_isometry b hb_symm hb_nd ht0 hgen hbt
  have hτχ : ∀ x : E, τ (χ x : F) = (χ x : F)⁻¹ := fun x => hτinv _ (χ x).ne_zero (hb_iso x)
  let gW : W →ₗ[K] W := (eK.symm : F →ₗ[K] W) ∘ₗ τ.toLinearMap ∘ₗ (eK : W →ₗ[K] F)
  have heK_gW : ∀ w : W, eK (gW w) = τ (eK w) := fun w => by
    change eK (eK.symm (τ (eK w))) = τ (eK w)
    rw [LinearEquiv.apply_symm_apply]
  have hgW : ∀ w : W, ((gW w : W) : V) = i (τ (eK w)) := fun w => rfl
  have hgWiso : ∀ v w : W, B (gW v) (gW w) = B (v : V) (w : V) := by
    intro v w
    have h := hτiso (eK v) (eK w)
    rw [hb, hb, hi, hi] at h
    rw [hgW, hgW]
    exact h
  have hgWsem : ∀ (x : V ≃ₗ[K] V) (hx : x ∈ E) (w : W),
      ((gW ⟨x (w : V), hWE x hx w w.2⟩ : W) : V) = x⁻¹ ((gW w : W) : V) := by
    intro x hx w
    let y : E := ⟨x, hx⟩
    have hL : eK (gW ⟨x (w : V), hWE x hx w w.2⟩) = (χ y : F)⁻¹ * τ (eK w) := by
      rw [heK_gW, hact y w, map_mul, hτχ]
    have hR : eK ⟨x⁻¹ ((gW w : W) : V), hWE x⁻¹ (inv_mem hx) _ (gW w).2⟩ =
        (χ y : F)⁻¹ * τ (eK w) := by
      have h1 := hact y⁻¹ (gW w)
      rw [heK_gW, map_inv, Units.val_inv_eq_inv_val] at h1
      exact h1
    exact congrArg Subtype.val (eK.injective (hL.trans hR.symm))
  have hcompl : IsCompl W (B.orthogonal W) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (B := B) (W := W) (fun x y h => by rwa [hsymm y x]) hWnd
  obtain ⟨g, hgform, hgorth, hgiso⟩ := exists_isometry_extend B hcompl gW hgWiso
  refine ⟨g, fun v hv => ?_, hgorth, fun v hv w hw => ?_, fun x hx v hv => ?_⟩
  · rw [hgform ⟨v, hv⟩]
    exact (gW ⟨v, hv⟩).2
  · rw [hgform ⟨v, hv⟩, hgform ⟨w, hw⟩]
    exact hgWiso ⟨v, hv⟩ ⟨w, hw⟩
  · rw [hgform ⟨x v, hWE x hx v hv⟩, hgform ⟨v, hv⟩]
    exact hgWsem x hx ⟨v, hv⟩

open FrobeniusIsometryPair in
theorem exists_isometry_inv_of_pair [Finite K] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hsymm : ∀ v w, B v w = B w v) {E : Subgroup (V ≃ₗ[K] V)}
    [Finite E] (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
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
        ∀ x ∈ E, ∀ v ∈ W ⊔ W', g (x v) = x⁻¹ (g v) := by
  classical
  have hkerL := ker_left_eq_bot B hsymm hiso W W' hWE hW'E hminW hpair
  have hkerR := ker_right_eq_bot B hiso W W' hWE hW'E hminW' hpair
  have hWW' := inf_eq_bot B W W' hWE hW'E hminW hiW' hpair
  have hnd := restrict_nondegenerate B hsymm W W' hiW hiW' hkerL hkerR
  refine ⟨hnd, ?_⟩
  have hW0 : W ≠ ⊥ := by
    rintro rfl
    obtain ⟨v, hv, w, -, hvw⟩ := hpair
    rw [Submodule.mem_bot] at hv
    rw [hv, map_zero, LinearMap.zero_apply] at hvw
    exact hvw rfl
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
  have hr2 : ∀ b₁ b₂ : W', (∀ a : W, P a b₁ = P a b₂) → b₁ = b₂ := fun b₁ b₂ h =>
    sub_eq_zero.mp (hr _ fun a => by rw [map_sub, h, sub_self])
  have hl2 : ∀ a₁ a₂ : W, (∀ b : W', P a₁ b = P a₂ b) → a₁ = a₂ := fun a₁ a₂ h =>
    sub_eq_zero.mp (hl _ fun b => by rw [map_sub, LinearMap.sub_apply, h, sub_self])
  have : FiniteDimensional K W := Module.Finite.of_injective W.subtype Subtype.val_injective
  have : FiniteDimensional K W' := Module.Finite.of_injective W'.subtype Subtype.val_injective
  have hPinj : Function.Injective P := fun a₁ a₂ h => hl2 a₁ a₂ fun b => by rw [h]
  have hPfinj : Function.Injective P.flip := fun b₁ b₂ h => hr2 b₁ b₂ fun a => by
    have := congrArg (fun f : Module.Dual K W => f a) h
    simpa [LinearMap.flip_apply] using this
  have hdim : finrank K W = finrank K W' := by
    apply le_antisymm
    · have := LinearMap.finrank_le_finrank_of_injective hPinj
      rwa [Subspace.dual_finrank_eq] at this
    · have := LinearMap.finrank_le_finrank_of_injective hPfinj
      rwa [Subspace.dual_finrank_eq] at this
  let π : W' ≃ₗ[K] Module.Dual K W := LinearEquiv.ofBijective P.flip ⟨hPfinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq, hdim])).mp hPfinj⟩
  have hπ : ∀ (b : W') (a : W), π b a = P a b := fun b a => rfl
  obtain ⟨F, _, _, _, _, eK, χ, -, hact, -, -⟩ := exists_field_model hcomm hodd hWE hminW hW0
  let Φ : W →ₗ[K] Module.Dual K W :=
    (Algebra.traceForm K F).compl₁₂ (eK : W →ₗ[K] F) (eK : W →ₗ[K] F)
  have hΦ : ∀ a a' : W, Φ a a' = Algebra.trace K F (eK a * eK a') := fun a a' => by
    simp only [Φ, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Algebra.traceForm_apply]
  have hΦinj : Function.Injective Φ := by
    intro a₁ a₂ h
    have hnd' := traceForm_nondegenerate K F
    apply eK.injective
    rw [← sub_eq_zero]
    refine hnd'.1 _ fun c => ?_
    have h1 := congrArg (fun f : Module.Dual K W => f (eK.symm c)) h
    simp only [hΦ, LinearEquiv.apply_symm_apply] at h1
    rw [Algebra.traceForm_apply, sub_mul, map_sub, h1, sub_self]
  let φ : W →ₗ[K] W' := (π.symm : Module.Dual K W →ₗ[K] W') ∘ₗ Φ
  have hφ : ∀ a a' : W, P a' (φ a) = Φ a a' := fun a a' => by
    rw [← hπ]
    change (π (π.symm (Φ a))) a' = Φ a a'
    rw [LinearEquiv.apply_symm_apply]
  have hφinj : Function.Injective φ := π.symm.injective.comp hΦinj
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hφinj
  have hφx : ∀ (x : V ≃ₗ[K] V) (hx : x ∈ E) (a : W),
      φ ⟨x a, hWE x hx a a.2⟩ = ⟨x⁻¹ (φ a), hW'E x⁻¹ (inv_mem hx) _ (φ a).2⟩ := by
    intro x hx a
    refine hr2 _ _ fun a' => ?_
    let y : E := ⟨x, hx⟩
    have hxa' : eK ⟨x a', hWE x hx a' a'.2⟩ = (χ y : F) * eK a' := hact y a'
    rw [hφ, hΦ, hact y a, hP]
    change Algebra.trace K F ((χ y : F) * eK a * eK a') = B (a' : V) (x⁻¹ (φ a : V))
    have h1 : B (a' : V) (x⁻¹ (φ a : V)) = B (x a') (φ a : V) := by
      rw [← hiso x hx (a' : V) (x⁻¹ (φ a : V))]
      congr 1
      exact x.apply_symm_apply _
    rw [h1, ← hP ⟨x a', hWE x hx a' a'.2⟩, hφ, hΦ, hxa', mul_left_comm, mul_assoc]
  let σ : W →ₗ[K] Module.Dual K W := P.compl₂ φ
  have hσ : ∀ a₁ a : W, σ a₁ a = P a₁ (φ a) := fun _ _ => rfl
  have hσinj : Function.Injective σ := fun a₁ a₂ h => hl2 a₁ a₂ fun b => by
    obtain ⟨a, rfl⟩ := hφsurj b
    rw [← hσ, ← hσ, h]
  let σe : W ≃ₗ[K] Module.Dual K W := LinearEquiv.ofBijective σ ⟨hσinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq])).mp hσinj⟩
  let ψ : W' →ₗ[K] W := (σe.symm : Module.Dual K W →ₗ[K] W) ∘ₗ (π : W' →ₗ[K] Module.Dual K W)
  have hψ : ∀ (a : W) (b : W'), P (ψ b) (φ a) = P a b := fun a b => by
    rw [← hσ, ← hπ]
    change σe (σe.symm (π b)) a = π b a
    rw [LinearEquiv.apply_symm_apply]
  have hψx : ∀ (x : V ≃ₗ[K] V) (hx : x ∈ E) (b : W'),
      ψ ⟨x b, hW'E x hx b b.2⟩ = ⟨x⁻¹ (ψ b), hWE x⁻¹ (inv_mem hx) _ (ψ b).2⟩ := by
    intro x hx b
    refine hl2 _ _ fun c => ?_
    obtain ⟨a, rfl⟩ := hφsurj c
    rw [hψ, hP, hP]
    have hxa := hφx x⁻¹ (inv_mem hx) a
    have h1 : B (a : V) (x b) = B (x⁻¹ a) b := by
      rw [← hiso x⁻¹ (inv_mem hx) (a : V) (x b)]
      congr 1
      exact x.symm_apply_apply _
    have h2 : B (x⁻¹ (ψ b : V)) (φ a : V) = B (ψ b : V) (x (φ a : V)) := by
      rw [← hiso x hx (x⁻¹ (ψ b : V)) (φ a : V),
        show x (x⁻¹ (ψ b : V)) = (ψ b : V) from x.apply_symm_apply _]
    change B (a : V) (x b) = B (x⁻¹ (ψ b : V)) (φ a : V)
    rw [h1, h2, ← hP ⟨x⁻¹ a, hWE x⁻¹ (inv_mem hx) a a.2⟩, ← hψ, hxa]
    simp only [hP, inv_inv]
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
  let sw : (WU × W'U) →ₗ[K] (WU × W'U) :=
    LinearMap.prod ((eW.symm : W →ₗ[K] WU) ∘ₗ ψ ∘ₗ (eW' : W'U →ₗ[K] W') ∘ₗ LinearMap.snd K WU W'U)
      ((eW'.symm : W' →ₗ[K] W'U) ∘ₗ φ ∘ₗ (eW : WU →ₗ[K] W) ∘ₗ LinearMap.fst K WU W'U)
  let gU : U →ₗ[K] U := (e : (WU × W'U) →ₗ[K] U) ∘ₗ sw ∘ₗ (e.symm : U →ₗ[K] (WU × W'U))
  have hW1 : ∀ a : W, (((eW.symm a : WU) : U) : V) = a := fun a => by
    have h := Submodule.comapSubtypeEquivOfLe_apply_coe (le_sup_left : W ≤ U) (eW.symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hW2 : ∀ b : W', (((eW'.symm b : W'U) : U) : V) = b := fun b => by
    have h := Submodule.comapSubtypeEquivOfLe_apply_coe (le_sup_right : W' ≤ U) (eW'.symm b)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hgU : ∀ (a : W) (b : W'), ((gU ⟨a + b, Submodule.add_mem_sup a.2 b.2⟩ : U) : V) =
      ψ b + φ a := by
    intro a b
    have hab : (⟨a + b, Submodule.add_mem_sup a.2 b.2⟩ : U) =
        e (eW.symm a, eW'.symm b) := by
      apply Subtype.ext
      simp [e, Submodule.coe_prodEquivOfIsCompl', hW1, hW2]
    rw [hab]
    simp only [gU, sw, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prod_apply]
    simp [e, Submodule.coe_prodEquivOfIsCompl', hW1, hW2]
  have hUc : IsCompl U (B.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (fun x y h => by rw [hsymm]; exact h) hnd
  let g : V →ₗ[K] V := LinearMap.ofIsCompl hUc (U.subtype ∘ₗ gU) (B.orthogonal U).subtype
  have hgu : ∀ u : U, g u = ((gU u : U) : V) := fun u => by
    rw [LinearMap.ofIsCompl_apply_left hUc (u := u)]
    rfl
  have hg2 : ∀ (a : W) (b : W'), g (a + b) = ψ b + φ a := fun a b => by
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
    rw [hiW _ (ψ _).2 _ (ψ _).2, hiW' _ (φ _).2 _ (φ _).2, hiW _ ha _ ha', hiW' _ hb _ hb']
    have h1 := hψ ⟨a', ha'⟩ ⟨b, hb⟩
    have h2 := hψ ⟨a, ha⟩ ⟨b', hb'⟩
    rw [hP, hP] at h1 h2
    rw [h1, hsymm (φ _ : V), h2, hsymm b]
    abel
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    have hxa := congrArg Subtype.val (hφx x hx ⟨a, ha⟩)
    have hxb := congrArg Subtype.val (hψx x hx ⟨b, hb⟩)
    rw [map_add, show x a + x b = ((⟨x a, hWE x hx a ha⟩ : W) : V) +
      ((⟨x b, hW'E x hx b hb⟩ : W') : V) from rfl, hg2,
      show a + b = ((⟨a, ha⟩ : W) : V) + ((⟨b, hb⟩ : W') : V) from rfl, hg2, map_add]
    rw [hxa, hxb]

end FrobeniusIsometryInverse

open FrobeniusIsometry FrobeniusIsometryInverse in
theorem exists_isometry_conj_eq_inv [Fintype K] [CharP K 2] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V)
    (hsymm : ∀ v w, B v w = B w v) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    {E : Subgroup (V ≃ₗ[K] V)} [Finite E] (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hodd : Odd (Nat.card E)) (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) :
    ∃ J : V ≃ₗ[K] V, (∀ v w, B (J v) (J w) = B v w) ∧
      (∀ x ∈ E, J * x * J⁻¹ = x⁻¹) ∧ ∀ v, (∀ x ∈ E, x v = v) → J v = v := by
  have hnd' : (B.restrict ⊤).Nondegenerate :=
    (restrict_nondegenerate_iff hsymm).mpr fun v _ hv => hnd v fun w => hv w trivial
  obtain ⟨g, -, -, h3, h4, h5⟩ := exists_good hsymm hodd hiso (fun x => x⁻¹)
    (fun x hx => inv_mem hx)
    (fun W hWE hmin hW0 hWnd _ =>
      exists_isometry_inv_of_minimal B hsymm hcomm hodd hiso W hWE hmin hW0 hWnd)
    (fun W W' hWE hW'E hmW hmW' hiW hiW' hp =>
      exists_isometry_inv_of_pair B hsymm hcomm hodd hiso W W' hWE hW'E hmW hmW' hiW hiW' hp)
    _ ⊤ rfl (fun _ _ _ _ => trivial) hnd'
  have hinj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    refine hnd v fun w => ?_
    have h := h3 v trivial w trivial
    rwa [LinearMap.mem_ker.mp hv, map_zero, LinearMap.zero_apply, eq_comm] at h
  let ge : V ≃ₗ[K] V := LinearEquiv.ofInjectiveEndo g hinj
  refine ⟨ge, fun v w => h3 v trivial w trivial, fun x hx => ?_, fun v hv => h5 v trivial hv⟩
  refine LinearEquiv.ext fun v => ?_
  change ge (x (ge.symm v)) = x⁻¹ v
  have h := h4 x hx (ge.symm v) trivial
  change ge (x (ge.symm v)) = x⁻¹ (ge (ge.symm v)) at h
  rw [h, LinearEquiv.apply_symm_apply]

end CFSG.LinearAlgebra
