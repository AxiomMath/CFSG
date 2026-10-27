module

public import CFSG.LinearAlgebra.FrobeniusIsometryField
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.SimpleModule.Basic

public section

namespace CFSG.LinearAlgebra

variable {K : Type*} [Field K] [Fintype K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
theorem isSimpleModule_restrict {E : Subgroup (V ≃ₗ[K] V)} [CommGroup E]
    {W : Submodule K V}
    (hmin : ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W)
    (hW0 : W ≠ ⊥) (ρ : E →* (W →ₗ[K] W))
    (hρ : ∀ (x : E) (w : W), ((ρ x w : W) : V) = (x : V ≃ₗ[K] V) (w : V))
    [Module (MonoidAlgebra K E) W] [IsScalarTower K (MonoidAlgebra K E) W]
    (hof : ∀ (x : E) (w : W), MonoidAlgebra.of K E x • w = ρ x w) :
    IsSimpleModule (MonoidAlgebra K E) W := by
  have hWn : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  have : Nontrivial (Submodule (MonoidAlgebra K E) W) :=
    (Submodule.nontrivial_iff (R := MonoidAlgebra K E) (M := W)).mpr hWn
  have : IsSimpleOrder (Submodule (MonoidAlgebra K E) W) :=
    IsSimpleOrder.mk fun U => by
      have hUinv : ∀ x ∈ E, ∀ v ∈ (U.restrictScalars K).map W.subtype,
          x v ∈ (U.restrictScalars K).map W.subtype := by
        intro x hx v hv
        obtain ⟨u, hu, rfl⟩ := hv
        refine ⟨MonoidAlgebra.of K E ⟨x, hx⟩ • u,
          Submodule.smul_mem U (MonoidAlgebra.of K E ⟨x, hx⟩) hu, ?_⟩
        rw [hof ⟨x, hx⟩ u]
        exact hρ ⟨x, hx⟩ u
      rcases hmin ((U.restrictScalars K).map W.subtype)
        (Submodule.map_subtype_le (p := W) _) hUinv with h | h
      · left
        rw [eq_bot_iff]
        intro u hu
        have hmem : (u : V) ∈ (U.restrictScalars K).map W.subtype := ⟨u, hu, rfl⟩
        rw [h, Submodule.mem_bot] at hmem
        exact Subtype.ext hmem
      · right
        rw [eq_top_iff]
        intro w _
        have hw : (w : V) ∈ (U.restrictScalars K).map W.subtype := by
          rw [h]
          exact w.2
        obtain ⟨u, hu, huw⟩ := hw
        have huw' : u = w := Subtype.ext huw
        rwa [← huw']
  exact IsSimpleModule.mk

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
theorem exists_adjoin_eq_top_of_surjective {E : Subgroup (V ≃ₗ[K] V)} {F : Type*}
    [Field F] [Finite F] [Algebra K F]
    (ψ : MonoidAlgebra K E →ₐ[K] F) (hψ : Function.Surjective ψ) (χ : E →* Fˣ)
    (hχ : ∀ x : E, (χ x : F) = ψ (MonoidAlgebra.of K E x)) (hodd : Odd (Nat.card E)) :
    ∃ (t : Fˣ) (x₀ : E), χ x₀ = t ∧ Subgroup.zpowers t = χ.range ∧
      Odd (orderOf t) ∧ Algebra.adjoin K ({(t : F)} : Set F) = ⊤ := by
  have hcyc : IsCyclic ↥χ.range := by
    refine isCyclic_of_subgroup_isDomain ((Units.coeHom F).comp χ.range.subtype) ?_
    intro x y hxy
    exact Subtype.ext (Units.ext hxy)
  obtain ⟨t, ht⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top χ.range).mp hcyc
  have htmem : t ∈ χ.range := by
    rw [← ht]
    exact Subgroup.mem_zpowers t
  obtain ⟨x₀, hx₀⟩ := htmem
  refine ⟨t, x₀, hx₀, ht, ?_, ?_⟩
  · have h1 : orderOf t ∣ orderOf x₀ := by
      rw [← hx₀]
      exact orderOf_map_dvd χ x₀
    exact Odd.of_dvd_nat hodd (h1.trans (orderOf_dvd_natCard x₀))
  · rw [eq_top_iff]
    intro y _
    obtain ⟨a, rfl⟩ := hψ y
    refine MonoidAlgebra.induction_on (motive := fun a =>
      ψ a ∈ Algebra.adjoin K ({(t : F)} : Set F)) a ?_ ?_ ?_
    · intro m
      have hmem : χ m ∈ Subgroup.zpowers t := by
        rw [ht]
        exact ⟨m, rfl⟩
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (χ m) t).mp
        (mem_powers_iff_mem_zpowers.mpr hmem)
      have hval : (χ m : F) = (t : F) ^ n := by
        rw [← hn]
        exact Units.val_pow_eq_pow_val (a := t) n
      rw [← hχ m, hval]
      exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (by simp)) n
    · intro a b ha hb
      rw [map_add]
      exact Subalgebra.add_mem _ ha hb
    · intro c a ha
      have hmul : ψ (algebraMap K (MonoidAlgebra K E) c) = algebraMap K F c :=
        ψ.commutes c
      rw [Algebra.smul_def, map_mul, hmul]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ c) ha

theorem exists_linearEquiv_mul_pow_card_isometry {F : Type*} [Field F] [Finite F] [Algebra K F]
    [FiniteDimensional K F] (b : F →ₗ[K] F →ₗ[K] K) (hsymm : ∀ a a', b a a' = b a' a)
    (hnd : ∀ a, (∀ a', b a a' = 0) → a = 0) {t : F} (ht1 : t ≠ 1) (hodd : Odd (orderOf t))
    (hgen : Algebra.adjoin K ({t} : Set F) = ⊤) (hiso : ∀ a a', b (t * a) (t * a') = b a a') :
    ∃ (u : F) (gF : F ≃ₗ[K] F), u ≠ 0 ∧ (∀ a, gF a = u * a ^ Fintype.card K) ∧
      ∀ a a', b (gF a) (gF a') = b a a' := by
  obtain ⟨u, hu0, hu⟩ := exists_mul_pow_card_isometry b hsymm hnd ht1 hodd hgen hiso
  let φ : F ≃ₐ[K] F := FiniteField.frobeniusAlgEquivOfAlgebraic K F
  have hφ : ∀ a, φ a = a ^ Fintype.card K := fun a =>
    FiniteField.frobeniusAlgEquivOfAlgebraic_apply K F a
  let uu : Fˣ := Units.mk0 u hu0
  let gF : F ≃ₗ[K] F := φ.toLinearEquiv.trans (DistribMulAction.toLinearEquiv K F uu)
  have hgF : ∀ a, gF a = u * a ^ Fintype.card K := fun a => by
    change uu • φ a = u * a ^ Fintype.card K
    rw [Units.smul_def, hφ]
    rfl
  refine ⟨u, gF, hu0, hgF, fun a a' => ?_⟩
  rw [hgF a, hgF a']
  exact hu a a'

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
theorem exists_isometry_extend (B : LinearMap.BilinForm K V) {W : Submodule K V}
    (hcompl : IsCompl W (B.orthogonal W)) (gW : W →ₗ[K] W)
    (hiso : ∀ v w : W, B (gW v) (gW w) = B (v : V) (w : V)) :
    ∃ g : V →ₗ[K] V, (∀ v : W, g (v : V) = (gW v : V)) ∧
      (∀ v ∈ B.orthogonal W, g v = v) ∧
      ∀ v w : W, B (g (v : V)) (g (w : V)) = B (v : V) (w : V) := by
  refine ⟨LinearMap.ofIsCompl hcompl (W.subtype ∘ₗ gW) (B.orthogonal W).subtype, ?_, ?_, ?_⟩
  · intro v
    rw [LinearMap.ofIsCompl_apply_left hcompl (u := v)]
    rfl
  · intro v hv
    rw [LinearMap.ofIsCompl_apply_right hcompl (v := ⟨v, hv⟩)]
    rfl
  · intro v w
    rw [LinearMap.ofIsCompl_apply_left hcompl (u := v),
      LinearMap.ofIsCompl_apply_left hcompl (u := w)]
    exact hiso v w

omit [FiniteDimensional K V] in
theorem exists_isometry_pow_card_of_field {E : Subgroup (V ≃ₗ[K] V)}
    (B : LinearMap.BilinForm K V)
    (hsymm : ∀ v w, B v w = B w v) {W : Submodule K V}
    (hWnd : (B.restrict W).Nondegenerate)
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W)
    {F : Type*} [Field F] [Finite F] [Algebra K F] [FiniteDimensional K F]
    (eK : W ≃ₗ[K] F) (χ : E →* Fˣ)
    (hact : ∀ (x : E) (w : W),
      eK ⟨(x : V ≃ₗ[K] V) (w : V), hWE (x : V ≃ₗ[K] V) x.2 w w.2⟩ =
        (χ x : F) * eK w)
    {t : F} (ht1 : t ≠ 1) (hodd : Odd (orderOf t))
    (hgen : Algebra.adjoin K ({t} : Set F) = ⊤)
    (hx₀ : ∃ x₀ : E, (χ x₀ : F) = t)
    (hiso : ∀ x ∈ E, ∀ v w : V, B (x v) (x w) = B v w) :
    ∃ gW : W →ₗ[K] W, (∀ v w : W, B (gW v) (gW w) = B (v : V) (w : V)) ∧
      ∀ (x : V ≃ₗ[K] V) (hx : x ∈ E) (w : W),
        ((gW ⟨x (w : V), hWE x hx w w.2⟩ : W) : V) =
          (x ^ Fintype.card K) ((gW w : W) : V) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hx₀
  let i : F →ₗ[K] V := W.subtype ∘ₗ (eK.symm : F →ₗ[K] W)
  let b : F →ₗ[K] F →ₗ[K] K := B.compl₁₂ i i
  have hb_apply : ∀ a a', b a a' = B (i a) (i a') := fun a a' =>
    LinearMap.compl₁₂_apply B i i a a'
  have hb_symm : ∀ a a', b a a' = b a' a := by
    intro a a'
    rw [hb_apply, hb_apply]
    exact hsymm _ _
  have hb_nd : ∀ a, (∀ a', b a a' = 0) → a = 0 := by
    intro a ha
    have hzeroW : eK.symm a = 0 := by
      apply hWnd.1
      intro w
      have h := ha (eK w)
      rw [hb_apply] at h
      have hia : i a = ((eK.symm a : W) : V) := rfl
      have hiw : i (eK w) = (w : V) := by
        change W.subtype (eK.symm (eK w)) = (w : V)
        rw [LinearEquiv.symm_apply_apply]
        rfl
      rw [hia, hiw] at h
      simpa using h
    have := congrArg (fun w : W => eK w) hzeroW
    simpa using this
  have hb_iso : ∀ a a', b (t * a) (t * a') = b a a' := by
    have hshift : ∀ a : F, i (t * a) = (x₀ : V ≃ₗ[K] V) (i a) := by
      intro a
      have h1W : eK.symm (t * a) =
          ⟨(x₀ : V ≃ₗ[K] V) ((eK.symm a : W) : V),
            hWE (x₀ : V ≃ₗ[K] V) x₀.2 ((eK.symm a : W) : V)
              (eK.symm a).2⟩ := by
        refine eK.injective ?_
        rw [LinearEquiv.apply_symm_apply, hact x₀ (eK.symm a),
          LinearEquiv.apply_symm_apply, ← hx₀]
      change W.subtype (eK.symm (t * a)) = (x₀ : V ≃ₗ[K] V) (i a)
      rw [h1W]
      rfl
    intro a a'
    rw [hb_apply, hb_apply, hshift, hshift]
    exact hiso x₀ x₀.2 (i a) (i a')
  obtain ⟨u, gF, hu0, hgF, hisoF⟩ :=
    exists_linearEquiv_mul_pow_card_isometry b hb_symm hb_nd ht1 hodd hgen hb_iso
  let gW : W →ₗ[K] W :=
    (eK.symm : F →ₗ[K] W) ∘ₗ (gF : F →ₗ[K] F) ∘ₗ (eK : W →ₗ[K] F)
  have hgW : ∀ w : W, gW w = eK.symm (gF (eK w)) := fun w => rfl
  have heK_gW : ∀ w : W, eK (gW w) = gF (eK w) := fun w => by
    rw [hgW, LinearEquiv.apply_symm_apply]
  refine ⟨gW, ?_, ?_⟩
  · intro v w
    have hv : (gW v : V) = i (gF (eK v)) := rfl
    have hw : (gW w : V) = i (gF (eK w)) := rfl
    rw [hv, hw]
    have h := hisoF (eK v) (eK w)
    rw [hb_apply, hb_apply] at h
    have hve : i (eK v) = (v : V) := by
      change W.subtype (eK.symm (eK v)) = (v : V)
      rw [LinearEquiv.symm_apply_apply]
      rfl
    have hwe : i (eK w) = (w : V) := by
      change W.subtype (eK.symm (eK w)) = (w : V)
      rw [LinearEquiv.symm_apply_apply]
      rfl
    rwa [hve, hwe] at h
  · intro x hx w
    let y : E := ⟨x, hx⟩
    have hval : (χ (y ^ Fintype.card K) : F) = (χ y : F) ^ Fintype.card K := by
      rw [map_pow]
      exact Units.val_pow_eq_pow_val (a := χ y) _
    have hL : eK (gW ⟨x (w : V), hWE x hx w w.2⟩) =
        u * ((χ y : F) ^ Fintype.card K * (eK w) ^ Fintype.card K) := by
      rw [heK_gW, hact y w, hgF, mul_pow]
    have hR : eK ⟨(x ^ Fintype.card K) ((gW w : W) : V),
          hWE (x ^ Fintype.card K) (pow_mem hx (Fintype.card K))
            ((gW w : W) : V) (gW w).2⟩ =
        (χ y : F) ^ Fintype.card K * (u * (eK w) ^ Fintype.card K) := by
      have h1 := hact (y ^ Fintype.card K) (gW w)
      rw [hval, heK_gW, hgF] at h1
      simpa [Subgroup.coe_pow] using h1
    have hEq : gW ⟨x (w : V), hWE x hx w w.2⟩ =
        ⟨(x ^ Fintype.card K) ((gW w : W) : V),
          hWE (x ^ Fintype.card K) (pow_mem hx (Fintype.card K))
            ((gW w : W) : V) (gW w).2⟩ := by
      apply eK.injective
      rw [hL, hR]
      ring
    exact congrArg Subtype.val hEq

omit [Fintype K] [CharP K 2] [FiniteDimensional K V] in
theorem eq_bot_of_generator_eq_one {E : Subgroup (V ≃ₗ[K] V)} {W : Submodule K V}
    (hW0 : W ≠ ⊥) (hfix : ∀ v ∈ W, (∀ x ∈ E, x v = v) → v = 0)
    (ρ : E →* (W →ₗ[K] W))
    (hρ : ∀ (x : E) (w : W), ((ρ x w : W) : V) = (x : V ≃ₗ[K] V) (w : V))
    {F : Type*} [Field F] [Algebra K F] (e : W ≃ₗ[K] F) (χ : E →* Fˣ)
    (he_act : ∀ (x : E) (w : W), e (ρ x w) = (χ x : F) * e w)
    {t : Fˣ} (htrange : Subgroup.zpowers t = χ.range) (ht : (t : F) = 1) :
    False := by
  have htunit : t = 1 := Units.ext ht
  have hχone : ∀ y : E, χ y = 1 := by
    intro y
    have hmem : χ y ∈ Subgroup.zpowers t := by
      rw [htrange]
      exact ⟨y, rfl⟩
    rw [htunit, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmem
    exact hmem
  have hfixW : ∀ w : W, w = 0 := by
    intro w
    have hx : ∀ x ∈ E, (x : V ≃ₗ[K] V) (w : V) = (w : V) := by
      intro x hxE
      have h1 : e (ρ ⟨x, hxE⟩ w) = e w := by
        rw [he_act, show χ ⟨x, hxE⟩ = 1 from hχone ⟨x, hxE⟩]
        simp
      have h2 : ρ ⟨x, hxE⟩ w = w := e.injective h1
      rw [← hρ ⟨x, hxE⟩ w, h2]
    have h3 : (w : V) = 0 := hfix (w : V) w.2 hx
    exact Subtype.ext h3
  have hWbot : W = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have h4 : (⟨v, hv⟩ : W) = 0 := hfixW ⟨v, hv⟩
    simpa using congrArg Subtype.val h4
  exact hW0 hWbot

theorem exists_isometry_pow_card_of_minimal (B : LinearMap.BilinForm K V)
    (hsymm : ∀ v w, B v w = B w v) {E : Subgroup (V ≃ₗ[K] V)} [Finite E]
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hodd : Odd (Nat.card E))
    (hiso : ∀ x ∈ E, ∀ v w, B (x v) (x w) = B v w) (W : Submodule K V)
    (hWE : ∀ x ∈ E, ∀ v ∈ W, x v ∈ W)
    (hmin : ∀ U : Submodule K V, U ≤ W → (∀ x ∈ E, ∀ v ∈ U, x v ∈ U) → U = ⊥ ∨ U = W)
    (hW0 : W ≠ ⊥) (hWnd : (B.restrict W).Nondegenerate)
    (hfix : ∀ v ∈ W, (∀ x ∈ E, x v = v) → v = 0) :
    ∃ g : V →ₗ[K] V, (∀ v ∈ W, g v ∈ W) ∧ (∀ v ∈ B.orthogonal W, g v = v) ∧
      (∀ v ∈ W, ∀ w ∈ W, B (g v) (g w) = B v w) ∧
      ∀ x ∈ E, ∀ v ∈ W, g (x v) = (x ^ Fintype.card K) (g v) := by
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
  obtain ⟨t, x₀, hx₀, htrange, hodd_t, hgen⟩ :=
    exists_adjoin_eq_top_of_surjective ψ hψ χ hχ hodd
  have he_actK : ∀ (x : E) (w : W), eK (ρ x w) = (χ x : F) * eK w :=
    fun x w => he_act x w
  have ht1 : (t : F) ≠ 1 := fun ht =>
    eq_bot_of_generator_eq_one hW0 hfix ρ hρ eK χ he_actK htrange ht
  have hoddF : Odd (orderOf (t : F)) := by
    rwa [orderOf_units]
  have hact : ∀ (x : E) (w : W),
      eK ⟨(x : V ≃ₗ[K] V) (w : V), hWE (x : V ≃ₗ[K] V) x.2 w w.2⟩ =
        (χ x : F) * eK w := fun x w => he_act x w
  have hx₀F : ∃ x₀ : E, (χ x₀ : F) = (t : F) := by
    refine ⟨x₀, ?_⟩
    rw [hx₀]
  obtain ⟨gW, hgWiso, hgWsem⟩ :=
    exists_isometry_pow_card_of_field B hsymm hWnd hWE eK χ hact ht1 hoddF hgen hx₀F hiso
  have hcompl : IsCompl W (B.orthogonal W) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
      (B := B) (W := W) (fun x y h => by rwa [hsymm y x]) hWnd
  obtain ⟨g, hgform, hgorth, hgiso⟩ := exists_isometry_extend B hcompl gW hgWiso
  refine ⟨g, ?_, hgorth, ?_, ?_⟩
  · intro v hv
    rw [hgform ⟨v, hv⟩]
    exact (gW ⟨v, hv⟩).2
  · intro v hv w hw
    rw [hgform ⟨v, hv⟩, hgform ⟨w, hw⟩]
    exact hgWiso ⟨v, hv⟩ ⟨w, hw⟩
  · intro x hx v hv
    have hxmem : x v ∈ W := hWE x hx v hv
    rw [hgform ⟨x v, hxmem⟩, hgform ⟨v, hv⟩]
    exact hgWsem x hx ⟨v, hv⟩

end CFSG.LinearAlgebra
