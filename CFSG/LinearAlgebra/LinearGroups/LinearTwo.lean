module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoCoordinateQuotients
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas

public section

namespace CFSG.LinearGroups

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter Matrix

universe u

variable {K : Type u} [Field K]

theorem linear_two_projective_identification (K : Type u) [Field K] :
    coordinateEquiv K none = Projectivization.mk K ![1, 0] psl2_e0_ne_zero ∧
      (∀ x : K, coordinateEquiv K (some x) =
        Projectivization.mk K ![x, 1] (psl2AffineVector_ne_zero x)) ∧
      (∀ g : ProjectiveSpecialLinearGroup (Fin 2) K,
        ((pslEquivCoordinateG K g : coordinateG K) : Equiv.Perm (Omega K)) =
          coordinatePSLAction K g) ∧
      (∀ (g : ProjectiveSpecialLinearGroup (Fin 2) K) (x : Omega K),
        coordinateEquiv K (coordinatePSLAction K g x) = g • coordinateEquiv K x) ∧
      (coordinateGLAction K).range = coordinateD K ∧
      (∀ (A : GL (Fin 2) K) (x : Omega K),
        coordinateEquiv K (coordinateGLAction K A x) =
          Matrix.ProjGenLinGroup.mk A • coordinateEquiv K x) ∧
      (∀ (A : GL (Fin 2) K) (x : K),
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (A : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 →
          coordinateGLAction K A (some x) =
            some (((A : Matrix (Fin 2) (Fin 2) K) 0 0 * x + (A : Matrix (Fin 2) (Fin 2) K) 0 1) /
              ((A : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (A : Matrix (Fin 2) (Fin 2) K) 1 1))) ∧
      (∀ (A : GL (Fin 2) K) (x : K),
        (A : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 →
          coordinateGLAction K A (some x) = none) ∧
      (∀ A : GL (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 →
        coordinateGLAction K A none =
          some ((A : Matrix (Fin 2) (Fin 2) K) 0 0 / (A : Matrix (Fin 2) (Fin 2) K) 1 0)) ∧
      (∀ A : GL (Fin 2) K, (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 →
        coordinateGLAction K A none = none) ∧
      MulAction.IsPretransitive (coordinateG K) (Omega K) :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, coordinatePSLAction_point K, coordinateGLAction_range K,
    fun _ x => coordinatePGLAction_point K _ x, coordinateGLAction_finite K,
    coordinateGLAction_finite_denominator_zero K, coordinateGLAction_infinity K,
    coordinateGLAction_infinity_lower_left_zero K, ⟨coordinateG_transitive K⟩⟩

@[expose] def coordinateB (K : Type u) [Field K] : Subgroup (Equiv.Perm (Omega K)) :=
  coordinateG K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) (none : Omega K)

theorem mem_coordinateB_iff {g : Equiv.Perm (Omega K)} :
    g ∈ coordinateB K ↔ g ∈ coordinateG K ∧ g none = none :=
  Iff.rfl

@[expose] def translationHom (K : Type u) [Field K] : Multiplicative K →* Equiv.Perm (Omega K) where
  toFun b := translation K b.toAdd
  map_one' := by
    ext x
    cases x <;> simp
  map_mul' b c := by
    ext x
    cases x <;> simp [add_comm, add_left_comm]

theorem translationHom_apply (b : K) :
    translationHom K (Multiplicative.ofAdd b) = translation K b :=
  rfl

theorem translationHom_injective : Function.Injective (translationHom K) := by
  intro b c h
  have := congrArg (fun g : Equiv.Perm (Omega K) => g (some 0)) h
  simpa [translationHom] using this

theorem coordinateU_eq_range : coordinateU K = (translationHom K).range := by
  have h : Set.range (translation K) = Set.range (translationHom K) := by
    ext g
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨Multiplicative.ofAdd b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b.toAdd, rfl⟩
  rw [coordinateU, h, ← MonoidHom.coe_range, Subgroup.closure_eq]

theorem coordinatePSLAction_mk (A : SpecialLinearGroup (Fin 2) K) :
    coordinatePSLAction K (QuotientGroup.mk A) =
      coordinateGLAction K (SpecialLinearGroup.toGL A) := by
  rw [← coordinatePGLAction_toPGL, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  rfl

theorem coordinatePSLAction_mk_some (A : SpecialLinearGroup (Fin 2) K) (x : K)
    (hden : (A : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (A : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0) :
    coordinatePSLAction K (QuotientGroup.mk A) (some x) =
      some (((A : Matrix (Fin 2) (Fin 2) K) 0 0 * x + (A : Matrix (Fin 2) (Fin 2) K) 0 1) /
        ((A : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (A : Matrix (Fin 2) (Fin 2) K) 1 1)) := by
  rw [coordinatePSLAction_mk]
  exact coordinateGLAction_finite K _ x hden

theorem coordinatePSLAction_mk_none_of_ne (A : SpecialLinearGroup (Fin 2) K)
    (hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    coordinatePSLAction K (QuotientGroup.mk A) none =
      some ((A : Matrix (Fin 2) (Fin 2) K) 0 0 / (A : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  rw [coordinatePSLAction_mk]
  exact coordinateGLAction_infinity K _ hc

theorem coordinatePSLAction_mk_none_of_eq (A : SpecialLinearGroup (Fin 2) K)
    (hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    coordinatePSLAction K (QuotientGroup.mk A) none = none := by
  rw [coordinatePSLAction_mk]
  exact coordinateGLAction_infinity_lower_left_zero K _ hc

@[expose] def sl2Diagonal (a : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(a : K), 0; 0, ((a⁻¹ : Kˣ) : K)], by simp [det_fin_two_of]⟩

theorem coordinatePSLAction_sl2Diagonal (a : Kˣ) :
    coordinatePSLAction K (QuotientGroup.mk (sl2Diagonal a)) = multiplier K (a ^ 2) := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none =>
    rw [coordinatePSLAction_mk_none_of_eq _ (by simp [sl2Diagonal]), multiplier_none]
  | some x =>
    rw [coordinatePSLAction_mk_some _ x (by simp [sl2Diagonal]), multiplier_some]
    congr 1
    simp only [sl2Diagonal, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
    ring

theorem multiplier_sq_mem_coordinateG (a : Kˣ) : multiplier K (a ^ 2) ∈ coordinateG K := by
  rw [← coordinatePSLAction_range_eq_G]
  exact ⟨_, coordinatePSLAction_sl2Diagonal a⟩

theorem translation_mem_coordinateG (b : K) : translation K b ∈ coordinateG K :=
  Subgroup.subset_closure (Or.inl ⟨b, rfl⟩)

theorem mem_coordinateB_iff_affine {g : Equiv.Perm (Omega K)} :
    g ∈ coordinateB K ↔ g none = none ∧
      ∃ (s : Kˣ) (b : K), (∃ a : Kˣ, s = a ^ 2) ∧ ∀ x : K, g (some x) = some (s * x + b) := by
  constructor
  · intro hg
    obtain ⟨hG, hinf⟩ := mem_coordinateB_iff.mp hg
    refine ⟨hinf, ?_⟩
    rw [← coordinatePSLAction_range_eq_G] at hG
    obtain ⟨h, rfl⟩ := hG
    obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective h
    have hdet := A.2
    rw [det_fin_two] at hdet
    have hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      by_contra hc
      rw [coordinatePSLAction_mk_none_of_ne _ hc] at hinf
      exact Option.some_ne_none _ hinf
    rw [hc, mul_zero, sub_zero] at hdet
    have ha : (A : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have hd : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = ((A : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    refine ⟨Units.mk0 _ ha ^ 2, (A : Matrix (Fin 2) (Fin 2) K) 0 0 *
      (A : Matrix (Fin 2) (Fin 2) K) 0 1, ⟨_, rfl⟩, fun x => ?_⟩
    rw [coordinatePSLAction_mk_some _ x (by rw [hc, hd, zero_mul, zero_add]; exact inv_ne_zero ha)]
    congr 1
    rw [hc, hd, zero_mul, zero_add, div_inv_eq_mul]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    ring
  · rintro ⟨hinf, s, b, ⟨a, rfl⟩, hg⟩
    have hgeq : g = translation K b * multiplier K (a ^ 2) := by
      ext x
      cases x with
      | none => simp [hinf]
      | some x => simp [hg]
    refine mem_coordinateB_iff.mpr ⟨?_, hinf⟩
    rw [hgeq]
    exact (coordinateG K).mul_mem (translation_mem_coordinateG b) (multiplier_sq_mem_coordinateG a)

theorem affine_params_unique {s s' : Kˣ} {b b' : K}
    (h : ∀ x : K, (s : K) * x + b = s' * x + b') : s = s' ∧ b = b' := by
  have h0 := h 0
  have h1 := h 1
  simp only [mul_zero, zero_add, mul_one] at h0 h1
  refine ⟨Units.ext ?_, h0⟩
  rw [h0] at h1
  exact add_right_cancel h1

theorem translation_mem_coordinateB (b : K) : translation K b ∈ coordinateB K :=
  mem_coordinateB_iff.mpr ⟨translation_mem_coordinateG b, rfl⟩

theorem multiplier_sq_mem_coordinateB (a : Kˣ) : multiplier K (a ^ 2) ∈ coordinateB K :=
  mem_coordinateB_iff.mpr ⟨multiplier_sq_mem_coordinateG a, rfl⟩

theorem coordinateU_le_coordinateB : coordinateU K ≤ coordinateB K := by
  rw [coordinateU, Subgroup.closure_le]
  rintro _ ⟨b, rfl⟩
  exact translation_mem_coordinateB b

theorem conj_translation_of_affine {g : Equiv.Perm (Omega K)} (hg0 : g none = none) {s : Kˣ}
    {c : K} (hg : ∀ x, g (some x) = some (s * x + c)) (b : K) :
    g * translation K b * g⁻¹ = translation K (s * b) := by
  refine Equiv.ext fun y => ?_
  obtain ⟨z, rfl⟩ := g.surjective y
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  cases z with
  | none => rw [translation_none, hg0, translation_none]
  | some x =>
    rw [translation_some, hg, hg, translation_some]
    congr 1
    ring

theorem coordinateU_fixed_points :
    {x : Omega K | ∀ u ∈ coordinateU K, u x = x} = {none} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    cases x with
    | none => rfl
    | some y =>
      have h := hx (translation K 1) (Subgroup.subset_closure ⟨1, rfl⟩)
      rw [translation_some, Option.some_inj, add_eq_left] at h
      exact (one_ne_zero h).elim
  · rintro rfl u hu
    exact (mem_coordinateB_iff.mp (coordinateU_le_coordinateB hu)).2

@[expose] def affineSlope (g : Equiv.Perm (Omega K)) : K :=
  (g (some 1)).getD 0 - (g (some 0)).getD 0

theorem affineSlope_eq {g : Equiv.Perm (Omega K)} {s : Kˣ} {b : K}
    (hg : ∀ x, g (some x) = some (s * x + b)) : affineSlope g = s := by
  simp [affineSlope, hg]

theorem exists_affine_of_mem_coordinateB {g : Equiv.Perm (Omega K)} (hg : g ∈ coordinateB K) :
    ∃ (s : Kˣ) (b : K), (∃ a : Kˣ, s = a ^ 2) ∧ ∀ x : K, g (some x) = some (s * x + b) :=
  (mem_coordinateB_iff_affine.mp hg).2

@[expose] noncomputable def coordinateBSlope (K : Type u) [Field K] : coordinateB K →* Kˣ where
  toFun g := Units.mk0 (affineSlope (g : Equiv.Perm (Omega K))) (by
    obtain ⟨s, b, -, hs⟩ := exists_affine_of_mem_coordinateB g.2
    rw [affineSlope_eq hs]
    exact s.ne_zero)
  map_one' := by
    ext
    simp [affineSlope]
  map_mul' g h := by
    obtain ⟨s, b, -, hs⟩ := exists_affine_of_mem_coordinateB g.2
    obtain ⟨t, c, -, ht⟩ := exists_affine_of_mem_coordinateB h.2
    have hgh : ∀ x : K, ((g * h : coordinateB K) : Equiv.Perm (Omega K)) (some x) =
        some ((s * t : Kˣ) * x + (s * c + b)) := by
      intro x
      simp only [Subgroup.coe_mul, Equiv.Perm.mul_apply, ht, hs, Units.val_mul]
      congr 1
      ring
    ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [affineSlope_eq hgh, affineSlope_eq hs, affineSlope_eq ht, Units.val_mul]

theorem coordinateBSlope_eq {g : coordinateB K} {s : Kˣ} {b : K}
    (hg : ∀ x, (g : Equiv.Perm (Omega K)) (some x) = some (s * x + b)) :
    coordinateBSlope K g = s :=
  Units.ext (affineSlope_eq hg)

theorem coordinateBSlope_range :
    (coordinateBSlope K).range = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  ext s
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨t, b, ⟨a, rfl⟩, ht⟩ := exists_affine_of_mem_coordinateB g.2
    rw [coordinateBSlope_eq ht]
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨⟨multiplier K (a ^ 2), multiplier_sq_mem_coordinateB a⟩, ?_⟩
    exact coordinateBSlope_eq (b := 0) fun x => by simp

theorem coordinateBSlope_ker :
    (coordinateBSlope K).ker = (coordinateU K).subgroupOf (coordinateB K) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, coordinateU_eq_range]
  obtain ⟨s, b, -, hs⟩ := exists_affine_of_mem_coordinateB g.2
  rw [coordinateBSlope_eq hs]
  constructor
  · rintro rfl
    refine ⟨Multiplicative.ofAdd b, Equiv.ext fun x => ?_⟩
    cases x with
    | none => exact ((mem_coordinateB_iff.mp g.2).2).symm
    | some x => simp [translationHom_apply, hs]
  · rintro ⟨c, hc⟩
    have h := fun x => (congrArg (fun f : Equiv.Perm (Omega K) => f (some x)) hc).symm
    simp only [translationHom, MonoidHom.coe_mk, OneHom.coe_mk, translation_some, hs,
      Option.some_inj] at h
    exact (affine_params_unique (s' := 1) (b' := c.toAdd) fun x => by simpa [add_comm] using h x).1

instance coordinateU_normal_in_B : ((coordinateU K).subgroupOf (coordinateB K)).Normal := by
  rw [← coordinateBSlope_ker]
  exact MonoidHom.normal_ker _

@[expose] noncomputable def coordinateBQuotientEquiv (K : Type u) [Field K] :
    coordinateB K ⧸ (coordinateU K).subgroupOf (coordinateB K) ≃*
      (powMonoidHom 2 : Kˣ →* Kˣ).range :=
  (QuotientGroup.quotientMulEquivOfEq coordinateBSlope_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr coordinateBSlope_range))

@[expose] noncomputable def coordinateUEquiv (K : Type u) [Field K] :
    Multiplicative K ≃* coordinateU K :=
  (MonoidHom.ofInjective translationHom_injective).trans
    (MulEquiv.subgroupCongr coordinateU_eq_range.symm)

theorem coordinateUEquiv_apply (b : K) :
    (coordinateUEquiv K (Multiplicative.ofAdd b) : Equiv.Perm (Omega K)) = translation K b :=
  rfl

theorem card_coordinateU : Nat.card (coordinateU K) = Nat.card K :=
  (Nat.card_congr (coordinateUEquiv K).toEquiv).symm.trans (Nat.card_congr Multiplicative.toAdd)

theorem card_coordinateB :
    Nat.card (coordinateB K) = Nat.card K * Nat.card (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((coordinateU K).subgroupOf (coordinateB K)),
    Nat.card_congr (coordinateBQuotientEquiv K).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe coordinateU_le_coordinateB).toEquiv,
    card_coordinateU, mul_comm]

theorem linear_two_affine_stabilizer (K : Type u) [Field K] :
    coordinateB K = coordinateG K ⊓ MulAction.stabilizer (Equiv.Perm (Omega K)) (none : Omega K) ∧
      (coordinateU K : Set (Equiv.Perm (Omega K))) = Set.range (translation K) ∧
      (∃ e : Multiplicative K ≃* coordinateU K,
        ∀ b : K, (e (Multiplicative.ofAdd b) : Equiv.Perm (Omega K)) = translation K b) ∧
      (∀ g : Equiv.Perm (Omega K), g ∈ coordinateB K ↔ g none = none ∧
        ∃ (s : Kˣ) (b : K), (∃ a : Kˣ, s = a ^ 2) ∧ ∀ x : K, g (some x) = some (s * x + b)) ∧
      (∀ (g : Equiv.Perm (Omega K)) (s s' : Kˣ) (b b' : K),
        (∀ x : K, g (some x) = some (s * x + b)) → (∀ x : K, g (some x) = some (s' * x + b')) →
          s = s' ∧ b = b') ∧
      coordinateU K ≤ coordinateB K ∧ ((coordinateU K).subgroupOf (coordinateB K)).Normal ∧
      Nonempty (coordinateB K ⧸ (coordinateU K).subgroupOf (coordinateB K) ≃*
        (powMonoidHom 2 : Kˣ →* Kˣ).range) ∧
      (Finite K → Nat.card (coordinateU K) = Nat.card K ∧
        Nat.card (coordinateB K) = Nat.card K * Nat.card (powMonoidHom 2 : Kˣ →* Kˣ).range) ∧
      {x : Omega K | ∀ u ∈ coordinateU K, u x = x} = {none} := by
  have hU : (coordinateU K : Set (Equiv.Perm (Omega K))) = Set.range (translation K) := by
    rw [coordinateU_eq_range, MonoidHom.coe_range]
    ext g
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.toAdd, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Multiplicative.ofAdd b, rfl⟩
  refine ⟨rfl, hU,
    ⟨coordinateUEquiv K, coordinateUEquiv_apply⟩, fun g => mem_coordinateB_iff_affine,
    fun _ _ _ _ _ h h' =>
      affine_params_unique fun x => Option.some_inj.mp ((h x).symm.trans (h' x)),
    coordinateU_le_coordinateB, inferInstance, ⟨coordinateBQuotientEquiv K⟩,
    fun _ => ⟨card_coordinateU, card_coordinateB⟩, coordinateU_fixed_points⟩

theorem coordinateB_subgroupOf_eq_stabilizer :
    (coordinateB K).subgroupOf (coordinateG K) =
      MulAction.stabilizer (coordinateG K) (none : Omega K) := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_coordinateB_iff, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩

theorem coordinateB_le_coordinateG : coordinateB K ≤ coordinateG K := inf_le_left

theorem coordinateU_le_coordinateG : coordinateU K ≤ coordinateG K :=
  coordinateU_le_coordinateB.trans coordinateB_le_coordinateG


theorem translation_mem_coordinateU (b : K) : translation K b ∈ coordinateU K :=
  Subgroup.subset_closure ⟨b, rfl⟩

theorem conj_mem_coordinateU {g u : Equiv.Perm (Omega K)} (hg : g ∈ coordinateB K)
    (hu : u ∈ coordinateU K) : g * u * g⁻¹ ∈ coordinateU K := by
  obtain ⟨s, c, -, hs⟩ := exists_affine_of_mem_coordinateB hg
  rw [coordinateU_eq_range] at hu
  obtain ⟨b, rfl⟩ := hu
  rw [translationHom, MonoidHom.coe_mk, OneHom.coe_mk,
    conj_translation_of_affine (mem_coordinateB_iff.mp hg).2 hs]
  exact translation_mem_coordinateU _

theorem coordinateU_normalizer :
    Subgroup.normalizer ((coordinateU K).subgroupOf (coordinateG K) : Set (coordinateG K)) =
      (coordinateB K).subgroupOf (coordinateG K) := by
  ext g
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hfix : (g : Equiv.Perm (Omega K)) none ∈ {x : Omega K | ∀ u ∈ coordinateU K, u x = x} := by
      intro u hu
      have hh : g⁻¹ * ⟨u, coordinateU_le_coordinateG hu⟩ * g ∈
          (coordinateU K).subgroupOf (coordinateG K) := by
        rw [hg]
        simpa [mul_assoc, Subgroup.mem_subgroupOf] using hu
      have h0 := (mem_coordinateB_iff.mp (coordinateU_le_coordinateB hh)).2
      change (g : Equiv.Perm (Omega K))⁻¹ (u ((g : Equiv.Perm (Omega K)) none)) = none at h0
      have h1 := congrArg (g : Equiv.Perm (Omega K)) h0
      rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h1
    rw [coordinateU_fixed_points] at hfix
    exact mem_coordinateB_iff.mpr ⟨g.2, hfix⟩
  · intro hg h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · exact conj_mem_coordinateU hg
    · intro hh
      have := conj_mem_coordinateU ((coordinateB K).inv_mem hg) hh
      simpa [mul_assoc] using this

section Sylow

variable [Finite K]

theorem card_coordinateG :
    Nat.card (coordinateG K) = (Nat.card K + 1) * Nat.card (coordinateB K) := by
  have hidx := MulAction.index_stabilizer (coordinateG K) (none : Omega K)
  have horbit : MulAction.orbit (coordinateG K) (none : Omega K) = Set.univ :=
    Set.eq_univ_of_forall fun x => MulAction.mem_orbit_iff.mpr (coordinateG_transitive K none x)
  rw [horbit, Set.ncard_univ, Finite.card_option] at hidx
  rw [← Subgroup.index_mul_card (MulAction.stabilizer (coordinateG K) (none : Omega K)), hidx,
    ← coordinateB_subgroupOf_eq_stabilizer,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe coordinateB_le_coordinateG).toEquiv]

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

omit hp in
theorem coordinateU_isPGroup : IsPGroup p ((coordinateU K).subgroupOf (coordinateG K)) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  apply IsPGroup.of_card (n := n)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe coordinateU_le_coordinateG).toEquiv,
    card_coordinateU, Nat.card_eq_fintype_card, hn]

omit hp in
theorem coordinateU_index :
    ((coordinateU K).subgroupOf (coordinateG K)).index =
      (Nat.card K + 1) * Nat.card (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  have h := Subgroup.index_mul_card ((coordinateU K).subgroupOf (coordinateG K))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe coordinateU_le_coordinateG).toEquiv,
    card_coordinateU, card_coordinateG, card_coordinateB] at h
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := K))
  rw [h]
  ring

theorem not_dvd_coordinateU_index : ¬ p ∣ ((coordinateU K).subgroupOf (coordinateG K)).index := by
  classical
  rw [coordinateU_index]
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K p
  have hpq : p ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self p n.ne_zero
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp.out).mp hdvd with h1 | h2
  · exact hp.out.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hpq).mp h1))
  · have hsq : Nat.card (powMonoidHom 2 : Kˣ →* Kˣ).range ∣ Nat.card K - 1 := by
      rw [Nat.card_eq_fintype_card (α := K), ← Fintype.card_units, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card _
    have h3 : p ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hpq (h2.trans hsq)
    rw [Nat.sub_sub_self hq1] at h3
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h3)

@[expose] noncomputable def coordinateUSylow (K : Type u) [Field K] [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] : Sylow p (coordinateG K) :=
  (coordinateU_isPGroup p).toSylow (not_dvd_coordinateU_index p)

theorem coe_coordinateUSylow :
    (coordinateUSylow K p : Subgroup (coordinateG K)) =
      (coordinateU K).subgroupOf (coordinateG K) :=
  rfl

@[expose] noncomputable def pointSylow (K : Type u) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (ω : Omega K) : Sylow p (coordinateG K) :=
  Classical.choose (coordinateG_transitive K none ω) • coordinateUSylow K p

theorem pointSylow_eq {ω : Omega K} {g : coordinateG K} (hg : (g : Equiv.Perm (Omega K)) none = ω) :
    pointSylow K p ω = g • coordinateUSylow K p := by
  have hg₀ := Classical.choose_spec (coordinateG_transitive K none ω)
  set g₀ := Classical.choose (coordinateG_transitive K none ω)
  have hmem : g⁻¹ * g₀ ∈
      Subgroup.normalizer
        ((coordinateUSylow K p : Subgroup (coordinateG K)) : Set (coordinateG K)) := by
    rw [coe_coordinateUSylow, coordinateU_normalizer, coordinateB_subgroupOf_eq_stabilizer,
      MulAction.mem_stabilizer_iff, mul_smul]
    change g⁻¹ • (g₀ : Equiv.Perm (Omega K)) none = none
    rw [hg₀, ← hg]
    exact inv_smul_smul g (none : Omega K)
  have h := Sylow.smul_eq_iff_mem_normalizer.mpr hmem
  calc pointSylow K p ω = g₀ • coordinateUSylow K p := rfl
    _ = (g * (g⁻¹ * g₀)) • coordinateUSylow K p := by rw [mul_inv_cancel_left]
    _ = g • coordinateUSylow K p := by rw [mul_smul, h]

theorem pointSylow_smul (h : coordinateG K) (ω : Omega K) :
    pointSylow K p ((h : Equiv.Perm (Omega K)) ω) = h • pointSylow K p ω := by
  obtain ⟨g, hg⟩ := coordinateG_transitive K none ω
  rw [pointSylow_eq p hg, pointSylow_eq p (g := h * g) (by simp [hg]), mul_smul]

theorem pointSylow_fixed (ω : Omega K) :
    {x : Omega K | ∀ u ∈ (pointSylow K p ω : Subgroup (coordinateG K)),
      (u : Equiv.Perm (Omega K)) x = x} = {ω} := by
  obtain ⟨g, rfl⟩ := coordinateG_transitive K none ω
  rw [pointSylow_eq p rfl]
  have hmem : ∀ u : coordinateG K,
      u ∈ (↑(g • coordinateUSylow K p) : Subgroup (coordinateG K)) ↔
      ((g⁻¹ * u * g : coordinateG K) : Equiv.Perm (Omega K)) ∈ coordinateU K := by
    intro u
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      coe_coordinateUSylow, Subgroup.mem_subgroupOf]
    simp [MulAut.inv_apply, mul_assoc]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hfix : (g : Equiv.Perm (Omega K))⁻¹ x ∈ {y : Omega K | ∀ v ∈ coordinateU K, v y = y} := by
      intro v hv
      have hv' : g * ⟨v, coordinateU_le_coordinateG hv⟩ * g⁻¹ ∈
          (↑(g • coordinateUSylow K p) : Subgroup (coordinateG K)) := by
        rw [hmem]
        simpa [mul_assoc] using hv
      have h1 := hx _ hv'
      change (g : Equiv.Perm (Omega K)) (v ((g : Equiv.Perm (Omega K))⁻¹ x)) = x at h1
      have h2 := congrArg (fun y => ((g : Equiv.Perm (Omega K))⁻¹ : Equiv.Perm (Omega K)) y) h1
      rwa [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h2
    rw [coordinateU_fixed_points, Set.mem_singleton_iff] at hfix
    rw [← hfix, Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  · rintro rfl u hu
    have h0 := (mem_coordinateB_iff.mp (coordinateU_le_coordinateB ((hmem u).mp hu))).2
    change (g : Equiv.Perm (Omega K))⁻¹ ((u : Equiv.Perm (Omega K))
      ((g : Equiv.Perm (Omega K)) none)) = none at h0
    have h1 := congrArg (g : Equiv.Perm (Omega K)) h0
    rwa [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at h1

theorem pointSylow_bijective : Function.Bijective (pointSylow K p) := by
  constructor
  · intro ω₁ ω₂ h
    have h1 := pointSylow_fixed (K := K) p ω₁
    rw [h, pointSylow_fixed] at h1
    exact (Set.singleton_eq_singleton_iff.mp h1).symm
  · intro Q
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (coordinateG K) (coordinateUSylow K p) Q
    exact ⟨(k : Equiv.Perm (Omega K)) none, by rw [pointSylow_eq p rfl, hk]⟩

end Sylow

theorem linear_two_point_Sylow_bijection (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [Finite K]
    [CharP K p] :
    ∃ P : Sylow p (coordinateG K),
      (P : Subgroup (coordinateG K)) = (coordinateU K).subgroupOf (coordinateG K) ∧
      ∃ β : Omega K → Sylow p (coordinateG K),
        (∀ (ω : Omega K) (g : coordinateG K), (g : Equiv.Perm (Omega K)) none = ω →
          β ω = g • P) ∧
        Function.Bijective β ∧
        (∀ (h : coordinateG K) (ω : Omega K), β ((h : Equiv.Perm (Omega K)) ω) = h • β ω) ∧
        (∀ ω : Omega K, {x : Omega K | ∀ u ∈ (β ω : Subgroup (coordinateG K)),
          (u : Equiv.Perm (Omega K)) x = x} = {ω}) ∧
        Subgroup.normalizer ((coordinateU K).subgroupOf (coordinateG K) : Set (coordinateG K)) =
          (coordinateB K).subgroupOf (coordinateG K) ∧
        (coordinateB K).subgroupOf (coordinateG K) =
          MulAction.stabilizer (coordinateG K) (none : Omega K) :=
  ⟨coordinateUSylow K p, coe_coordinateUSylow p, pointSylow K p, fun _ _ hg => pointSylow_eq p hg,
    pointSylow_bijective p, pointSylow_smul p, pointSylow_fixed p, coordinateU_normalizer,
    coordinateB_subgroupOf_eq_stabilizer⟩

theorem linear_two_semilinear_quotients (K : Type u) [Field K] [Finite K] :
    coordinateG K ≤ coordinateD K ∧ coordinateD K ≤ coordinateE K ∧
      ((coordinateG K).subgroupOf (coordinateE K)).Normal ∧
      ((coordinateD K).subgroupOf (coordinateE K)).Normal ∧
      (∀ a b : coordinateD K ⧸ (coordinateG K).subgroupOf (coordinateD K), a * b = b * a) ∧
      IsCyclic (coordinateE K ⧸ (coordinateD K).subgroupOf (coordinateE K)) ∧
      derivedSeries (coordinateE K ⧸ (coordinateG K).subgroupOf (coordinateE K)) 2 = ⊥ :=
  ⟨coordinateG_le_D K, coordinateD_le_E K, coordinateG_normal_in_E K, coordinateD_normal_in_E K,
    (coordinateDG_isMulCommutative K).is_comm.comm, coordinateED_isCyclic K,
    coordinateEG_secondDerived_eq_bot K⟩

end CFSG.LinearGroups
