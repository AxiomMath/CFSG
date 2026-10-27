module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.PhanDn
open CFSG.Timmesfeld.ClassicalOrders QuadraticMap
open scoped commutatorElement

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f m : ℕ}

section Plane

private def hpE : F × F := (1, 0)

private def hpF : F × F := (0, 1)

private theorem polar_hypPlane (p q : F × F) :
    polar (hypPlane F) p q = p.1 * q.2 + q.1 * p.2 := by
  simp only [polar, hypPlane_apply, Prod.fst_add, Prod.snd_add]
  ring

private theorem linearEquiv_ext_hypPlane {S T : (F × F) ≃ₗ[F] (F × F)}
    (he : S hpE = T hpE) (hf : S hpF = T hpF) : S = T := by
  refine LinearEquiv.ext fun x => ?_
  have hx : x = x.1 • hpE + x.2 • hpF := by
    refine Prod.ext ?_ ?_ <;> simp [hpE, hpF]
  rw [hx, map_add, map_add, map_smul, map_smul, map_smul, map_smul, he, hf]

private theorem isometry_polar {S : (F × F) ≃ₗ[F] (F × F)}
    (hS : ∀ x, hypPlane F (S x) = hypPlane F x) :
    ∀ x y, polar (hypPlane F) (S x) (S y) = polar (hypPlane F) x y := by
  intro x y
  simp only [polar, ← LinearEquiv.map_add, hS]

private theorem hypPlane_isometry_diag_or_anti {S : (F × F) ≃ₗ[F] (F × F)}
    (hS : ∀ x, hypPlane F (S x) = hypPlane F x) :
    (∃ a : F, a ≠ 0 ∧ S hpE = a • hpE ∧ S hpF = a⁻¹ • hpF) ∨
      (∃ a : F, a ≠ 0 ∧ S hpE = a • hpF ∧ S hpF = a⁻¹ • hpE) := by
  have hpolar := isometry_polar hS
  have hq1 : (S hpE).1 * (S hpE).2 = 0 := by
    have := hS hpE
    simpa [hypPlane_apply, hpE] using this
  have hq2 : (S hpF).1 * (S hpF).2 = 0 := by
    have := hS hpF
    simpa [hypPlane_apply, hpF] using this
  have hp1 : (S hpE).1 * (S hpF).2 + (S hpF).1 * (S hpE).2 = 1 := by
    have h := hpolar hpE hpF
    rw [polar_hypPlane, polar_hypPlane] at h
    simpa [hpE, hpF] using h
  have hne : S hpE ≠ 0 := by
    intro h0
    have h1 : hpE = 0 := S.injective (by rw [h0, map_zero])
    exact (one_ne_zero : (1 : F) ≠ 0) (by simpa [hpE] using congrArg Prod.fst h1)
  by_cases ht : (S hpE).2 = 0
  · have hs : (S hpE).1 ≠ 0 := by
      intro h0
      exact hne (Prod.ext h0 ht)
    refine Or.inl ⟨(S hpE).1, hs, ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · simp [hpE]
      · rw [ht]; simp [hpE]
    · have hv : (S hpF).2 = ((S hpE).1)⁻¹ := by
        rw [ht, mul_zero, add_zero] at hp1
        exact eq_inv_of_mul_eq_one_right hp1
      have hu : (S hpF).1 = 0 := by
        rcases mul_eq_zero.mp hq2 with h | h
        · exact h
        · rw [hv] at h
          exact absurd h (inv_ne_zero hs)
      refine Prod.ext ?_ ?_
      · rw [hu]; simp [hpF]
      · rw [hv]; simp [hpF]
  · have hs : (S hpE).1 = 0 := (mul_eq_zero.mp hq1).resolve_right ht
    refine Or.inr ⟨(S hpE).2, ht, ?_, ?_⟩
    · refine Prod.ext ?_ ?_
      · rw [hs]; simp [hpF]
      · simp [hpF]
    · have hu : (S hpF).1 = ((S hpE).2)⁻¹ := by
        rw [hs, zero_mul, zero_add] at hp1
        exact eq_inv_of_mul_eq_one_left hp1
      have hv : (S hpF).2 = 0 := by
        rcases mul_eq_zero.mp hq2 with h | h
        · rw [hu] at h
          exact absurd h (inv_ne_zero ht)
        · exact h
      refine Prod.ext ?_ ?_
      · rw [hu]; simp [hpE]
      · rw [hv]; simp [hpE]

private noncomputable def planeDiag (x : F) (hx : x ≠ 0) : (F × F) ≃ₗ[F] (F × F) where
  toFun p := (x * p.1, x⁻¹ * p.2)
  invFun p := (x⁻¹ * p.1, x * p.2)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · show x⁻¹ * (x * p.1) = p.1
      rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
    · show x * (x⁻¹ * p.2) = p.2
      rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · show x * (x⁻¹ * p.1) = p.1
      rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    · show x⁻¹ * (x * p.2) = p.2
      rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  map_add' p q := by
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, mul_add]
  map_smul' c p := by
    refine Prod.ext ?_ ?_
    · show x * (c * p.1) = c * (x * p.1)
      ring
    · show x⁻¹ * (c * p.2) = c * (x⁻¹ * p.2)
      ring

private theorem planeDiag_hpE (x : F) (hx : x ≠ 0) :
    planeDiag x hx hpE = x • hpE := by
  ext <;> simp [planeDiag, hpE]

private theorem planeDiag_hpF (x : F) (hx : x ≠ 0) :
    planeDiag x hx hpF = x⁻¹ • hpF := by
  ext <;> simp [planeDiag, hpF]

private noncomputable def pd (x : Fˣ) : (F × F) ≃ₗ[F] (F × F) :=
  planeDiag (x : F) x.ne_zero

private theorem pd_hpE (x : Fˣ) : pd x hpE = (x : F) • hpE :=
  planeDiag_hpE (x : F) x.ne_zero

private theorem pd_hpF (x : Fˣ) : pd x hpF = (x : F)⁻¹ • hpF :=
  planeDiag_hpF (x : F) x.ne_zero

private noncomputable def planeDiagHom : Fˣ →* ((F × F) ≃ₗ[F] (F × F)) where
  toFun x := pd x
  map_one' := by
    refine linearEquiv_ext_hypPlane ?_ ?_
    · rw [pd_hpE]
      simp
    · rw [pd_hpF]
      simp
  map_mul' x y := by
    refine linearEquiv_ext_hypPlane ?_ ?_
    · simp only [pd_hpE, LinearEquiv.mul_apply, Units.val_mul, map_smul, smul_smul]
      congr 1
      ring
    · simp only [pd_hpF, LinearEquiv.mul_apply, Units.val_mul, mul_inv_rev, map_smul, smul_smul]

private theorem eq_planeDiag_of_isometry {S : (F × F) ≃ₗ[F] (F × F)}
    (hS : ∀ x, hypPlane F (S x) = hypPlane F x) {a : F} (ha : a ≠ 0)
    (he : S hpE = a • hpE) : S = planeDiag a ha := by
  have hpolar := isometry_polar hS
  have hpol := hpolar hpE hpF
  rw [he, polar_hypPlane, polar_hypPlane] at hpol
  have h2 : a * (S hpF).2 = 1 := by
    simpa [hpE, hpF] using hpol
  have hsf2 : (S hpF).2 = a⁻¹ := eq_inv_of_mul_eq_one_right h2
  have hq : (S hpF).1 * (S hpF).2 = 0 := by
    have := hS hpF
    simpa [hypPlane_apply, hpF] using this
  have hsf1 : (S hpF).1 = 0 := by
    rcases mul_eq_zero.mp hq with h | h
    · exact h
    · rw [hsf2] at h
      exact absurd h (inv_ne_zero ha)
  refine linearEquiv_ext_hypPlane ?_ ?_
  · rw [he, planeDiag_hpE]
  · refine Prod.ext ?_ ?_
    · rw [hsf1]; simp [planeDiag, hpF]
    · rw [hsf2]; simp [planeDiag, hpF]

private theorem diag_inv_apply {S : (F × F) ≃ₗ[F] (F × F)} {a : F} (ha : a ≠ 0)
    (he : S hpE = a • hpE) (hf : S hpF = a⁻¹ • hpF) :
    S⁻¹ hpE = a⁻¹ • hpE ∧ S⁻¹ hpF = a • hpF := by
  constructor
  · show S.symm hpE = a⁻¹ • hpE
    refine S.injective ?_
    rw [LinearEquiv.apply_symm_apply, map_smul, he, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · show S.symm hpF = a • hpF
    refine S.injective ?_
    rw [LinearEquiv.apply_symm_apply, map_smul, hf, smul_smul, mul_inv_cancel₀ ha, one_smul]

private theorem anti_mul_self {S : (F × F) ≃ₗ[F] (F × F)} {a : F} (ha : a ≠ 0)
    (he : S hpE = a • hpF) (hf : S hpF = a⁻¹ • hpE) : S * S = 1 := by
  refine linearEquiv_ext_hypPlane ?_ ?_
  · rw [LinearEquiv.mul_apply, he, map_smul, hf, smul_smul, mul_inv_cancel₀ ha, one_smul]
    simp
  · rw [LinearEquiv.mul_apply, hf, map_smul, he, smul_smul, inv_mul_cancel₀ ha, one_smul]
    simp

private theorem anti_inv_apply {S : (F × F) ≃ₗ[F] (F × F)} {a : F} (ha : a ≠ 0)
    (he : S hpE = a • hpF) (hf : S hpF = a⁻¹ • hpE) :
    S⁻¹ hpE = a • hpF ∧ S⁻¹ hpF = a⁻¹ • hpE := by
  have hSS : S * S = 1 := anti_mul_self ha he hf
  have hinv : S⁻¹ = S := inv_eq_of_mul_eq_one_right hSS
  exact ⟨by rw [hinv, he], by rw [hinv, hf]⟩

private theorem isometry_inv {S : (F × F) ≃ₗ[F] (F × F)}
    (hS : ∀ x, hypPlane F (S x) = hypPlane F x) :
    ∀ x, hypPlane F (S⁻¹ x) = hypPlane F x := by
  intro x
  show hypPlane F (S.symm x) = hypPlane F x
  have h := hS (S.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

private theorem commutatorElement_isometry {S T : (F × F) ≃ₗ[F] (F × F)}
    (hS : ∀ x, hypPlane F (S x) = hypPlane F x)
    (hT : ∀ x, hypPlane F (T x) = hypPlane F x) :
    ∀ x, hypPlane F (⁅S, T⁆ x) = hypPlane F x := by
  intro x
  rw [commutatorElement_def]
  simp only [LinearEquiv.mul_apply]
  rw [hS, hT, isometry_inv hS, isometry_inv hT]

private theorem commutator_mem_planeDiag {S T : (F × F) ≃ₗ[F] (F × F)}
    (hS : ∀ x, hypPlane F (S x) = hypPlane F x)
    (hT : ∀ x, hypPlane F (T x) = hypPlane F x) :
    ⁅S, T⁆ ∈ planeDiagHom.range := by
  have hST : ∀ x, hypPlane F (⁅S, T⁆ x) = hypPlane F x := commutatorElement_isometry hS hT
  have hdef : ⁅S, T⁆ hpE = S (T (S⁻¹ (T⁻¹ hpE))) := by
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply]
  rcases hypPlane_isometry_diag_or_anti hS with ⟨a, ha, hSe, hSf⟩ | ⟨a, ha, hSe, hSf⟩
  · rcases hypPlane_isometry_diag_or_anti hT with ⟨b, hb, hTe, hTf⟩ | ⟨b, hb, hTe, hTf⟩
    ·
      have hTinv := (diag_inv_apply hb hTe hTf).1
      have hSinv := (diag_inv_apply ha hSe hSf).1
      have hE : ⁅S, T⁆ hpE = (1 : F) • hpE := by
        simp only [hdef, hTinv, hSinv, hTe, hSe, LinearEquiv.map_smul, smul_smul]
        congr 1
        field_simp
      refine ⟨1, ?_⟩
      rw [eq_planeDiag_of_isometry hST one_ne_zero hE]
      rfl
    ·
      have hTinv := (anti_inv_apply hb hTe hTf).1
      have hSinv := (diag_inv_apply ha hSe hSf).2
      have hE : ⁅S, T⁆ hpE = (a * a) • hpE := by
        simp only [hdef, hTinv, hSinv, hTf, hSe, LinearEquiv.map_smul, smul_smul]
        congr 1
        field_simp
      have haa : a * a ≠ 0 := mul_ne_zero ha ha
      refine ⟨Units.mk0 (a * a) haa, ?_⟩
      rw [eq_planeDiag_of_isometry hST haa hE]
      rfl
  · rcases hypPlane_isometry_diag_or_anti hT with ⟨b, hb, hTe, hTf⟩ | ⟨b, hb, hTe, hTf⟩
    ·
      have hTinv := (diag_inv_apply hb hTe hTf).1
      have hSinv := (anti_inv_apply ha hSe hSf).1
      have hE : ⁅S, T⁆ hpE = (b⁻¹ * b⁻¹) • hpE := by
        simp only [hdef, hTinv, hSinv, hTf, hSf, LinearEquiv.map_smul, smul_smul]
        congr 1
        field_simp
      have hbb : b⁻¹ * b⁻¹ ≠ 0 := mul_ne_zero (inv_ne_zero hb) (inv_ne_zero hb)
      refine ⟨Units.mk0 (b⁻¹ * b⁻¹) hbb, ?_⟩
      rw [eq_planeDiag_of_isometry hST hbb hE]
      rfl
    ·
      have hTinv := (anti_inv_apply hb hTe hTf).1
      have hSinv := (anti_inv_apply ha hSe hSf).2
      have hE : ⁅S, T⁆ hpE = ((b * a⁻¹) * (b * a⁻¹)) • hpE := by
        simp only [hdef, hTinv, hSinv, hTe, hSf, LinearEquiv.map_smul, smul_smul]
        congr 1
        field_simp
      have hba : (b * a⁻¹) * (b * a⁻¹) ≠ 0 := mul_ne_zero (mul_ne_zero hb (inv_ne_zero ha))
        (mul_ne_zero hb (inv_ne_zero ha))
      refine ⟨Units.mk0 ((b * a⁻¹) * (b * a⁻¹)) hba, ?_⟩
      rw [eq_planeDiag_of_isometry hST hba hE]
      rfl

private theorem eq_bot_of_commutator_eq_self_of_le_orthogonalGroup_hypPlane
    {H : Subgroup ((F × F) ≃ₗ[F] (F × F))}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (hypPlane F))
    (hperf : ⁅H, H⁆ = H) : H = ⊥ := by
  have hcomm : ⁅H, H⁆ ≤ planeDiagHom.range :=
    Subgroup.commutator_le.mpr fun x hx y hy =>
      commutator_mem_planeDiag (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hH hx))
        (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hH hy))
  have hHdiag : H ≤ planeDiagHom.range := by
    intro x hx
    rw [← hperf] at hx
    exact hcomm hx
  have hDcomm : ∀ x y : (F × F) ≃ₗ[F] (F × F),
      x ∈ (planeDiagHom (F := F)).range → y ∈ (planeDiagHom (F := F)).range → x * y = y * x := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hHcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x :=
    fun x hx y hy => hDcomm x y (hHdiag hx) (hHdiag hy)
  have hbot : ⁅H, H⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hHcomm y hy x hx
  rw [← hperf]
  exact hbot

end Plane

theorem le_range_uniEmb_of_commute_scalar (E : QuadExt F K (unitaryInvolution K 2 f))
    (hK : UnitaryFieldData 2 f K) {T : normOmega E m} {ω : K}
    (hω : ω ∉ Set.range (algebraMap F K))
    (hT : ∀ v : (F × F) × (Fin m → K),
      (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
        (v.1, fun i => ω * v.2 i))
    {P : Subgroup (normOmega E m)} (hP : P ≤ ⁅P, P⁆)
    (hPT : P ≤ Subgroup.centralizer ({T} : Set (normOmega E m))) :
    P ≤ (uniEmb E hK m).range := by
  intro p hp
  have hpC : p ∈ Subgroup.centralizer ({T} : Set (normOmega E m)) := hPT hp
  have hω0 : ω ≠ 0 := by
    intro h0
    exact hω (by rw [h0]; exact ⟨0, by simp⟩)
  have hω1 : ω ≠ 1 := by
    intro h1
    exact hω (by rw [h1]; exact ⟨1, by simp⟩)
  have hω1' : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  have hT' : ∀ v : (F × F) × (Fin m → K),
      (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
        (v.1, ω • v.2) := fun v => hT v
  have hdecomp : ∀ c : K, ∃ a b : F, c = algebraMap F K a + algebraMap F K b * ω := by
    have hli : LinearIndependent F ![algebraMap F K (1 : F), ω] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 : algebraMap F K s + algebraMap F K t * ω = 0 := by
        simpa only [Algebra.smul_def, map_one, mul_one] using hst
      have ht : t = 0 := by
        by_contra ht
        apply hω
        refine ⟨-s * t⁻¹, ?_⟩
        have ht' : algebraMap F K t ≠ 0 := fun h0 =>
          ht ((algebraMap F K).injective (by simpa using h0))
        have h2 : algebraMap F K t * ω = -algebraMap F K s := by
          linear_combination h1
        calc algebraMap F K (-s * t⁻¹) = algebraMap F K (-s) * algebraMap F K t⁻¹ := by
              rw [map_mul]
          _ = (-algebraMap F K s) * (algebraMap F K t)⁻¹ := by rw [map_neg, map_inv₀]
          _ = ω := by
              rw [← h2]
              field_simp [ht']
      refine ⟨?_, ht⟩
      have h1' : algebraMap F K s = 0 := by simpa [ht] using h1
      exact (algebraMap F K).injective (by simpa using h1')
    have hspan : Submodule.span F ({ω, algebraMap F K (1 : F)} : Set K) = ⊤ := by
      have h := LinearIndependent.span_eq_top_of_card_eq_finrank hli (by simp [E.finrank_eq])
      simpa using h
    intro c
    have hc : c ∈ Submodule.span F ({ω, algebraMap F K (1 : F)} : Set K) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hc
    refine ⟨b, a, ?_⟩
    rw [← hab]
    simp only [Algebra.smul_def, map_one, mul_one]
    ring
  have hconj : ∀ (g : normOmega E m),
      g ∈ Subgroup.centralizer ({T} : Set (normOmega E m)) →
      ∀ v : (F × F) × (Fin m → K),
        (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            ((T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v) =
          (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v) := by
    intro g hg v
    have h := Subgroup.mem_centralizer_iff.mp hg T (Set.mem_singleton T)
    have h' : (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
        (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) =
        (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
          (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) :=
      congrArg Subtype.val h
    rw [← LinearEquiv.mul_apply, ← h', LinearEquiv.mul_apply]
  have hpresW : ∀ (g : normOmega E m),
      g ∈ Subgroup.centralizer ({T} : Set (normOmega E m)) →
      ∀ v : (F × F) × (Fin m → K), v.2 = 0 →
        ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v).2 = 0 := by
    intro g hg v hv
    have hTv : (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v = v := by
      rw [hT']
      refine Prod.ext ?_ ?_
      · rfl
      · funext i
        simp [Pi.smul_apply, hv]
    have h1 : (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
        (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v) := by
      calc (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
          (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            ((T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v) := by
            rw [hTv]
        _ = (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v) :=
            hconj g hg v
    have h2 : ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v).2 =
        ω • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v).2 := by
      have h := congrArg Prod.snd h1
      rw [hT'] at h
      exact h
    have h3 : ((1 : K) - ω) •
        ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v).2 = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr h2
    have hne : ((1 : K) - ω) ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
    have := (smul_eq_zero.mp h3).resolve_left hne
    simpa using this
  have hpresU : ∀ (g : normOmega E m),
      g ∈ Subgroup.centralizer ({T} : Set (normOmega E m)) →
      ∀ x : Fin m → K,
        ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (((0, 0) : F × F), x)).1 = 0 := by
    intro g hg x
    have hTu : (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (((0, 0) : F × F), (ω - 1)⁻¹ • x) - (((0, 0) : F × F), (ω - 1)⁻¹ • x) =
        (((0, 0) : F × F), x) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sub, hT', sub_self]
        rfl
      · rw [Prod.snd_sub, hT']
        show ω • ((ω - 1)⁻¹ • x) - (ω - 1)⁻¹ • x = x
        rw [show ω • ((ω - 1)⁻¹ • x) - (ω - 1)⁻¹ • x =
          (ω - 1) • ((ω - 1)⁻¹ • x) by rw [sub_smul, one_smul]]
        rw [smul_smul, mul_inv_cancel₀ hω1', one_smul]
    have h1 : (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((0, 0) : F × F), x) =
        (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
              (((0, 0) : F × F), (ω - 1)⁻¹ • x)) -
          (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            (((0, 0) : F × F), (ω - 1)⁻¹ • x) := by
      rw [← hTu, map_sub, hconj g hg]
    rw [h1, Prod.fst_sub, hT']
    simp
  have hsmulK : ∀ (g : normOmega E m),
      g ∈ Subgroup.centralizer ({T} : Set (normOmega E m)) →
      ∀ (c : K) (x : Fin m → K),
        ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (((0, 0) : F × F), c • x)).2 =
          c • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
            (((0, 0) : F × F), x)).2 := by
    intro g hg c x
    obtain ⟨a, b, hab⟩ := hdecomp c
    have hcx : (((0, 0) : F × F), c • x) =
        a • (((0, 0) : F × F), x) + b • (((0, 0) : F × F), ω • x) := by
      refine Prod.ext ?_ ?_
      · simp
      · show c • x = a • x + b • (ω • x)
        rw [hab, add_smul, mul_smul, algebraMap_smul, algebraMap_smul]
    have hT0 : (T : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((0, 0) : F × F), x) = (((0, 0) : F × F), ω • x) := by
      rw [hT']
    have hωx : ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((0, 0) : F × F), ω • x)).2 =
        ω • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
          (((0, 0) : F × F), x)).2 := by
      have h := hconj g hg (((0, 0) : F × F), x)
      rw [hT0, hT'] at h
      simpa using congrArg Prod.snd h
    rw [hcx, map_add, map_smul, map_smul]
    change a • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((0, 0) : F × F), x)).2 +
      b • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((0, 0) : F × F), ω • x)).2 =
      c • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((0, 0) : F × F), x)).2
    rw [hωx]
    have h1 : a • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        (((0, 0) : F × F), x)).2 =
        (algebraMap F K a) • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (((0, 0) : F × F), x)).2 :=
      (algebraMap_smul K a _).symm
    have h2 : b • (ω • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (((0, 0) : F × F), x)).2) =
        ((algebraMap F K b) * ω) • ((g : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (((0, 0) : F × F), x)).2 := by
      rw [← smul_assoc]
      congr 1
      exact Algebra.smul_def b ω
    rw [h1, h2, ← add_smul, ← hab]
  have hOmegaO : ∀ g : normOmega E m,
      (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) ∈
        TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) :=
    fun g => Subgroup.commutator_le_self _ g.2
  let rWfun : Subgroup.centralizer ({T} : Set (normOmega E m)) →
      ((F × F) ≃ₗ[F] (F × F)) := fun g =>
    { toFun := fun w => ((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (w, 0)).1
      invFun := fun w => ((((g⁻¹).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K)))) (w, 0)).1
      left_inv := fun w => by
        have h0 : ((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) (w, 0)).2 = 0 := hpresW g.1 g.2 (w, 0) rfl
        have hv : (g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) (w, 0) =
            (((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
              ((F × F) × (Fin m → K))) (w, 0)).1, 0) := by
          refine Prod.ext rfl ?_
          rw [h0]
        show ((((g⁻¹).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K)))) (((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) (w, 0)).1, 0)).1 = w
        rw [← hv]
        simp
      right_inv := fun w => by
        have h0 : ((((g⁻¹).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K)))) (w, 0)).2 = 0 :=
          hpresW (g⁻¹).1 (inv_mem g.2) (w, 0) rfl
        have hv : (((g⁻¹).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K)))) (w, 0) =
            (((((g⁻¹).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
              ((F × F) × (Fin m → K)))) (w, 0)).1, 0) := by
          refine Prod.ext rfl ?_
          rw [h0]
        show (((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K)))) (((((g⁻¹).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K)))) (w, 0)).1, 0)).1 = w
        rw [← hv]
        simp
      map_add' := fun w1 w2 => by
        have h : (((w1 + w2 : F × F), (0 : Fin m → K)) :
            (F × F) × (Fin m → K)) = (w1, 0) + (w2, 0) := by
          ext <;> simp
        have h' : (g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) ((w1 + w2, 0) : (F × F) × (Fin m → K)) =
            (g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) (w1, 0) +
              (g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
                ((F × F) × (Fin m → K))) (w2, 0) := by
          rw [h, map_add]
        exact congrArg Prod.fst h'
      map_smul' := fun c w => by
        have h : ((c • w : F × F), (0 : Fin m → K)) =
            c • ((w, 0) : (F × F) × (Fin m → K)) := by
          ext <;> simp
        have h' : (g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) ((c • w : F × F), (0 : Fin m → K)) =
            c • (g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
              ((F × F) × (Fin m → K))) (w, 0) := by
          rw [h, map_smul]
        exact congrArg Prod.fst h' }
  let rW : Subgroup.centralizer ({T} : Set (normOmega E m)) →*
      ((F × F) ≃ₗ[F] (F × F)) :=
    { toFun := rWfun
      map_one' := by
        refine LinearEquiv.ext fun w => ?_
        show ((rWfun 1) w) = w
        show (((1 : Subgroup.centralizer ({T} : Set (normOmega E m))).1 :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) (w, 0)).1 = w
        simp
      map_mul' := fun g h => by
        refine LinearEquiv.ext fun w => ?_
        show ((rWfun (g * h)) w) = (rWfun g * rWfun h) w
        have hv : ((h.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) (w, 0)) =
            (((h.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
              ((F × F) × (Fin m → K))) (w, 0)).1, 0) := by
          refine Prod.ext rfl ?_
          rw [hpresW h.1 h.2 (w, 0) rfl]
        show (((g * h).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (w, 0)).1 = _
        rw [show ((g * h).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) =
            (g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
              (h.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
                ((F × F) × (Fin m → K))) from rfl,
          LinearEquiv.mul_apply, LinearEquiv.mul_apply, hv]
        rfl }
  have rW_apply : ∀ (g : Subgroup.centralizer ({T} : Set (normOmega E m))) (w : F × F),
      (rW g) w = ((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (w, 0)).1 := fun g w => rfl
  have rW_mem : ∀ g : Subgroup.centralizer ({T} : Set (normOmega E m)),
      rW g ∈ TauCeti.QuadraticMap.orthogonalGroup (hypPlane F) := by
    intro g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    have h0 : ((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (w, 0)).2 = 0 := hpresW g.1 g.2 (w, 0) rfl
    rw [rW_apply]
    calc hypPlane F ((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (w, 0)).1 =
        normHypForm E m ((g.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (w, 0)) := by
          simp [hypPlane_apply, hypSum_apply, h0]
      _ = normHypForm E m ((w, 0) : (F × F) × (Fin m → K)) :=
          map_of_mem (hOmegaO g.1) (w, 0)
      _ = hypPlane F w := by simp [hypPlane_apply, hypSum_apply]
  let φ : P →* ((F × F) ≃ₗ[F] (F × F)) := rW.comp (Subgroup.inclusion hPT)
  let H : Subgroup ((F × F) ≃ₗ[F] (F × F)) := φ.range
  have hHle : H ≤ TauCeti.QuadraticMap.orthogonalGroup (hypPlane F) := by
    rintro _ ⟨q, rfl⟩
    exact rW_mem (Subgroup.inclusion hPT q)
  have hPtop : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
    refine le_antisymm (Subgroup.commutator_le_self ⊤) ?_
    intro q _
    have hq : (q.1 : normOmega E m) ∈ ⁅P, P⁆ := hP q.2
    rw [← Subgroup.map_subtype_commutator P] at hq
    obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp hq
    have hyq' : y = q := Subtype.ext hyq
    rwa [hyq'] at hy
  have hHperf : ⁅H, H⁆ = H := by
    have h1 : H = (⊤ : Subgroup P).map φ := MonoidHom.range_eq_map φ
    have hle' : (⊤ : Subgroup P).map φ ≤
        ⁅(⊤ : Subgroup P).map φ, (⊤ : Subgroup P).map φ⁆ := by
      calc (⊤ : Subgroup P).map φ ≤ (⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆).map φ :=
            Subgroup.map_mono hPtop.symm.le
        _ = ⁅(⊤ : Subgroup P).map φ, (⊤ : Subgroup P).map φ⁆ :=
            Subgroup.map_commutator ⊤ ⊤ φ
    have hle : H ≤ ⁅H, H⁆ := by
      rw [h1]
      exact hle'
    exact le_antisymm (Subgroup.commutator_le_self H) hle
  have hHbot : H = ⊥ :=
    eq_bot_of_commutator_eq_self_of_le_orthogonalGroup_hypPlane hHle hHperf
  have hpWid : ∀ w : F × F,
      ((p : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) (w, 0)).1 = w := by
    intro w
    have hmem : φ ⟨p, hp⟩ ∈ H := MonoidHom.mem_range.mpr ⟨⟨p, hp⟩, rfl⟩
    rw [hHbot] at hmem
    have hphi : φ ⟨p, hp⟩ = 1 := by simpa using hmem
    have h := congrArg (fun e => e w) hphi
    simpa [φ, rW, rWfun] using h
  let Aqf : P → ((Fin m → K) →ₗ[K] (Fin m → K)) := fun q =>
    { toFun := fun x => ((q.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (((0, 0) : F × F), x)).2
      map_add' := by
        intro x y
        have h : (((0, 0) : F × F), x + y) = (((0, 0) : F × F), x) +
            (((0, 0) : F × F), y) := by ext <;> simp
        rw [h, map_add]
        rfl
      map_smul' := fun c x => hsmulK q.1 (hPT q.2) c x }
  have Aqf_inj : ∀ q : P, Function.Injective (Aqf q) := by
    intro q x y hxy
    have h0 : (q.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (((0, 0) : F × F), x) =
        (q.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (((0, 0) : F × F), y) := by
      refine Prod.ext ?_ ?_
      · rw [hpresU q.1 (hPT q.2) x, hpresU q.1 (hPT q.2) y]
      · exact hxy
    have := (q.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))).injective h0
    simpa using congrArg Prod.snd this
  let AqfE : P → ((Fin m → K) ≃ₗ[K] (Fin m → K)) := fun q =>
    LinearEquiv.ofInjectiveOfFinrankEq (Aqf q) (Aqf_inj q) (by simp)
  have AqfE_apply : ∀ (q : P) (x : Fin m → K), (AqfE q) x = (Aqf q) x := fun q x => rfl
  let AP : P →* ((Fin m → K) ≃ₗ[K] (Fin m → K)) :=
    { toFun := fun q => LinearEquiv.ofInjectiveOfFinrankEq (Aqf q) (Aqf_inj q) (by simp)
      map_one' := by
        refine LinearEquiv.ext fun x => ?_
        show (Aqf 1) x = x
        show (((1 : P).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (((0, 0) : F × F), x)).2 = x
        simp
      map_mul' := fun q r => by
        refine LinearEquiv.ext fun x => ?_
        show (Aqf (q * r)) x = (Aqf q) ((Aqf r) x)
        have hv : (r.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) (((0, 0) : F × F), x) =
            (((0, 0) : F × F), (Aqf r) x) := by
          refine Prod.ext (hpresU r.1 (hPT r.2) x) ?_
          rfl
        show (((q * r).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (((0, 0) : F × F), x)).2 = _
        rw [show ((q * r).1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
            ((F × F) × (Fin m → K))) =
            (q.1 : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
              (r.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
                ((F × F) × (Fin m → K))) from rfl,
          LinearEquiv.mul_apply, hv]
        rfl }
  have hAP_apply : ∀ (q : P) (x : Fin m → K),
      (AP q : (Fin m → K) → (Fin m → K)) x =
        ((q.1 : ((F × F) × (Fin m → K)) ≃ₗ[F]
          ((F × F) × (Fin m → K))) (((0, 0) : F × F), x)).2 := by
    intro q x
    rfl
  let AE : (Fin m → K) ≃ₗ[K] (Fin m → K) := AP ⟨p, hp⟩
  let AEF : (Fin m → K) ≃ₗ[F] (Fin m → K) := AE.restrictScalars F
  have hAEF : ∀ x : Fin m → K, AEF x = AE x := fun x => rfl
  have hQn : ∀ x : Fin m → K, Qn E m (AE x) = Qn E m x := by
    intro x
    have h := map_of_mem (hOmegaO p) (((0, 0) : F × F), x)
    have hpv : (p : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (((0, 0) : F × F), x) =
        (((0, 0) : F × F), AE x) := by
      refine Prod.ext (hpresU p hpC x) ?_
      rw [show AE x = (AP ⟨p, hp⟩) x from rfl, hAP_apply]
    rw [hpv] at h
    simpa [hypSum_apply] using h
  have hAEorth : AEF ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E m) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (fun x => by
      rw [hAEF]; exact hQn x)
  have hpolarQ : ∀ x y : Fin m → K,
      QuadraticMap.polar (Qn E m) (AE x) (AE y) = QuadraticMap.polar (Qn E m) x y := by
    intro x y
    have h := polar_map_of_mem hAEorth x y
    rwa [hAEF, hAEF] at h
  have hHf : ∀ u v : Fin m → K, (∑ i, u i * (unitaryInvolution K 2 f) (v i)) =
      CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) v u := by
    intro u v
    simp only [CFSG.ClassicalGroups.Unitary.herm, mul_comm]
  have hh : ∀ u v : Fin m → K,
      (algebraMap F K) (QuadraticMap.polar (Qn E m) u v) =
        CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) v u +
          (unitaryInvolution K 2 f) (CFSG.ClassicalGroups.Unitary.herm
            (unitaryInvolution K 2 f) v u) := by
    intro u v
    rw [CFSG.ClassicalInvolution.PhanDn.algebraMap_polar_Qn]
    congr 1
    · exact hHf u v
    · rw [hHf]
  have htrace : ∀ d : K, (∀ e : K, e * d + (unitaryInvolution K 2 f) (e * d) = 0) → d = 0 := by
    intro d hd
    have h1 : d + (unitaryInvolution K 2 f) d = 0 := by simpa using hd 1
    have hσd : (unitaryInvolution K 2 f) d = -d := eq_neg_of_add_eq_zero_right h1
    have hmain : ∀ e : K, (e - (unitaryInvolution K 2 f) e) * d = 0 := by
      intro e
      have he := hd e
      have hσed : (unitaryInvolution K 2 f) (e * d) =
          -((unitaryInvolution K 2 f) e * d) := by
        rw [map_mul, hσd]
        ring
      rw [hσed] at he
      have hsub : e * d - (unitaryInvolution K 2 f) e * d = 0 := by
        rwa [sub_eq_add_neg]
      rwa [← sub_mul] at hsub
    obtain ⟨c, hc⟩ := E.isUnitary.trace_surj 1 (map_one (unitaryInvolution K 2 f))
    have hc' : c - (unitaryInvolution K 2 f) c = 1 := by
      rw [sub_eq_add_neg, CharTwo.neg_eq, hc]
    have := hmain c
    rwa [hc', one_mul] at this
  have hherm : ∀ x y : Fin m → K,
      CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (AE x) (AE y) =
        CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) x y := by
    intro x y
    have hD0 : ∀ c : K,
        (CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (AE (c • y)) (AE x) -
          CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (c • y) x) +
        (unitaryInvolution K 2 f)
          (CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (AE (c • y)) (AE x) -
            CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (c • y) x) = 0 := by
      intro c
      have h1 := hh (AE x) (AE (c • y))
      have h2 := hh x (c • y)
      rw [hpolarQ x (c • y)] at h1
      have hEq : CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f)
            (AE (c • y)) (AE x) +
          (unitaryInvolution K 2 f) (CFSG.ClassicalGroups.Unitary.herm
            (unitaryInvolution K 2 f) (AE (c • y)) (AE x)) =
          CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (c • y) x +
            (unitaryInvolution K 2 f) (CFSG.ClassicalGroups.Unitary.herm
              (unitaryInvolution K 2 f) (c • y) x) := by
        rw [← h1, h2]
      rw [map_sub]
      linear_combination hEq
    have hD : ∀ e : K, e * (CFSG.ClassicalGroups.Unitary.herm
          (unitaryInvolution K 2 f) (AE y) (AE x) -
          CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) y x) +
        (unitaryInvolution K 2 f) (e * (CFSG.ClassicalGroups.Unitary.herm
          (unitaryInvolution K 2 f) (AE y) (AE x) -
          CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) y x)) = 0 := by
      intro e
      obtain ⟨c, rfl⟩ := (unitaryInvolution K 2 f).surjective e
      have h1 : CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f)
          (AE (c • y)) (AE x) =
          (unitaryInvolution K 2 f) c *
            CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (AE y) (AE x) := by
        rw [LinearEquiv.map_smul, CFSG.ClassicalGroups.Unitary.herm_smul_left]
      have h2 : CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (c • y) x =
          (unitaryInvolution K 2 f) c *
            CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) y x := by
        rw [CFSG.ClassicalGroups.Unitary.herm_smul_left]
      have hDc := hD0 c
      rw [h1, h2] at hDc
      rw [← mul_sub] at hDc
      exact hDc
    have hAB : CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (AE y) (AE x) =
        CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) y x :=
      sub_eq_zero.mp (htrace _ hD)
    have hconj := CFSG.ClassicalGroups.Unitary.herm_conj
      (unitaryInvolution K 2 f) E.isUnitary.invol (AE x) (AE y)
    calc CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (AE x) (AE y) =
        (unitaryInvolution K 2 f) (CFSG.ClassicalGroups.Unitary.herm
          (unitaryInvolution K 2 f) (AE y) (AE x)) := by
          rw [hconj, E.isUnitary.invol]
      _ = (unitaryInvolution K 2 f) (CFSG.ClassicalGroups.Unitary.herm
          (unitaryInvolution K 2 f) y x) := by rw [hAB]
      _ = CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) x y := by
          rw [CFSG.ClassicalGroups.Unitary.herm_conj (unitaryInvolution K 2 f)
            E.isUnitary.invol x y, E.isUnitary.invol]
  let detHom : P →* Kˣ := LinearEquiv.det.comp AP
  have hdetker : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ detHom.ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_commutatorElement,
      map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (mul_comm (LinearEquiv.det (AP a)) (LinearEquiv.det (AP b)))
  have hmemP : (⟨p, hp⟩ : P) ∈ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ := by
    rw [hPtop]; exact Subgroup.mem_top _
  have hdetAP : LinearEquiv.det AE = 1 := by
    have h := hdetker hmemP
    rw [MonoidHom.mem_ker] at h
    simpa [detHom] using h
  have hdetMap : LinearMap.det (AE : (Fin m → K) →ₗ[K] (Fin m → K)) = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hdetAP
    rw [LinearEquiv.coe_det] at h
    simpa using h
  let M : Matrix (Fin m) (Fin m) K :=
    LinearMap.toMatrix' (AE : (Fin m → K) →ₗ[K] (Fin m → K))
  have hMdet : M.det = 1 := by
    rw [show M = LinearMap.toMatrix' (AE : (Fin m → K) →ₗ[K] (Fin m → K)) from rfl,
      LinearMap.det_toMatrix', hdetMap]
  have hM : ∀ x : Fin m → K, M.mulVec x = AE x := fun x =>
    LinearMap.toMatrix'_mulVec (AE : (Fin m → K) →ₗ[K] (Fin m → K)) x
  have hhiso : ∀ x y : Fin m → K,
      CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) (M.mulVec x) (M.mulVec y) =
        CFSG.ClassicalGroups.Unitary.herm (unitaryInvolution K 2 f) x y := by
    intro x y
    rw [hM, hM]
    exact hherm x y
  let s : CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution K 2 f) m :=
    CFSG.ClassicalGroups.Unitary.mkSU (unitaryInvolution K 2 f) M hMdet hhiso
  have hp_apply : ∀ v : (F × F) × (Fin m → K),
      (p : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v =
        (v.1, AE v.2) := by
    intro v
    have hv : v = (v.1, (0 : Fin m → K)) + (((0, 0) : F × F), v.2) := by
      ext <;> simp
    rw [hv, map_add]
    have h1 : (p : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (v.1, (0 : Fin m → K)) = (v.1, 0) := by
      refine Prod.ext (hpWid v.1) ?_
      exact hpresW p hpC (v.1, 0) rfl
    have h2 : (p : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (((0, 0) : F × F), v.2) =
        (((0, 0) : F × F), AE v.2) := by
      refine Prod.ext (hpresU p hpC v.2) ?_
      exact (hAP_apply ⟨p, hp⟩ v.2).symm
    rw [h1, h2]
    simp
  have hs : suEmb E m s = p := by
    refine Subtype.ext ?_
    refine LinearEquiv.ext fun v => ?_
    rw [suEmb_apply]
    show (v.1, s • v.2) = (p : ((F × F) × (Fin m → K)) ≃ₗ[F]
      ((F × F) × (Fin m → K))) v
    rw [hp_apply]
    congr 1
    rw [CFSG.ClassicalGroups.Unitary.mkSU_smul]
    exact hM v.2
  refine ⟨(suEquiv hK m) s, ?_⟩
  simp only [uniEmb, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  exact hs

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
