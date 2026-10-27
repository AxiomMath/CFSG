module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionSplit
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {p f : ℕ} {E : Type} [Field E] {V : Type*} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

theorem finrank_le_of_pairing [FiniteDimensional E V] {W₁ W₂ : Submodule E V}
    (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0) : finrank E W₂ ≤ finrank E W₁ := by
  have := h.finite
  have hinj : Function.Injective fun w : W₂ => (B (w : V)).comp W₁.subtype := by
    intro w w' hww'
    have h1 : ∀ v ∈ W₁, B ((w : V) - w') v = 0 := fun v hv => by
      have := congrArg (fun φ : W₁ →ₗ[E] E => φ ⟨v, hv⟩) hww'
      simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
      rw [map_sub, LinearMap.sub_apply, this, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hpair _ (sub_mem w.2 w'.2) h1))
  have : Finite (W₁ →ₗ[E] E) := Module.finite_of_finite E
  have : Finite W₂ := Module.finite_of_finite E
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Module.natCard_eq_pow_finrank (K := E) (V := W₂),
    Module.natCard_eq_pow_finrank (K := E) (V := W₁ →ₗ[E] E)] at hcard
  have hdual : finrank E (W₁ →ₗ[E] E) = finrank E W₁ := Subspace.dual_finrank_eq
  rw [hdual] at hcard
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp hcard

theorem exists_dual_action [FiniteDimensional E V] (hB : B.IsSymm) {W₁ W₂ : Submodule E V}
    (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0) (hdim : finrank E W₂ = finrank E W₁)
    (gp : LinearMap.GeneralLinearGroup E W₁) :
    ∃ gn : LinearMap.GeneralLinearGroup E W₂, ∀ (x : W₁) (y : W₂),
      B (((gp : Module.End E W₁) x : W₁) : V) (((gn : Module.End E W₂) y : W₂) : V) =
        B (x : V) (y : V) := by
  have := h.finite
  have : Finite W₂ := Module.finite_of_finite E
  have : Finite (W₁ →ₗ[E] E) := Module.finite_of_finite E
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W₂ → (W₁ →ₗ[E] E), Ψ = fun w : W₂ => (B (w : V)).comp W₁.subtype :=
    ⟨_, rfl⟩
  have hΨapp : ∀ (w : W₂) (v : W₁), Ψ w v = B (w : V) (v : V) := fun w v => by rw [hΨ]; rfl
  have hinj : Function.Injective Ψ := by
    intro w w' hww'
    have h1 : ∀ v ∈ W₁, B ((w : V) - w') v = 0 := fun v hv => by
      have := congrArg (fun φ : W₁ →ₗ[E] E => φ ⟨v, hv⟩) hww'
      simp only [hΨapp] at this
      rw [map_sub, LinearMap.sub_apply, this, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hpair _ (sub_mem w.2 w'.2) h1))
  have hcard : Nat.card W₂ = Nat.card (W₁ →ₗ[E] E) := by
    rw [Module.natCard_eq_pow_finrank (K := E) (V := W₂),
      Module.natCard_eq_pow_finrank (K := E) (V := W₁ →ₗ[E] E), Subspace.dual_finrank_eq,
      hdim]
  have hbij : Function.Bijective Ψ := (Nat.bijective_iff_injective_and_card Ψ).mpr ⟨hinj, hcard⟩
  obtain ⟨e, he⟩ : ∃ e : W₂ ≃ (W₁ →ₗ[E] E), e = Equiv.ofBijective Ψ hbij := ⟨_, rfl⟩
  have heΨ : ∀ w, e w = Ψ w := fun w => by rw [he, Equiv.ofBijective_apply]
  obtain ⟨θ, hθ⟩ : ∃ θ : W₂ → (W₁ →ₗ[E] E), θ = fun y : W₂ =>
      (B (y : V)).comp (W₁.subtype ∘ₗ ((gp⁻¹ : LinearMap.GeneralLinearGroup E W₁) :
        Module.End E W₁)) := ⟨_, rfl⟩
  have hθapp : ∀ (y : W₂) (v : W₁), θ y v =
      B (y : V) ((((gp⁻¹ : LinearMap.GeneralLinearGroup E W₁) : Module.End E W₁) v : W₁) : V) :=
    fun y v => by rw [hθ]; rfl
  have hspec : ∀ (y : W₂) (v : W₁), B ((e.symm (θ y) : W₂) : V) (v : V) = θ y v :=
    fun y v => by
    rw [← hΨapp, ← heΨ, Equiv.apply_symm_apply]
  have hadd : ∀ y y' : W₂, e.symm (θ (y + y')) = e.symm (θ y) + e.symm (θ y') :=
    fun y y' => by
    apply e.injective
    rw [Equiv.apply_symm_apply, heΨ]
    refine LinearMap.ext fun v => ?_
    rw [hΨapp, Submodule.coe_add, map_add, LinearMap.add_apply, ← hΨapp, ← hΨapp, ← heΨ, ← heΨ,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, hθapp, hθapp, hθapp, Submodule.coe_add,
      map_add, LinearMap.add_apply]
  have hsmul : ∀ (c : E) (y : W₂), e.symm (θ (c • y)) = c • e.symm (θ y) := fun c y => by
    apply e.injective
    rw [Equiv.apply_symm_apply, heΨ]
    refine LinearMap.ext fun v => ?_
    rw [hΨapp, Submodule.coe_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, ← hΨapp, ← heΨ,
      Equiv.apply_symm_apply, hθapp, hθapp, Submodule.coe_smul, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply]
  obtain ⟨gmap, hgmap⟩ : ∃ gmap : Module.End E W₂, ∀ y, gmap y = e.symm (θ y) :=
    ⟨{ toFun := fun y => e.symm (θ y), map_add' := hadd, map_smul' := hsmul }, fun _ => rfl⟩
  have hgmapinj : Function.Injective gmap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hgmap] at hy
    have h1 : θ y = 0 := by
      have := congrArg e hy
      rw [Equiv.apply_symm_apply, heΨ] at this
      rw [this]
      refine LinearMap.ext fun v => ?_
      rw [hΨapp, Submodule.coe_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
    refine Subtype.ext (hpair _ y.2 fun v hv => ?_)
    have h2 := congrArg (fun φ : W₁ →ₗ[E] E => φ
      (((gp : LinearMap.GeneralLinearGroup E W₁) : Module.End E W₁) ⟨v, hv⟩)) h1
    simp only [hθapp, LinearMap.zero_apply] at h2
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply] at h2
    exact h2
  obtain ⟨gmapE, hgmapE⟩ := (⟨LinearEquiv.ofInjectiveEndo gmap hgmapinj, rfl⟩ :
    ∃ x : W₂ ≃ₗ[E] W₂, x = LinearEquiv.ofInjectiveEndo gmap hgmapinj)
  refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv E W₂).symm gmapE, fun x y => ?_⟩
  have hy : (((LinearMap.GeneralLinearGroup.generalLinearEquiv E W₂).symm gmapE :
      LinearMap.GeneralLinearGroup E W₂) : Module.End E W₂) y = gmap y := by
    rw [hgmapE]
    rfl
  rw [hy, hgmap, ← hB.eq, hspec, hθapp, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Module.End.one_apply, hB.eq]

theorem exists_paired_centralizer_equiv (hp : p ≠ 2) [FiniteDimensional E V] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B} {l : E} (hl0 : l ≠ 0)
    (hAA : ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
      ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) = (l ^ 2) • 1)
    (hN : h.norm l = -1) :
    (∀ v ∈ eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
      ∀ w ∈ eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
        B v w = 0) ∧
    (∀ v ∈ eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
      ∀ w ∈ eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
        B v w = 0) ∧
    finrank E (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)) =
      finrank E (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)) ∧
    2 * finrank E (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)) =
      finrank E V ∧
    (∀ v ∈ eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
      (∀ w ∈ eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
        B v w = 0) → v = 0) ∧
    (∀ w ∈ eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
      (∀ v ∈ eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
        B v w = 0) → w = 0) ∧
    ∃ e : Subgroup.centralizer {A} ≃* LinearMap.GeneralLinearGroup E
        (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)),
      (∀ g : Subgroup.centralizer {A},
        (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)).subtype ∘ₗ
            ((e g : LinearMap.GeneralLinearGroup E
              (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) :
                Module.End E
                  (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) =
          (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) ∘ₗ
            (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)).subtype) ∧
      (∀ (g : Subgroup.centralizer {A}) (w : V),
        w ∈ eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) →
        ∀ w' ∈ eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
          ((∀ v ∈ eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
            B ((((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) :
              Module.End E V) v) w' = B v w) ↔
            w' = (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) :
              Module.End E V) w)) ∧
      (∀ g : Subgroup.centralizer {A}, (g : sesqUnitaryGroup B) ∈ sesqNormOneScalars h B ↔
        ∃ c : E, h.norm c = 1 ∧ ((e g : LinearMap.GeneralLinearGroup E
          (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) :
            Module.End E
              (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) =
            c • 1) := by
  obtain ⟨A', hA'⟩ : ∃ A' : Module.End E V,
      A' = ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) := ⟨_, rfl⟩
  rw [← hA'] at hAA ⊢
  have h2 := two_ne_zero_of_odd h hp
  have hc : IsCompl (eigenPlus l A') (eigenMinus l A') :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA)
  have hTB : ∀ v w, B (invSMulOp l A' v) (invSMulOp l A' w) = -B v w := fun v w => by
    rw [hA', sesq_invSMulOp, hN, inv_neg, inv_one, neg_one_mul]
  have hisoP : ∀ v ∈ eigenPlus l A', ∀ w ∈ eigenPlus l A', B v w = 0 :=
    fun v hv w hw => sesq_eq_zero_of_eigen_neg_plus h2 hTB hv hw
  have hisoM : ∀ v ∈ eigenMinus l A', ∀ w ∈ eigenMinus l A', B v w = 0 :=
    fun v hv w hw => sesq_eq_zero_of_eigen_neg_minus h2 hTB hv hw
  have hpairPM : ∀ v ∈ eigenPlus l A', (∀ w ∈ eigenMinus l A', B v w = 0) → v = 0 := by
    intro v hv h0
    refine hBl v fun w => ?_
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
    rw [map_add, hisoP v hv x hx, h0 y hy, add_zero]
  have hpairMP : ∀ w ∈ eigenMinus l A', (∀ v ∈ eigenPlus l A', B w v = 0) → w = 0 := by
    intro w hw h0
    refine hBl w fun v => ?_
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
    rw [map_add, h0 x hx, hisoM w hw y hy, add_zero]
  have hpairMP' : ∀ w ∈ eigenMinus l A', (∀ v ∈ eigenPlus l A', B v w = 0) → w = 0 :=
    fun w hw h0 => hpairMP w hw fun v hv => by rw [← hB.eq v w, h0 v hv, map_zero]
  have hdim : finrank E (eigenPlus l A') = finrank E (eigenMinus l A') :=
    le_antisymm (finrank_le_of_pairing (h := h) hpairPM) (finrank_le_of_pairing (h := h) hpairMP)
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hWp : ∀ g ∈ Subgroup.centralizer {A}, ∀ v ∈ eigenPlus l A',
      (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈
        eigenPlus l A' := fun g hg v hv => by
    rw [hA'] at hv ⊢
    exact mapsTo_ker_sub_one_of_mem_centralizer l hg hv
  have hWm : ∀ g ∈ Subgroup.centralizer {A}, ∀ v ∈ eigenMinus l A',
      (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈
        eigenMinus l A' := fun g hg v hv => by
    rw [hA'] at hv ⊢
    exact mapsTo_ker_add_one_of_mem_centralizer l hg hv
  obtain ⟨φ, hφ⟩ : ∃ φ : Subgroup.centralizer {A} →* LinearMap.GeneralLinearGroup E
      (eigenPlus l A'), φ = glRestrictHom _ hWp := ⟨_, rfl⟩
  have hφapp : ∀ (g : Subgroup.centralizer {A}) (v : eigenPlus l A'),
      (((φ g : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
        Module.End E (eigenPlus l A')) v : V) =
        (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) v :=
    fun g v => by rw [hφ]; rfl
  have hscal : ∀ (g : Subgroup.centralizer {A}) (c : E), h.norm c = 1 →
      (∀ v ∈ eigenPlus l A', (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) :
        Module.End E V) v = c • v) →
      ∀ w, (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) :
        Module.End E V) w = c • w := by
    intro g c hcN hg w
    have hc0 := ne_zero_of_norm_eq_one h hcN
    have hbc : h.bar c * c = 1 := by rw [mul_comm]; exact hcN
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
    rw [map_add, hg x hx, smul_add]
    congr 1
    have hgy := hWm g g.2 y hy
    refine sub_eq_zero.mp (hpairMP' _ (sub_mem hgy (Submodule.smul_mem _ c hy)) fun v hv => ?_)
    have h1 := (g : sesqUnitaryGroup B).2 v y
    rw [hg v hv, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [map_sub, map_smul, smul_eq_mul]
    linear_combination c * h1 - (B v ((((g : sesqUnitaryGroup B) :
      LinearMap.GeneralLinearGroup E V) : Module.End E V) y)) * hbc
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).mpr fun g hg => ?_
    have hg1 : ∀ v ∈ eigenPlus l A', (((g : sesqUnitaryGroup B) :
        LinearMap.GeneralLinearGroup E V) : Module.End E V) v = (1 : E) • v := fun v hv => by
      rw [one_smul, ← hφapp g ⟨v, hv⟩, hg]
      rfl
    have h1 := hscal g 1 (by rw [UnitaryFieldData.norm, map_one, one_mul]) hg1
    exact Subtype.ext (Subtype.ext (Units.ext (LinearMap.ext fun w => by
      rw [h1, one_smul]
      rfl)))
  have hsurj : Function.Surjective φ := by
    intro gp
    obtain ⟨gn, hgn⟩ := exists_dual_action (h := h) hB hpairMP hdim.symm gp
    obtain ⟨G, hG⟩ : ∃ G : LinearMap.GeneralLinearGroup E V, G = glOfIsCompl hc gp gn :=
      ⟨_, rfl⟩
    have hGl : ∀ x (hx : x ∈ eigenPlus l A'), (G : Module.End E V) x =
        (((gp : Module.End E (eigenPlus l A')) ⟨x, hx⟩ : eigenPlus l A') : V) :=
      fun x hx => by rw [hG]; exact glOfIsCompl_apply_left hc _ _ ⟨x, hx⟩
    have hGr : ∀ x (hx : x ∈ eigenMinus l A'), (G : Module.End E V) x =
        (((gn : Module.End E (eigenMinus l A')) ⟨x, hx⟩ : eigenMinus l A') : V) :=
      fun x hx => by rw [hG]; exact glOfIsCompl_apply_right hc _ _ ⟨x, hx⟩
    have hGU : G ∈ sesqUnitaryGroup B := by
      intro v w
      obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
      obtain ⟨x', y', hx', hy', rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
      have i1 := hgn ⟨x, hx⟩ ⟨y', hy'⟩
      have i2 := hgn ⟨x', hx'⟩ ⟨y, hy⟩
      simp only [map_add, LinearMap.add_apply]
      rw [hGl x hx, hGr y hy, hGl x' hx', hGr y' hy',
        hisoP _ ((gp : Module.End E (eigenPlus l A')) ⟨x, hx⟩).2 _
          ((gp : Module.End E (eigenPlus l A')) ⟨x', hx'⟩).2,
        hisoM _ ((gn : Module.End E (eigenMinus l A')) ⟨y, hy⟩).2 _
          ((gn : Module.End E (eigenMinus l A')) ⟨y', hy'⟩).2,
        hisoP x hx x' hx', hisoM y hy y' hy', i1, ← hB.eq, i2, hB.eq]
    have hGC : (⟨G, hGU⟩ : sesqUnitaryGroup B) ∈ Subgroup.centralizer {A} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine Subtype.ext (Units.ext ?_)
      change (G : Module.End E V) * ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) =
        ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) * (G : Module.End E V)
      rw [← hA']
      refine commute_of_mapsTo_eigen h2 hl0 hAA (fun v hv => ?_) (fun v hv => ?_)
      · rw [hGl v hv]
        exact ((gp : Module.End E (eigenPlus l A')) ⟨v, hv⟩).2
      · rw [hGr v hv]
        exact ((gn : Module.End E (eigenMinus l A')) ⟨v, hv⟩).2
    refine ⟨⟨⟨G, hGU⟩, hGC⟩, Units.ext (LinearMap.ext fun x => Subtype.ext ?_)⟩
    rw [hφapp]
    exact hGl x x.2
  refine ⟨hisoP, hisoM, hdim, by omega, hpairPM, hpairMP',
    MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun g => LinearMap.ext fun v => hφapp g v,
    fun g w hw w' hw' => ⟨fun H => ?_, ?_⟩, fun g => ⟨?_, ?_⟩⟩
  ·
    have hgw := hWm g g.2 w hw
    refine sub_eq_zero.mp (hpairMP' _ (sub_mem hw' hgw) fun z hz => ?_)
    obtain ⟨u, hu⟩ : ∃ u : V, u = (((((g⁻¹ : Subgroup.centralizer {A}) : sesqUnitaryGroup B) :
        LinearMap.GeneralLinearGroup E V) : Module.End E V) z) := ⟨_, rfl⟩
    have hu' : u ∈ eigenPlus l A' := by
      rw [hu]
      exact hWp _ (inv_mem g.2) z hz
    have hzz : (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) :
        Module.End E V) u = z := by
      rw [hu]
      change ((((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) *
        ((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V)⁻¹ :
          LinearMap.GeneralLinearGroup E V) : Module.End E V) z = z
      rw [mul_inv_cancel]
      rfl
    rw [← hzz, map_sub, H u hu', (g : sesqUnitaryGroup B).2, sub_self]
  · rintro rfl v _
    exact (g : sesqUnitaryGroup B).2 v w
  · rintro ⟨c, hcN, hgc⟩
    refine ⟨c, hcN, LinearMap.ext fun v => Subtype.ext ?_⟩
    change (((φ g : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
      Module.End E (eigenPlus l A')) v : V) = _
    rw [hφapp, hgc]
    rfl
  · rintro ⟨c, hcN, hgc⟩
    have hgv : ∀ v ∈ eigenPlus l A', (((g : sesqUnitaryGroup B) :
        LinearMap.GeneralLinearGroup E V) : Module.End E V) v = c • v := fun v hv => by
      rw [← hφapp g ⟨v, hv⟩]
      rw [show ((φ g : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
        Module.End E (eigenPlus l A')) = c • 1 from hgc]
      rfl
    exact ⟨c, hcN, LinearMap.ext fun w => hscal g c hcN hgv w⟩

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
