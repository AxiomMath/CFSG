module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {E : Type} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

section GLHelpers

@[expose] def glRestrict (W : Submodule E V) (g : LinearMap.GeneralLinearGroup E V)
    (hg : ∀ v ∈ W, (g : Module.End E V) v ∈ W)
    (hg' : ∀ v ∈ W, ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈ W) :
    LinearMap.GeneralLinearGroup E W where
  val := (g : Module.End E V).restrict hg
  inv := ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : Module.End E V).restrict hg'
  val_inv := LinearMap.ext fun v => Subtype.ext (by
    change (g : Module.End E V) (((g⁻¹ : LinearMap.GeneralLinearGroup E V) :
      Module.End E V) v) = v
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply])
  inv_val := LinearMap.ext fun v => Subtype.ext (by
    change ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : Module.End E V)
      ((g : Module.End E V) v) = v
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply])

theorem coe_glRestrict_apply (W : Submodule E V) (g : LinearMap.GeneralLinearGroup E V)
    (hg : ∀ v ∈ W, (g : Module.End E V) v ∈ W)
    (hg' : ∀ v ∈ W, ((g⁻¹ : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈ W)
    (v : W) :
    (((glRestrict W g hg hg' : LinearMap.GeneralLinearGroup E W) : Module.End E W) v : V) =
      (g : Module.End E V) v :=
  rfl

variable {W₁ W₂ : Submodule E V} (hc : IsCompl W₁ W₂)

@[expose] noncomputable def glOfIsCompl (g₁ : LinearMap.GeneralLinearGroup E W₁)
    (g₂ : LinearMap.GeneralLinearGroup E W₂) : LinearMap.GeneralLinearGroup E V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv E V).symm
    ((Submodule.prodEquivOfIsCompl W₁ W₂ hc).symm.trans
      (((LinearMap.GeneralLinearGroup.generalLinearEquiv E W₁ g₁).prodCongr
        (LinearMap.GeneralLinearGroup.generalLinearEquiv E W₂ g₂)).trans
        (Submodule.prodEquivOfIsCompl W₁ W₂ hc)))

theorem glOfIsCompl_apply_left (g₁ : LinearMap.GeneralLinearGroup E W₁)
    (g₂ : LinearMap.GeneralLinearGroup E W₂) (x : W₁) :
    ((glOfIsCompl hc g₁ g₂ : LinearMap.GeneralLinearGroup E V) : Module.End E V) x =
      ((g₁ : Module.End E W₁) x : V) := by
  simp [glOfIsCompl, LinearMap.GeneralLinearGroup.generalLinearEquiv]

theorem glOfIsCompl_apply_right (g₁ : LinearMap.GeneralLinearGroup E W₁)
    (g₂ : LinearMap.GeneralLinearGroup E W₂) (x : W₂) :
    ((glOfIsCompl hc g₁ g₂ : LinearMap.GeneralLinearGroup E V) : Module.End E V) x =
      ((g₂ : Module.End E W₂) x : V) := by
  simp [glOfIsCompl, LinearMap.GeneralLinearGroup.generalLinearEquiv]

include hc in
theorem endo_ext_of_isCompl {g g' : Module.End E V} (h₁ : ∀ x ∈ W₁, g x = g' x)
    (h₂ : ∀ x ∈ W₂, g x = g' x) : g = g' := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
  rw [map_add, map_add, h₁ x hx, h₂ y hy]

end GLHelpers

section Restrict

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

@[expose] noncomputable def glRestrictHom {C : Subgroup (sesqUnitaryGroup B)} (W : Submodule E V)
    (hW : ∀ g ∈ C, ∀ v ∈ W,
      (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈ W) :
    C →* LinearMap.GeneralLinearGroup E W where
  toFun g := glRestrict W ((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V)
    (hW g g.2) (hW _ (inv_mem g.2))
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := Units.ext (LinearMap.ext fun _ => rfl)

theorem coe_glRestrictHom_apply {C : Subgroup (sesqUnitaryGroup B)} (W : Submodule E V)
    (hW : ∀ g ∈ C, ∀ v ∈ W,
      (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈ W)
    (g : C) (v : W) :
    ((((glRestrictHom W hW g : LinearMap.GeneralLinearGroup E W) : Module.End E W) v : W) : V) =
      (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) v :=
  rfl

theorem glRestrictHom_mem {C : Subgroup (sesqUnitaryGroup B)} (W : Submodule E V)
    (hW : ∀ g ∈ C, ∀ v ∈ W,
      (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈ W)
    (g : C) : glRestrictHom W hW g ∈ sesqUnitaryGroup (B.domRestrict₁₂ W W) :=
  fun x y => (g : sesqUnitaryGroup B).2 x y

@[expose] noncomputable def unitaryRestrictHom {C : Subgroup (sesqUnitaryGroup B)}
    (W : Submodule E V)
    (hW : ∀ g ∈ C, ∀ v ∈ W,
      (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈ W) :
    C →* sesqUnitaryGroup (B.domRestrict₁₂ W W) :=
  (glRestrictHom W hW).codRestrict _ (glRestrictHom_mem W hW)

theorem commute_of_mem_centralizer {A g : sesqUnitaryGroup B}
    (hg : g ∈ Subgroup.centralizer {A}) :
    ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
        ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) =
      ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
        ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) :=
  congrArg (fun x : sesqUnitaryGroup B => ((x : LinearMap.GeneralLinearGroup E V) :
    Module.End E V)) (Subgroup.mem_centralizer_singleton_iff.mp hg)

theorem mapsTo_ker_sub_one_of_mem_centralizer {A g : sesqUnitaryGroup B} (l : E)
    (hg : g ∈ Subgroup.centralizer {A}) {v : V}
    (hv : v ∈ LinearMap.ker (invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) :
      Module.End E V) - 1)) :
    ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈
      LinearMap.ker (invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) :
        Module.End E V) - 1) := by
  have e : invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) - 1 =
      invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) -
        (1 : E) • (1 : Module.End E V) := by rw [one_smul]
  rw [e] at hv ⊢
  exact mapsTo_eigen_of_commute (commute_of_mem_centralizer hg) hv

theorem mapsTo_ker_add_one_of_mem_centralizer {A g : sesqUnitaryGroup B} (l : E)
    (hg : g ∈ Subgroup.centralizer {A}) {v : V}
    (hv : v ∈ LinearMap.ker (invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) :
      Module.End E V) + 1)) :
    ((g : LinearMap.GeneralLinearGroup E V) : Module.End E V) v ∈
      LinearMap.ker (invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) :
        Module.End E V) + 1) := by
  have e : invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) + 1 =
      invSMulOp l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) -
        (-1 : E) • (1 : Module.End E V) := by rw [neg_smul, one_smul, sub_neg_eq_add]
  rw [e] at hv ⊢
  exact mapsTo_eigen_of_commute (commute_of_mem_centralizer hg) hv

end Restrict

section Split

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

@[expose] def eigenPlus (l : E) (A : Module.End E V) : Submodule E V :=
  LinearMap.ker (invSMulOp l A - 1)

@[expose] def eigenMinus (l : E) (A : Module.End E V) : Submodule E V :=
  LinearMap.ker (invSMulOp l A + 1)

theorem separatingLeft_domRestrict_of_orth (hBl : B.SeparatingLeft) {W₁ W₂ : Submodule E V}
    (hc : IsCompl W₁ W₂) (horth : ∀ v ∈ W₁, ∀ w ∈ W₂, B v w = 0) :
    (B.domRestrict₁₂ W₁ W₁).SeparatingLeft := by
  intro x hx
  refine Subtype.ext (hBl (x : V) fun w => ?_)
  obtain ⟨y, z, hy, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
  rw [map_add, horth x x.2 z hz, add_zero]
  exact hx ⟨y, hy⟩

theorem exists_split_centralizer_equiv (hp : p ≠ 2) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {A : sesqUnitaryGroup B} {l : E} (hl0 : l ≠ 0)
    (hAA : ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) *
      ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) = (l ^ 2) • 1)
    (hN : h.norm l = 1) :
    (∀ v ∈ eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
      ∀ w ∈ eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V),
        B v w = 0) ∧
    (B.domRestrict₁₂ (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))
      (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))).SeparatingLeft ∧
    (B.domRestrict₁₂ (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))
      (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))).SeparatingLeft ∧
    ∃ e : Subgroup.centralizer {A} ≃*
        sesqUnitaryGroup (B.domRestrict₁₂
          (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))
          (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) ×
        sesqUnitaryGroup (B.domRestrict₁₂
          (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))
          (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))),
      ∀ g : Subgroup.centralizer {A},
        (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)).subtype ∘ₗ
            (((e g).1 : LinearMap.GeneralLinearGroup E
              (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) :
                Module.End E
                  (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) =
          (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) ∘ₗ
            (eigenPlus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)).subtype ∧
        (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)).subtype ∘ₗ
            (((e g).2 : LinearMap.GeneralLinearGroup E
              (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) :
                Module.End E
                  (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V))) =
          (((g : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) : Module.End E V) ∘ₗ
            (eigenMinus l ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V)).subtype := by
  obtain ⟨A', hA'⟩ : ∃ A' : Module.End E V,
      A' = ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) := ⟨_, rfl⟩
  rw [← hA'] at hAA ⊢
  have h2 := two_ne_zero_of_odd h hp
  have hc : IsCompl (eigenPlus l A') (eigenMinus l A') :=
    isCompl_ker_sub_one_ker_add_one h2 (invSMulOp_mul_self hl0 hAA)
  have hTB : ∀ v w, B (invSMulOp l A' v) (invSMulOp l A' w) = B v w := fun v w => by
    rw [hA', sesq_invSMulOp, hN, inv_one, one_mul]
  have horth : ∀ v ∈ eigenPlus l A', ∀ w ∈ eigenMinus l A', B v w = 0 :=
    fun v hv w hw => sesq_eq_zero_of_eigen_one h2 hTB hv hw
  have horth' : ∀ v ∈ eigenMinus l A', ∀ w ∈ eigenPlus l A', B v w = 0 := fun v hv w hw => by
    rw [← hB.eq w v, horth w hw v hv, map_zero]
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
  obtain ⟨φ, hφ⟩ : ∃ φ : Subgroup.centralizer {A} →*
      sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l A') (eigenPlus l A')) ×
        sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l A') (eigenMinus l A')),
      φ = (unitaryRestrictHom _ hWp).prod (unitaryRestrictHom _ hWm) := ⟨_, rfl⟩
  have hinj : Function.Injective φ := by
    intro g g' hgg'
    rw [hφ] at hgg'
    have h1 := congrArg Prod.fst hgg'
    have h3 := congrArg Prod.snd hgg'
    refine Subtype.ext (Subtype.ext (Units.ext (endo_ext_of_isCompl hc
      (fun x hx => ?_) (fun x hx => ?_))))
    · exact congrArg (fun u : sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l A')
        (eigenPlus l A')) => ((((u : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
          Module.End E (eigenPlus l A')) ⟨x, hx⟩ : eigenPlus l A') : V)) h1
    · exact congrArg (fun u : sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l A')
        (eigenMinus l A')) => ((((u : LinearMap.GeneralLinearGroup E (eigenMinus l A')) :
          Module.End E (eigenMinus l A')) ⟨x, hx⟩ : eigenMinus l A') : V)) h3
  have hsurj : Function.Surjective φ := by
    rintro ⟨g₁, g₂⟩
    obtain ⟨G, hG⟩ : ∃ G : LinearMap.GeneralLinearGroup E V,
        G = glOfIsCompl hc (g₁ : LinearMap.GeneralLinearGroup E (eigenPlus l A'))
          (g₂ : LinearMap.GeneralLinearGroup E (eigenMinus l A')) := ⟨_, rfl⟩
    have hGl : ∀ x (hx : x ∈ eigenPlus l A'), (G : Module.End E V) x =
        (((g₁ : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
          Module.End E (eigenPlus l A')) ⟨x, hx⟩ : V) := fun x hx => by
      rw [hG]
      exact glOfIsCompl_apply_left hc _ _ ⟨x, hx⟩
    have hGr : ∀ x (hx : x ∈ eigenMinus l A'), (G : Module.End E V) x =
        (((g₂ : LinearMap.GeneralLinearGroup E (eigenMinus l A')) :
          Module.End E (eigenMinus l A')) ⟨x, hx⟩ : V) := fun x hx => by
      rw [hG]
      exact glOfIsCompl_apply_right hc _ _ ⟨x, hx⟩
    have hGU : G ∈ sesqUnitaryGroup B := by
      intro v w
      obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint v
      obtain ⟨x', y', hx', hy', rfl⟩ :=
        Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint w
      have i1 := g₁.2 ⟨x, hx⟩ ⟨x', hx'⟩
      have i2 := g₂.2 ⟨y, hy⟩ ⟨y', hy'⟩
      simp only [LinearMap.domRestrict₁₂_apply] at i1 i2
      simp only [map_add, LinearMap.add_apply]
      rw [hGl x hx, hGr y hy, hGl x' hx', hGr y' hy']
      rw [horth _ (((g₁ : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
          Module.End E (eigenPlus l A')) ⟨x, hx⟩).2 _
          (((g₂ : LinearMap.GeneralLinearGroup E (eigenMinus l A')) :
          Module.End E (eigenMinus l A')) ⟨y', hy'⟩).2,
        horth' _ (((g₂ : LinearMap.GeneralLinearGroup E (eigenMinus l A')) :
          Module.End E (eigenMinus l A')) ⟨y, hy⟩).2 _
          (((g₁ : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
          Module.End E (eigenPlus l A')) ⟨x', hx'⟩).2,
        horth x hx y' hy', horth' y hy x' hx', i1, i2]
    have hGC : (⟨G, hGU⟩ : sesqUnitaryGroup B) ∈ Subgroup.centralizer {A} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine Subtype.ext (Units.ext ?_)
      change (G : Module.End E V) * ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) =
        ((A : LinearMap.GeneralLinearGroup E V) : Module.End E V) * (G : Module.End E V)
      rw [← hA']
      refine commute_of_mapsTo_eigen h2 hl0 hAA (fun v hv => ?_) (fun v hv => ?_)
      · rw [hGl v hv]
        exact (((g₁ : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
          Module.End E (eigenPlus l A')) ⟨v, hv⟩).2
      · rw [hGr v hv]
        exact (((g₂ : LinearMap.GeneralLinearGroup E (eigenMinus l A')) :
          Module.End E (eigenMinus l A')) ⟨v, hv⟩).2
    refine ⟨⟨⟨G, hGU⟩, hGC⟩, ?_⟩
    rw [hφ]
    refine Prod.ext (Subtype.ext (Units.ext (LinearMap.ext fun x => Subtype.ext ?_)))
      (Subtype.ext (Units.ext (LinearMap.ext fun x => Subtype.ext ?_)))
    · exact hGl x x.2
    · exact hGr x x.2
  refine ⟨horth, separatingLeft_domRestrict_of_orth hBl hc horth,
    separatingLeft_domRestrict_of_orth hBl hc.symm horth',
    MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun g => ⟨LinearMap.ext fun v => ?_,
      LinearMap.ext fun v => ?_⟩⟩
  · change ((((φ g).1 : LinearMap.GeneralLinearGroup E (eigenPlus l A')) :
      Module.End E (eigenPlus l A')) v : V) = _
    rw [hφ]
    rfl
  · change ((((φ g).2 : LinearMap.GeneralLinearGroup E (eigenMinus l A')) :
      Module.End E (eigenMinus l A')) v : V) = _
    rw [hφ]
    rfl

end Split

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
