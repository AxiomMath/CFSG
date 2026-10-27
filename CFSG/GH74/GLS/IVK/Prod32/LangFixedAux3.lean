module

public import CFSG.GH74.GLS.IVK.Prod32.LangFixedAux

public section

namespace CFSG.GH74.GLS.IVK.Prod3.LangF

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GorensteinWalter
open scoped commutatorElement

section Psi

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

noncomputable def phi (K₁ : Subgroup H) (e₂ : ↥K₂ ≃* SL2 F₂) :
    ↥K₁ × ↥K₂ →* PGL2 F₂ :=
  Matrix.ProjGenLinGroup.mk.comp
    ((StatedSL 2 F₂).subtype.comp (e₂.toMonoidHom.comp (MonoidHom.snd _ _)))

def mulHom' (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) : ↥K₁ × ↥K₂ →* ↥(K₁ ⊔ K₂) :=
  (mulHom hc).codRestrict (K₁ ⊔ K₂)
    (fun p => mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2))

theorem mulHom'_surjective (hc : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) :
    Function.Surjective (mulHom' hc) := by
  rintro ⟨x, hx⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff_of_comm hc).1 hx
  exact ⟨(⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩), rfl⟩

theorem ker_mulHom'_le (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) :
    (mulHom' h.comm).ker ≤ (phi K₁ e₂).ker := by
  rintro ⟨k₁, k₂⟩ hk
  have h1 : (k₁ : H) * k₂ = 1 := congrArg Subtype.val hk
  have hk₂K₁ : (k₂ : H) ∈ K₁ := by
    have : (k₂ : H) = (k₁ : H)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact inv_mem k₁.2
  show Matrix.ProjGenLinGroup.mk ((e₂ k₂ : SL2 F₂) : GL (Fin 2) F₂) = 1
  rw [Matrix.ProjGenLinGroup.mk_eq_one]
  exact central_mem_center _ (e₁_central (symm h) k₂.2 hk₂K₁)

noncomputable def psi₀ (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : ↥(K₁ ⊔ K₂) →* PGL2 F₂ :=
  (mulHom' h.comm).liftOfRightInverse (Function.surjInv (mulHom'_surjective h.comm))
    (Function.rightInverse_surjInv _) ⟨phi K₁ e₂, ker_mulHom'_le h⟩

theorem psi₀_apply (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) {k₁ k₂ : H} (hk₁ : k₁ ∈ K₁)
    (hk₂ : k₂ ∈ K₂) :
    psi₀ h ⟨k₁ * k₂, mul_mem (mem_sup_left hk₁) (mem_sup_right hk₂)⟩ =
      Matrix.ProjGenLinGroup.mk ((e₂ ⟨k₂, hk₂⟩ : SL2 F₂) : GL (Fin 2) F₂) :=
  MonoidHom.liftOfRightInverse_comp_apply (mulHom' h.comm) _ _ _ (⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩)

noncomputable def psi (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) :
    ↥(cen (K₁ ⊔ K₂) a) →* PGL2 F₂ :=
  (psi₀ h).comp (Subgroup.inclusion (inf_le_left : cen (K₁ ⊔ K₂) a ≤ K₁ ⊔ K₂))

theorem psi_apply (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) {k₁ k₂ : H} (hk₁ : k₁ ∈ K₁)
    (hk₂ : k₂ ∈ K₂) (hc : k₁ * k₂ ∈ cen (K₁ ⊔ K₂) a) :
    psi h ⟨k₁ * k₂, hc⟩ =
      Matrix.ProjGenLinGroup.mk ((e₂ ⟨k₂, hk₂⟩ : SL2 F₂) : GL (Fin 2) F₂) :=
  psi₀_apply h hk₁ hk₂

end Psi

section Kernel

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem e₂_z_matrix :
    (((e₂ ⟨z, z_mem₂ h⟩ : SL2 F₂) : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) = -1 :=
  e₁_z_matrix (symm h)

theorem ker_psi : (psi h).ker = (cen K₁ a).subgroupOf (cen (K₁ ⊔ K₂) a) := by
  ext ⟨c, hcmem⟩
  obtain ⟨hcK, hca⟩ := mem_cen.1 hcmem
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff h).1 hcK
  rw [MonoidHom.mem_ker, psi_apply h hk₁ hk₂, mem_subgroupOf, mem_cen]
  show _ ↔ (k₁ * k₂ ∈ K₁ ∧ k₁ * k₂ * a = a * (k₁ * k₂))
  constructor
  · intro hψ
    refine ⟨?_, hca⟩
    rw [Matrix.ProjGenLinGroup.mk_eq_one] at hψ
    have hcen : ∀ x : SL2 F₂, x * e₂ ⟨k₂, hk₂⟩ = e₂ ⟨k₂, hk₂⟩ * x := by
      intro x
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.1 hψ) (x : GL (Fin 2) F₂)
    rcases central_cases _ hcen with h1 | h1
    · have h2 : e₂ ⟨k₂, hk₂⟩ = 1 := Subtype.ext (Units.ext (by simpa using h1))
      have h3 : (⟨k₂, hk₂⟩ : ↥K₂) = 1 := e₂.injective (h2.trans (map_one e₂).symm)
      have h4 : k₂ = 1 := congrArg Subtype.val h3
      rw [h4, mul_one]
      exact hk₁
    · have h2 : e₂ ⟨k₂, hk₂⟩ = e₂ ⟨z, z_mem₂ h⟩ :=
        Subtype.ext (Units.ext (h1.trans (e₂_z_matrix h).symm))
      have h3 : k₂ = z := congrArg Subtype.val (e₂.injective h2)
      rw [h3]
      exact mul_mem hk₁ (z_mem₁ h)
  · rintro ⟨hK, -⟩
    have hk₂K₁ : k₂ ∈ K₁ := by
      have := mul_mem (inv_mem hk₁) hK
      simpa using this
    rw [Matrix.ProjGenLinGroup.mk_eq_one]
    exact central_mem_center _ (e₁_central (symm h) hk₂ hk₂K₁)

theorem range_psi_le : (psi h).range ≤ (pgl2Incl σ₂).range := by
  rintro _ ⟨⟨c, hcmem⟩, rfl⟩
  obtain ⟨hcK, hca⟩ := mem_cen.1 hcmem
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (mem_sup_iff h).1 hcK
  rw [psi_apply h hk₁ hk₂, mem_range_pgl2Incl_iff]
  obtain ⟨u, hu, -, hu₂⟩ := exists_twist_of_fixed h hk₁ hk₂ hca
  have hu₂' : a * k₂ * a⁻¹ ∈ K₂ := h.norm₂ k₂ hk₂
  have huinv₂ : u⁻¹ ∈ K₂ := inv_mem hu.2
  have h1 : e₂ ⟨a * k₂ * a⁻¹, hu₂'⟩ = e₂ ⟨k₂, hk₂⟩ * e₂ ⟨u⁻¹, huinv₂⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hu₂
  have h2 := h.act₂ ⟨k₂, hk₂⟩ hu₂'
  rw [h1] at h2
  have h3 : (Matrix.GeneralLinearGroup.map σ₂.toRingHom ((e₂ ⟨k₂, hk₂⟩ : SL2 F₂) : GL (Fin 2) F₂)) =
      ((e₂ ⟨k₂, hk₂⟩ : SL2 F₂) : GL (Fin 2) F₂) * ((e₂ ⟨u⁻¹, huinv₂⟩ : SL2 F₂) : GL (Fin 2) F₂) :=
    congrArg Subtype.val h2.symm
  show pgl2RingEquiv σ₂ (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) F₂))
      ((e₂ ⟨k₂, hk₂⟩ : SL2 F₂) : GL (Fin 2) F₂)) =
    Matrix.ProjGenLinGroup.mk ((e₂ ⟨k₂, hk₂⟩ : SL2 F₂) : GL (Fin 2) F₂)
  rw [pgl2RingEquiv_mk, h3]
  exact mk_mul_of_mem_center _ _ (central_mem_center _ (e₁_central (symm h) huinv₂ (inv_mem hu.1)))

end Kernel

section Preimage

variable {F : Type} [Field F]

theorem exists_sl_mk_eq (G : GL (Fin 2) F)
    (hG : IsSquare ((G : Matrix (Fin 2) (Fin 2) F).det)) :
    ∃ g : SL2 F, Matrix.ProjGenLinGroup.mk (g : GL (Fin 2) F) = Matrix.ProjGenLinGroup.mk G := by
  obtain ⟨s, hs⟩ := hG
  have hs0 : s ≠ 0 := by
    rintro rfl
    have := (Matrix.isUnit_iff_isUnit_det (G : Matrix (Fin 2) (Fin 2) F)).1 G.isUnit
    rw [hs, mul_zero] at this
    exact not_isUnit_zero this
  let u : Fˣ := (Units.mk0 s hs0)⁻¹
  have hdet : ((G * Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar, hs]
    simp [Matrix.scalar_apply, Matrix.det_diagonal, u]
    field_simp
  refine ⟨⟨G * Matrix.GeneralLinearGroup.scalar (Fin 2) u, (mem_statedSL_iff_det _).2 hdet⟩, ?_⟩
  show Matrix.ProjGenLinGroup.mk (G * Matrix.GeneralLinearGroup.scalar (Fin 2) u) = _
  rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one]

theorem sigma_twist (σ : F ≃+* F) (g : SL2 F)
    (hfix : pgl2RingEquiv σ (Matrix.ProjGenLinGroup.mk (g : GL (Fin 2) F)) =
      Matrix.ProjGenLinGroup.mk (g : GL (Fin 2) F)) :
    ((glAut σ (g : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ∨
      ((glAut σ (g : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        -((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have hfix' : Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map σ.toRingHom
      (g : GL (Fin 2) F)) = Matrix.ProjGenLinGroup.mk (g : GL (Fin 2) F) :=
    (pgl2RingEquiv_mk σ (g : GL (Fin 2) F)).symm.trans hfix
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 hfix'
  have hmat : ((glAut σ (g : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      ((u : F) • (1 : Matrix (Fin 2) (Fin 2) F)) = ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    have := congrArg (fun x : GL (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hu
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal] at this ⊢
    exact this
  have hdetσ : ((glAut σ (g : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have h1 : ((glAut σ (g : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (σ : F →+* F).mapMatrix ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl
    rw [h1, ← RingHom.map_det, det_eq_one, map_one]
  have hu2 : (u : F) * u = 1 := by
    have := congrArg Matrix.det hmat
    rw [Matrix.det_mul, hdetσ, Matrix.det_smul, Matrix.det_one, det_eq_one] at this
    simpa [sq] using this
  rcases mul_self_eq_one_iff.1 hu2 with h1 | h1
  · left
    rw [h1] at hmat
    simpa using hmat
  · right
    rw [h1] at hmat
    have : -((glAut σ (g : GL (Fin 2) F) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by simpa using hmat
    rw [← this, neg_neg]

theorem exists_moved (σ : F ≃+* F) (hσ : orderOf σ = 2) : ∃ x : F, σ x ≠ x := by
  by_contra hcon
  push Not at hcon
  have : σ = 1 := RingEquiv.ext hcon
  rw [this, orderOf_one] at hσ
  omega

theorem sigma_sigma (σ : F ≃+* F) (hσ : orderOf σ = 2) (x : F) : σ (σ x) = x := by
  have h2 : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσ, pow_two] at this
  have := congrArg (fun τ : F ≃+* F => τ x) h2
  simpa [RingAut.mul_apply] using this

theorem exists_neg_eigen (σ : F ≃+* F) (hσ : orderOf σ = 2) : ∃ ι : F, ι ≠ 0 ∧ σ ι = -ι := by
  obtain ⟨x, hx⟩ := exists_moved σ hσ
  refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
  rw [map_sub, sigma_sigma σ hσ]
  ring

end Preimage

section Preimage2

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem exists_twist₁ : ∃ x₁ ∈ K₁, a * x₁ * a⁻¹ = x₁ * z := by
  obtain ⟨ι, hι, hσι⟩ := exists_neg_eigen σ₁ h.σ₁_ord
  let X : Matrix.SpecialLinearGroup (Fin 2) F₁ :=
    ⟨!![ι, 0; 0, ι⁻¹], by simp [Matrix.det_fin_two, hι]⟩
  let Xs : SL2 F₁ := specialLinearGroupEquivStatedSL 2 F₁ X
  refine ⟨(e₁.symm Xs : H), (e₁.symm Xs).2, ?_⟩
  have hxx := h.norm₁ (e₁.symm Xs) (e₁.symm Xs).2
  have h1 : e₁ ⟨a * (e₁.symm Xs : H) * a⁻¹, hxx⟩ = Xs * e₁ ⟨z, z_mem₁ h⟩ := by
    rw [h.act₁ (e₁.symm Xs) hxx, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    apply Units.ext
    show ((glAut σ₁ (Xs : GL (Fin 2) F₁) : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) =
      ((Xs : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) *
        ((e₁ ⟨z, z_mem₁ h⟩ : SL2 F₁) : GL (Fin 2) F₁)
    rw [e₁_z_matrix h]
    have hXs : ((Xs : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) = !![ι, 0; 0, ι⁻¹] := rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [glAut_coe, hXs, hσι, Matrix.mul_apply, Matrix.one_apply]
  have h2 : e₁ ⟨a * (e₁.symm Xs : H) * a⁻¹, hxx⟩ = e₁ (e₁.symm Xs * ⟨z, z_mem₁ h⟩) := by
    rw [map_mul, MulEquiv.apply_symm_apply]
    exact h1
  exact congrArg Subtype.val (e₁.injective h2)

end Preimage2

section Range

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

variable (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂)
include h

theorem exists_psi_eq (g₀ : GL (Fin 2) (fixedField σ₂)) :
    ∃ c : ↥(cen (K₁ ⊔ K₂) a), psi h c = pgl2Incl σ₂ (Matrix.ProjGenLinGroup.mk g₀) := by
  set G : GL (Fin 2) F₂ := Matrix.GeneralLinearGroup.map (fixedField σ₂).subtype g₀ with hG
  have hdet : IsSquare ((G : Matrix (Fin 2) (Fin 2) F₂).det) := by
    apply isSquare_of_mem_fixedField_of_even σ₂ (by rw [h.σ₂_ord]; exact even_two)
    have h1 : (G : Matrix (Fin 2) (Fin 2) F₂).det =
        (((g₀ : Matrix (Fin 2) (Fin 2) (fixedField σ₂)).det : fixedField σ₂) : F₂) :=
      (RingHom.map_det (fixedField σ₂).subtype
        (g₀ : Matrix (Fin 2) (Fin 2) (fixedField σ₂))).symm
    rw [h1]
    exact (((g₀ : Matrix (Fin 2) (Fin 2) (fixedField σ₂)).det : fixedField σ₂)).2
  obtain ⟨gS, hgS⟩ := exists_sl_mk_eq G hdet
  have hA : pgl2Incl σ₂ (Matrix.ProjGenLinGroup.mk g₀) = Matrix.ProjGenLinGroup.mk G := rfl
  have hfix : pgl2RingEquiv σ₂ (Matrix.ProjGenLinGroup.mk (gS : GL (Fin 2) F₂)) =
      Matrix.ProjGenLinGroup.mk (gS : GL (Fin 2) F₂) := by
    rw [hgS, ← hA]
    exact (mem_range_pgl2Incl_iff σ₂ _).1 ⟨_, rfl⟩
  have htw := sigma_twist σ₂ gS hfix
  set x₂ : ↥K₂ := e₂.symm gS with hx₂
  have hxx : a * (x₂ : H) * a⁻¹ ∈ K₂ := h.norm₂ x₂ x₂.2
  have hact := h.act₂ x₂ hxx
  have hex : e₂ x₂ = gS := by rw [hx₂, MulEquiv.apply_symm_apply]
  rw [hex] at hact
  rcases htw with htw | htw
  · have h1 : e₂ ⟨a * (x₂ : H) * a⁻¹, hxx⟩ = e₂ x₂ := by
      rw [hact, hex]
      exact Subtype.ext (Units.ext htw)
    have h2 : a * (x₂ : H) * a⁻¹ = x₂ := congrArg Subtype.val (e₂.injective h1)
    have h3 : (x₂ : H) * a = a * x₂ := (mul_inv_eq_iff_eq_mul.1 h2).symm
    have hc : (1 : H) * x₂ ∈ cen (K₁ ⊔ K₂) a := by
      rw [one_mul, mem_cen]
      exact ⟨mem_sup_right x₂.2, h3⟩
    refine ⟨⟨1 * x₂, hc⟩, ?_⟩
    rw [psi_apply h (one_mem K₁) x₂.2 hc, hA, ← hgS]
    simp [hex]
  · obtain ⟨x₁, hx₁, hx₁'⟩ := exists_twist₁ h
    have h1 : e₂ ⟨a * (x₂ : H) * a⁻¹, hxx⟩ = e₂ (x₂ * ⟨z, z_mem₂ h⟩) := by
      rw [hact, map_mul, hex]
      apply Subtype.ext
      apply Units.ext
      show ((glAut σ₂ (gS : GL (Fin 2) F₂) : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) =
        ((gS : GL (Fin 2) F₂) : Matrix (Fin 2) (Fin 2) F₂) *
          ((e₂ ⟨z, z_mem₂ h⟩ : SL2 F₂) : GL (Fin 2) F₂)
      rw [e₂_z_matrix h, htw]
      simp
    have h2 : a * (x₂ : H) * a⁻¹ = x₂ * z := congrArg Subtype.val (e₂.injective h1)
    have hc : x₁ * x₂ ∈ cen (K₁ ⊔ K₂) a := by
      rw [mem_cen]
      refine ⟨mul_mem (mem_sup_left hx₁) (mem_sup_right x₂.2), ?_⟩
      have h3 : a * (x₁ * x₂) * a⁻¹ = x₁ * x₂ := by
        calc a * (x₁ * x₂) * a⁻¹ = (a * x₁ * a⁻¹) * (a * x₂ * a⁻¹) := by group
          _ = (x₁ * z) * (x₂ * z) := by rw [hx₁', h2]
          _ = x₁ * (z * x₂) * z := by group
          _ = x₁ * (x₂ * z) * z := by rw [h.comm z (z_mem₁ h) x₂ x₂.2]
          _ = x₁ * x₂ * (z * z) := by group
          _ = x₁ * x₂ := by rw [z_sq h, mul_one]
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    refine ⟨⟨x₁ * x₂, hc⟩, ?_⟩
    rw [psi_apply h hx₁ x₂.2 hc, hA, ← hgS]
    simp [hex]

theorem range_psi : (psi h).range = (pgl2Incl σ₂).range := by
  apply le_antisymm (range_psi_le h)
  rintro _ ⟨B, rfl⟩
  induction B using Matrix.ProjGenLinGroup.induction_on with | mk g₀ => ?_
  obtain ⟨c, hc⟩ := exists_psi_eq h g₀
  exact ⟨c, hc⟩

end Range

end CFSG.GH74.GLS.IVK.Prod3.LangF
