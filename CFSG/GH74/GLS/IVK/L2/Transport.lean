module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section Transport

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)

omit [Finite F] in
theorem toPSL_apply (x : K) : toPSL e x = L2.equivPSL F (e x) := rfl

theorem semilinearEquivAut_inl (g : PGL2 F) :
    semilinearEquivAut F (SemidirectProduct.inl g) = pglAction F g := by
  show semilinearAction F (SemidirectProduct.inl g) = _
  exact semilinearAction_inl F g

theorem semilinearEquivAut_inr (σ : F ≃+* F) :
    semilinearEquivAut F (SemidirectProduct.inr σ) = psl2FieldAut F σ := by
  show semilinearAction F (SemidirectProduct.inr σ) = _
  exact semilinearAction_inr F σ

omit [Finite F] in
theorem toPSL_congr_symm (β : MulAut (PSL2 F)) (x : K) :
    toPSL e (((MulAut.congr (toPSL e)).symm β) x) = β (toPSL e x) := by
  have h := MulEquiv.apply_symm_apply (MulAut.congr (toPSL e)) β
  have _h2 := congrArg (fun γ : MulAut (PSL2 F) => γ (toPSL e x)) h
  simp

theorem innDiagHom_apply' (g : PGL2 F) :
    innDiagHom e g = (MulAut.congr (toPSL e)).symm (pglAction F g) := by
  show (MulAut.congr (toPSL e)).symm (semilinearEquivAut F (SemidirectProduct.inl g)) = _
  rw [semilinearEquivAut_inl]

theorem toPGL_toPSL_innDiagHom (g : PGL2 F) (x : K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e (innDiagHom e g x)) =
      g * Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e x) * g⁻¹ := by
  rw [innDiagHom_apply', toPSL_congr_symm, toPGL_pglAction]

omit [Finite F] in
theorem toPSL_fieldAutHom (σ : F ≃+* F) (x : K) :
    toPSL e (fieldAutHom e σ x) = psl2FieldAut F σ (toPSL e x) := by
  have h1 := toPSL_congr_symm e (psl2FieldAut F σ) x
  exact h1

theorem innDiagHom_injective : Function.Injective (innDiagHom e) := by
  intro g h hgh
  have h1 : (semilinearEquivAut F) (SemidirectProduct.inl g) =
      (semilinearEquivAut F) (SemidirectProduct.inl h) :=
    (MulAut.congr (toPSL e)).symm.injective hgh
  exact SemidirectProduct.inl_injective ((semilinearEquivAut F).injective h1)

omit [Finite F] in
theorem fieldAutHom_apply' (σ : F ≃+* F) :
    fieldAutHom e σ = (MulAut.congr (toPSL e)).symm (psl2FieldAut F σ) := rfl

omit [Finite F] in
theorem fieldAutHom_injective : Function.Injective (fieldAutHom e) := by
  intro σ τ hστ
  have h1 : psl2FieldAut F σ = psl2FieldAut F τ :=
    (MulAut.congr (toPSL e)).symm.injective hστ
  exact psl2FieldAut_injective F h1

theorem innAut_le_innDiagSub : innAut K ≤ innDiagSub e := by
  rintro _ ⟨k, rfl⟩
  refine ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k), ?_⟩
  ext x
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_toPSL_innDiagHom]
  simp [MulAut.conj_apply]

end Transport

theorem isOddPrimePower_of_L2Field {F : Type} [Field F] [Finite F] (h : L2Field F) :
    IsOddPrimePower (Nat.card F) := by
  have := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' F
  have hq : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  refine ⟨p, n, hp, ?_, n.pos, hq⟩
  by_contra hpo
  have h2 : p = 2 := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · exact h2
    · exact absurd h2 hpo
  have hq2 : Even (Nat.card F) := by
    rw [hq, h2]
    exact (Nat.even_pow.mpr ⟨even_two, n.pos.ne'⟩)
  exact (Nat.not_even_iff_odd.mpr h.1) hq2

section Structure

variable {F : Type} [Field F] [Finite F]

theorem card_pgl2_eq_two_mul (h : L2Field F) : Nat.card (PGL2 F) = 2 * Nat.card (PSL2 F) := by
  have hodd := isOddPrimePower_of_L2Field h
  rw [pgl2_card_formula, psl2_card_formula F hodd]
  have hq : Odd (Nat.card F) := h.1
  have hfactorEven : Even (Nat.card F ^ 2 - 1) :=
    Nat.Odd.sub_odd hq.pow (show Odd (1 : ℕ) from odd_one)
  have hdvd : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) :=
    dvd_mul_of_dvd_right hfactorEven.two_dvd _
  exact (Nat.mul_div_cancel' hdvd).symm

variable {K : Type} [Group K] (e : K ≃* L2 F)

theorem innDiagSub_inf_fieldAutSub : innDiagSub e ⊓ fieldAutSub e = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro α ⟨⟨g, rfl⟩, ⟨σ, hσ⟩⟩
  have h1 : (semilinearEquivAut F) (SemidirectProduct.inl g) =
      (semilinearEquivAut F) (SemidirectProduct.inr σ) := by
    rw [semilinearEquivAut_inl, semilinearEquivAut_inr]
    apply (MulAut.congr (toPSL e)).symm.injective
    rw [← innDiagHom_apply', ← fieldAutHom_apply']
    exact hσ.symm
  have h2 := (semilinearEquivAut F).injective h1
  have h3 : g = 1 := by
    have := congrArg SemidirectProduct.left h2
    simpa using this
  rw [h3, map_one]

theorem innDiagSub_sup_fieldAutSub : innDiagSub e ⊔ fieldAutSub e = ⊤ := by
  rw [eq_top_iff]
  intro α _
  obtain ⟨x, hx⟩ := (semilinearEquivAut F).surjective ((MulAut.congr (toPSL e)) α)
  have hx' : α = innDiagHom e x.left * fieldAutHom e x.right := by
    apply (MulAut.congr (toPSL e)).injective
    have h1 : (semilinearEquivAut F)
        (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) =
        (MulAut.congr (toPSL e)) α := by
      rw [SemidirectProduct.inl_left_mul_inr_right]
      exact hx
    rw [map_mul, semilinearEquivAut_inl, semilinearEquivAut_inr] at h1
    rw [map_mul, innDiagHom_apply', fieldAutHom_apply', MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    exact h1.symm
  rw [hx']
  exact Subgroup.mul_mem_sup ⟨x.left, rfl⟩ ⟨x.right, rfl⟩

include e in
theorem card_eq_of_L2Field (h : L2Field F) :
    Nat.card K = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
  rw [Nat.card_congr (toPSL e).toEquiv]
  exact psl2_card_formula F (isOddPrimePower_of_L2Field h)

theorem card_innDiagSub (h : L2Field F) : Nat.card (innDiagSub e) = 2 * Nat.card K := by
  have h1 : Nat.card (innDiagSub e) = Nat.card (PGL2 F) :=
    (Nat.card_congr (MonoidHom.ofInjective (innDiagHom_injective e)).toEquiv).symm
  rw [h1, card_pgl2_eq_two_mul h, Nat.card_congr (toPSL e).toEquiv]

end Structure

section Normal

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)

instance innAut_normal : (innAut K).Normal where
  conj_mem := by
    rintro _ ⟨k, rfl⟩ β
    refine ⟨β k, ?_⟩
    ext x
    simp [MulAut.conj_apply]

theorem innDiagSub_normal : (innDiagSub e).Normal := by
  let Φ : PGammaL2 F →* MulAut K :=
    (MulAut.congr (toPSL e)).symm.toMonoidHom.comp (semilinearEquivAut F).toMonoidHom
  have hΦ : Function.Surjective Φ := by
    intro β
    obtain ⟨x, hx⟩ := (semilinearEquivAut F).surjective ((MulAut.congr (toPSL e)) β)
    refine ⟨x, ?_⟩
    show (MulAut.congr (toPSL e)).symm ((semilinearEquivAut F) x) = β
    rw [hx]
    exact MulEquiv.symm_apply_apply _ _
  have h : innDiagSub e = (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range.map Φ := by
    rw [innDiagSub, innDiagHom, ← MonoidHom.range_comp]
    rfl
  rw [h]
  exact Subgroup.Normal.map inferInstance Φ hΦ

end Normal

section Finite

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

omit [Finite K] in
include e in
theorem conj_injective_of_L2 : Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hx
    have hc : (toPSL e x) ∈ Subgroup.center (PSL2 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun α : MulAut K => α ((toPSL e).symm y)) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      have h2 := congrArg (toPSL e) this
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    rw [psl2_center_eq_bot F, Subgroup.mem_bot] at hc
    exact (toPSL e).injective (by rw [hc, map_one])
  · rintro rfl
    simp

omit [Finite K] in
include e in
theorem card_innAut : Nat.card (innAut K) = Nat.card K := by
  rw [innAut]
  exact (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_L2 e)).toEquiv).symm

omit [Finite K] in
theorem card_innDiagSub_eq (h : L2Field F) :
    Nat.card (innDiagSub e) = 2 * Nat.card (innAut K) := by
  rw [card_innDiagSub e h, card_innAut e]

theorem innAut_sup_zpowers_eq (h : L2Field F) {t : MulAut K} (ht : t ∈ innDiagSub e)
    (ht' : t ∉ innAut K) : innAut K ⊔ Subgroup.zpowers t = innDiagSub e := by
  have hle : innAut K ⊔ Subgroup.zpowers t ≤ innDiagSub e :=
    sup_le (innAut_le_innDiagSub e) ((Subgroup.zpowers_le).2 ht)
  have hne : innAut K ≠ innAut K ⊔ Subgroup.zpowers t := by
    intro heq
    apply ht'
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (le_sup_left : innAut K ≤ innAut K ⊔ Subgroup.zpowers t)
  have hd2 : Nat.card ↥(innAut K ⊔ Subgroup.zpowers t) ∣ Nat.card ↥(innDiagSub e) :=
    Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card (innAut K) := Nat.card_pos
  have hkd : k ∣ 2 := by
    rw [card_innDiagSub_eq e h, hk, mul_comm 2] at hd2
    exact (Nat.mul_dvd_mul_iff_left hpos).mp hd2
  rcases (Nat.dvd_prime Nat.prime_two).mp hkd with rfl | rfl
  · exfalso
    apply hne
    apply Subgroup.eq_of_le_of_card_ge le_sup_left
    rw [hk, mul_one]
  · apply Subgroup.eq_of_le_of_card_ge hle
    rw [hk, card_innDiagSub_eq e h]
    exact le_of_eq (mul_comm _ _)

theorem innAut_relIndex_two (h : L2Field F) : (innAut K).relIndex (innDiagSub e) = 2 := by
  have hle : innAut K ≤ innDiagSub e := innAut_le_innDiagSub e
  have h1 := Subgroup.card_mul_index ((innAut K).subgroupOf (innDiagSub e))
  have h2 : Nat.card ↥((innAut K).subgroupOf (innDiagSub e)) = Nat.card (innAut K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2, card_innDiagSub_eq e h] at h1
  have hpos : 0 < Nat.card (innAut K) := Nat.card_pos
  unfold Subgroup.relIndex
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans (mul_comm _ _))


end Finite

end CFSG.GH74.GLS.IVK
