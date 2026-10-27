module

public import CFSG.GH74.GLS.IVK.Prod32.LangSL
public import CFSG.GH74.GLS.IVK.Prod32.LangDefs

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank

namespace LangC

section SL2Facts

variable {F : Type} [Field F]

theorem scalar_of_commute_sl (m : GL (Fin 2) F)
    (hm : ∀ x : SL2 F, m * (x : GL (Fin 2) F) = (x : GL (Fin 2) F) * m) :
    ∃ s : F, (m : Matrix (Fin 2) (Fin 2) F) = s • (1 : Matrix (Fin 2) (Fin 2) F) := by
  apply exists_smul_one_of_commute_sl
  intro b
  set y : SL2 F := specialLinearGroupEquivStatedSL 2 F b with hy
  have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hm y)
  have hyb : ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (b : Matrix (Fin 2) (Fin 2) F) :=
    specialLinearGroupEquivStatedSL_coe 2 F b
  simpa [hyb] using h2

theorem slNegOne_ne_one (h2 : (2 : F) ≠ 0) : slNegOne F ≠ 1 := by
  intro h
  have := congrArg (fun g : SL2 F => (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 0 0) h
  simp only [slNegOne_mat, sl_mat_one] at this
  apply h2
  have h' : (-1 : F) = 1 := by simpa using this
  linear_combination -h'

theorem slNegOne_comm (x : SL2 F) : slNegOne F * x = x * slNegOne F := by
  apply sl_ext
  rw [sl_mat_mul, sl_mat_mul, slNegOne_mat]
  simp

theorem slNegOne_mul_self : slNegOne F * slNegOne F = 1 := by
  apply sl_ext
  rw [sl_mat_mul, slNegOne_mat, sl_mat_one]
  simp

theorem eq_slNegOne_of_central (ζ : SL2 F) (hc : ∀ x : SL2 F, ζ * x = x * ζ) (hne : ζ ≠ 1) :
    ζ = slNegOne F := by
  obtain ⟨s, hs⟩ := scalar_of_commute_sl (ζ : GL (Fin 2) F) (fun x => congrArg Subtype.val (hc x))
  have hdet := det_sl ζ
  rw [hs, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] at hdet
  rcases mul_self_eq_one_iff.1 (by simpa [sq] using hdet : s * s = 1) with h1 | h1
  · exfalso
    apply hne
    apply sl_ext
    rw [hs, h1, one_smul, sl_mat_one]
  · apply sl_ext
    rw [hs, h1, slNegOne_mat, neg_smul, one_smul]

theorem slσ_slσ (σ : F ≃+* F) (hσ : orderOf σ = 2) (g : SL2 F) : slσ σ (slσ σ g) = g := by
  apply sl_ext
  rw [slσ_mat, slσ_mat]
  ext i j
  simp [Matrix.map_apply, apply_apply_of_orderOf σ hσ]

theorem slσ_negOne (σ : F ≃+* F) : slσ σ (slNegOne F) = slNegOne F := by
  apply sl_ext
  rw [slσ_mat, slNegOne_mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

theorem cv_cobdry (σ : F ≃+* F) (hσ : orderOf σ = 2) (x ε : SL2 F) (hε : ε = 1 ∨ ε = slNegOne F) :
    (x * (slσ σ x)⁻¹ * ε) * slσ σ (x * (slσ σ x)⁻¹ * ε) = 1 := by
  have hεc : ∀ y : SL2 F, ε * y = y * ε := by
    rcases hε with rfl | rfl
    · intro y; simp
    · exact slNegOne_comm
  have hεε : ε * ε = 1 := by
    rcases hε with rfl | rfl
    · simp
    · exact slNegOne_mul_self
  have hσε : slσ σ ε = ε := by
    rcases hε with rfl | rfl
    · exact map_one _
    · exact slσ_negOne σ
  rw [map_mul, map_mul, map_inv, slσ_slσ σ hσ, hσε]
  calc x * (slσ σ x)⁻¹ * ε * (slσ σ x * x⁻¹ * ε)
      = x * (slσ σ x)⁻¹ * (ε * (slσ σ x * x⁻¹)) * ε := by simp only [mul_assoc]
    _ = x * (slσ σ x)⁻¹ * ((slσ σ x * x⁻¹) * ε) * ε := by rw [hεc]
    _ = x * (slσ σ x)⁻¹ * (slσ σ x * x⁻¹) * (ε * ε) := by simp only [mul_assoc]
    _ = 1 := by rw [hεε]; group

end SL2Facts

section Pair

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

theorem z_mem₁ (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : z ∈ K₁ := by
  have : z ∈ K₁ ⊓ K₂ := by rw [h.inter]; exact Subgroup.mem_zpowers z
  exact this.1

theorem z_mem₂ (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : z ∈ K₂ := by
  have : z ∈ K₁ ⊓ K₂ := by rw [h.inter]; exact Subgroup.mem_zpowers z
  exact this.2

theorem z_mul_self (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : z * z = 1 := by
  have h1 : z ^ 2 = 1 := by rw [← h.z_ord]; exact pow_orderOf_eq_one z
  rwa [pow_two] at h1

theorem e_symm_conj₁ (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (x : SL2 F₁) :
    a * ((e₁.symm x : ↥K₁) : H) * a⁻¹ = ((e₁.symm (slσ σ₁ x) : ↥K₁) : H) := by
  have hx : a * ((e₁.symm x : ↥K₁) : H) * a⁻¹ ∈ K₁ := h.norm₁ _ (e₁.symm x).2
  have h1 := h.act₁ (e₁.symm x) hx
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : (⟨a * ((e₁.symm x : ↥K₁) : H) * a⁻¹, hx⟩ : ↥K₁) = e₁.symm (slσ σ₁ x) := by
    rw [MulEquiv.eq_symm_apply]
    exact h1
  exact congrArg Subtype.val h2

theorem e_symm_conj₂ (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (x : SL2 F₂) :
    a * ((e₂.symm x : ↥K₂) : H) * a⁻¹ = ((e₂.symm (slσ σ₂ x) : ↥K₂) : H) := by
  have hx : a * ((e₂.symm x : ↥K₂) : H) * a⁻¹ ∈ K₂ := h.norm₂ _ (e₂.symm x).2
  have h1 := h.act₂ (e₂.symm x) hx
  rw [MulEquiv.apply_symm_apply] at h1
  have h2 : (⟨a * ((e₂.symm x : ↥K₂) : H) * a⁻¹, hx⟩ : ↥K₂) = e₂.symm (slσ σ₂ x) := by
    rw [MulEquiv.eq_symm_apply]
    exact h1
  exact congrArg Subtype.val h2

theorem e_central_eq_negOne {F : Type} [Field F] (K : Subgroup H)
    (e : ↥K ≃* SL2 F) {z : H} (hz : z ∈ K) (hzo : orderOf z = 2) (hcomm : ∀ x ∈ K, x * z = z * x) :
    e ⟨z, hz⟩ = slNegOne F := by
  apply eq_slNegOne_of_central
  · intro x
    have h1 : (e.symm x : ↥K) * ⟨z, hz⟩ = ⟨z, hz⟩ * e.symm x :=
      Subtype.ext (hcomm _ (e.symm x).2)
    have h2 := congrArg e h1.symm
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  · intro h1
    have h2 : (⟨z, hz⟩ : ↥K) = 1 := e.injective (by rw [h1, map_one])
    have h3 : z = 1 := congrArg Subtype.val h2
    rw [h3, orderOf_one] at hzo
    omega

theorem e₁_z (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : e₁ ⟨z, z_mem₁ h⟩ = slNegOne F₁ :=
  e_central_eq_negOne K₁ e₁ (z_mem₁ h) h.z_ord (fun x hx => h.comm x hx z (z_mem₂ h))

theorem e₂_z (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : e₂ ⟨z, z_mem₂ h⟩ = slNegOne F₂ :=
  e_central_eq_negOne K₂ e₂ (z_mem₂ h) h.z_ord (fun x hx => (h.comm z (z_mem₁ h) x hx).symm)

theorem e₁_symm_negOne (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) :
    ((e₁.symm (slNegOne F₁) : ↥K₁) : H) = z := by
  rw [← e₁_z h, MulEquiv.symm_apply_apply]

theorem e₂_symm_negOne (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) :
    ((e₂.symm (slNegOne F₂) : ↥K₂) : H) = z := by
  rw [← e₂_z h, MulEquiv.symm_apply_apply]

@[expose] def pairMap (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : SL2 F₁ × SL2 F₂ →* H :=
  MonoidHom.noncommCoprod (K₁.subtype.comp e₁.symm.toMonoidHom)
    (K₂.subtype.comp e₂.symm.toMonoidHom)
    (fun x y => h.comm _ (e₁.symm x).2 _ (e₂.symm y).2)

theorem pairMap_apply (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (x : SL2 F₁) (y : SL2 F₂) :
    pairMap h (x, y) = ((e₁.symm x : ↥K₁) : H) * ((e₂.symm y : ↥K₂) : H) := rfl

theorem pairMap_mem (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (γ : SL2 F₁ × SL2 F₂) :
    pairMap h γ ∈ K₁ ⊔ K₂ :=
  mul_mem (Subgroup.mem_sup_left (e₁.symm γ.1).2) (Subgroup.mem_sup_right (e₂.symm γ.2).2)

theorem exists_pairMap_eq (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) {k : H} (hk : k ∈ K₁ ⊔ K₂) :
    ∃ γ : SL2 F₁ × SL2 F₂, pairMap h γ = k := by
  have hle : K₁ ⊔ K₂ ≤ (pairMap h).range := by
    refine sup_le ?_ ?_
    · intro k hk
      refine ⟨(e₁ ⟨k, hk⟩, 1), ?_⟩
      rw [pairMap_apply]
      simp
    · intro k hk
      refine ⟨(1, e₂ ⟨k, hk⟩), ?_⟩
      rw [pairMap_apply]
      simp
  exact hle hk

@[expose] noncomputable def pairTw (σ₁ : F₁ ≃+* F₁) (σ₂ : F₂ ≃+* F₂) :
    SL2 F₁ × SL2 F₂ ≃* SL2 F₁ × SL2 F₂ :=
  MulEquiv.prodCongr (slσ σ₁) (slσ σ₂)

theorem pairTw_apply (σ₁ : F₁ ≃+* F₁) (σ₂ : F₂ ≃+* F₂) (γ : SL2 F₁ × SL2 F₂) :
    pairTw σ₁ σ₂ γ = (slσ σ₁ γ.1, slσ σ₂ γ.2) := rfl

@[expose] noncomputable def negPair (F₁ F₂ : Type) [Field F₁] [Field F₂] : SL2 F₁ × SL2 F₂ :=
  (slNegOne F₁, slNegOne F₂)

theorem pairMap_twist (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (γ : SL2 F₁ × SL2 F₂) :
    a * pairMap h γ * a⁻¹ = pairMap h (pairTw σ₁ σ₂ γ) := by
  obtain ⟨x, y⟩ := γ
  rw [pairTw_apply, pairMap_apply, pairMap_apply]
  calc a * (((e₁.symm x : ↥K₁) : H) * ((e₂.symm y : ↥K₂) : H)) * a⁻¹
      = (a * ((e₁.symm x : ↥K₁) : H) * a⁻¹) * (a * ((e₂.symm y : ↥K₂) : H) * a⁻¹) := by group
    _ = _ := by rw [e_symm_conj₁ h, e_symm_conj₂ h]

theorem pairMap_negPair (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) : pairMap h (negPair F₁ F₂) = 1 := by
  rw [negPair, pairMap_apply, e₁_symm_negOne h, e₂_symm_negOne h, z_mul_self h]

theorem pairMap_eq_one_iff (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (γ : SL2 F₁ × SL2 F₂) :
    pairMap h γ = 1 ↔ γ = 1 ∨ γ = negPair F₁ F₂ := by
  constructor
  · intro hγ
    obtain ⟨x, y⟩ := γ
    rw [pairMap_apply] at hγ
    set p : ↥K₁ := e₁.symm x with hp
    set q : ↥K₂ := e₂.symm y with hq
    have hpq : (p : H) = (q : H)⁻¹ := eq_inv_of_mul_eq_one_left hγ
    have hmem : (p : H) ∈ K₁ ⊓ K₂ := ⟨p.2, by rw [hpq]; exact K₂.inv_mem q.2⟩
    rw [h.inter] at hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hz2 : z * z = 1 := z_mul_self h
    have hn' : (p : H) = 1 ∨ (p : H) = z := by
      have hn2 : z ^ (n % 2) = (p : H) := by
        have := zpow_mod_orderOf z n
        rw [h.z_ord] at this
        rw [← hn, ← this]
        norm_num
      rcases Int.emod_two_eq_zero_or_one n with h0 | h1
      · left; rw [h0] at hn2; simpa using hn2.symm
      · right; rw [h1] at hn2; simpa using hn2.symm
    rcases hn' with h0 | h1
    · left
      have hx : x = 1 := by
        have : e₁.symm x = 1 := Subtype.ext h0
        simpa using congrArg e₁ this
      have hq : (q : H) = 1 := by rw [h0, one_mul] at hγ; exact hγ
      have hy : y = 1 := by
        have : e₂.symm y = 1 := Subtype.ext hq
        simpa using congrArg e₂ this
      rw [hx, hy]; rfl
    · right
      have hx : x = slNegOne F₁ := by
        have : e₁.symm x = e₁.symm (slNegOne F₁) := Subtype.ext (by rw [e₁_symm_negOne h]; exact h1)
        exact e₁.symm.injective this
      have hq : (q : H) = z := by
        have : (q : H) = (p : H)⁻¹ := eq_inv_of_mul_eq_one_right hγ
        rw [this, h1]
        exact inv_eq_of_mul_eq_one_right (z_mul_self h)
      have hy : y = slNegOne F₂ := by
        have : e₂.symm y = e₂.symm (slNegOne F₂) := Subtype.ext (by rw [e₂_symm_negOne h]; exact hq)
        exact e₂.symm.injective this
      rw [hx, hy]; rfl
  · rintro (rfl | rfl)
    · exact map_one _
    · exact pairMap_negPair h

theorem invol_eq (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (γ : SL2 F₁ × SL2 F₂) :
    (pairMap h γ * a) * (pairMap h γ * a) = pairMap h (γ * pairTw σ₁ σ₂ γ) := by
  have e1 : pairMap h γ * a * (pairMap h γ * a) =
      pairMap h γ * (a * pairMap h γ * a⁻¹) * (a * a) := by group
  rw [e1, h.a_sq, mul_one, pairMap_twist, map_mul]

theorem conj_pairMap (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (η γ : SL2 F₁ × SL2 F₂) :
    pairMap h η * (pairMap h γ * a) * (pairMap h η)⁻¹ =
      pairMap h (η * γ * (pairTw σ₁ σ₂ η)⁻¹) * a := by
  have e1 : pairMap h η * (pairMap h γ * a) * (pairMap h η)⁻¹ =
      pairMap h η * pairMap h γ * (a * (pairMap h η)⁻¹ * a⁻¹) * a := by group
  have e2 : a * (pairMap h η)⁻¹ * a⁻¹ = (pairMap h (pairTw σ₁ σ₂ η))⁻¹ := by
    rw [← pairMap_twist h η]; group
  rw [e1, e2, map_mul, map_mul, map_inv]

theorem conj_a_cv (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) {γ : SL2 F₁ × SL2 F₂}
    (hc : ConjUnder (K₁ ⊔ K₂) a (pairMap h γ * a)) : γ.1 * slσ σ₁ γ.1 = 1 := by
  obtain ⟨g, hg, hga⟩ := hc
  obtain ⟨η, rfl⟩ := exists_pairMap_eq h hg
  have h1 := conj_pairMap h η 1
  rw [map_one, one_mul, mul_one] at h1
  have h2 : pairMap h (η * (pairTw σ₁ σ₂ η)⁻¹) = pairMap h γ := by
    have := h1.symm.trans hga
    exact mul_right_cancel this
  have h3 : pairMap h ((η * (pairTw σ₁ σ₂ η)⁻¹)⁻¹ * γ) = 1 := by
    rw [map_mul, map_inv, h2, inv_mul_cancel]
  have hεγ : ∃ ε : SL2 F₁, (ε = 1 ∨ ε = slNegOne F₁) ∧
      γ.1 = η.1 * (slσ σ₁ η.1)⁻¹ * ε := by
    rcases (pairMap_eq_one_iff h _).1 h3 with h4 | h4
    · refine ⟨1, Or.inl rfl, ?_⟩
      have h5 : γ = η * (pairTw σ₁ σ₂ η)⁻¹ := (inv_mul_eq_one.1 h4).symm
      rw [mul_one, h5]
      simp [pairTw_apply]
    · refine ⟨slNegOne F₁, Or.inr rfl, ?_⟩
      have h5 : γ = η * (pairTw σ₁ σ₂ η)⁻¹ * negPair F₁ F₂ := by
        rw [inv_mul_eq_iff_eq_mul] at h4
        exact h4
      rw [h5]
      simp [pairTw_apply, negPair]
  obtain ⟨ε, hε, hγ1⟩ := hεγ
  rw [hγ1]
  exact cv_cobdry σ₁ h.σ₁_ord η.1 ε hε

theorem pairMap_conj_left (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) (γ : SL2 F₁ × SL2 F₂) (V : SL2 F₁) :
    pairMap h γ * ((e₁.symm V : ↥K₁) : H) * (pairMap h γ)⁻¹ =
      ((e₁.symm (γ.1 * V * γ.1⁻¹) : ↥K₁) : H) := by
  obtain ⟨x, y⟩ := γ
  rw [pairMap_apply]
  have hq : ((e₂.symm y : ↥K₂) : H) * ((e₁.symm V : ↥K₁) : H) =
      ((e₁.symm V : ↥K₁) : H) * ((e₂.symm y : ↥K₂) : H) :=
    (h.comm _ (e₁.symm V).2 _ (e₂.symm y).2).symm
  calc ((e₁.symm x : ↥K₁) : H) * ((e₂.symm y : ↥K₂) : H) * ((e₁.symm V : ↥K₁) : H) *
        (((e₁.symm x : ↥K₁) : H) * ((e₂.symm y : ↥K₂) : H))⁻¹
      = ((e₁.symm x : ↥K₁) : H) * (((e₂.symm y : ↥K₂) : H) * ((e₁.symm V : ↥K₁) : H) *
          ((e₂.symm y : ↥K₂) : H)⁻¹) * ((e₁.symm x : ↥K₁) : H)⁻¹ := by group
    _ = ((e₁.symm x : ↥K₁) : H) * ((e₁.symm V : ↥K₁) : H) * ((e₁.symm x : ↥K₁) : H)⁻¹ := by
        rw [hq]; group
    _ = _ := by simp

end Pair

end LangC

end CFSG.GH74.GLS.IVK.Prod3
