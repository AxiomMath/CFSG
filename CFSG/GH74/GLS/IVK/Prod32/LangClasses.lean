module

public import CFSG.GH74.GLS.IVK.Prod32.LangPair
public import CFSG.GH74.GLS.IVK.Statements.Sec32

public section

namespace CFSG.GH74.GLS.IVK.Prod3

open Subgroup CFSG CFSG.Assembly.LowTwoRank

section LangClasses

open LangC

variable {H : Type} [Group H] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
  {K₁ K₂ : Subgroup H} {z a : H} {e₁ : ↥K₁ ≃* SL2 F₁} {e₂ : ↥K₂ ≃* SL2 F₂}
  {σ₁ : F₁ ≃+* F₁} {σ₂ : F₂ ≃+* F₂}

theorem LangC.two_ne_zero_of_odd {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    (2 : F) ≠ 0 :=
  Ring.two_ne_zero (CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd)

theorem LangHyp.two_classes (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) :
    ∃ b ∈ invCoset (K₁ ⊔ K₂) a, ¬ ConjUnder (K₁ ⊔ K₂) a b ∧
      ∀ u ∈ invCoset (K₁ ⊔ K₂) a, ConjUnder (K₁ ⊔ K₂) a u ∨ ConjUnder (K₁ ⊔ K₂) b u := by
  obtain ⟨x₁, hx₁⟩ := exists_cocycle_neg h.odd₁.1 σ₁ h.σ₁_ord
  obtain ⟨x₂, hx₂⟩ := exists_cocycle_neg h.odd₂.1 σ₂ h.σ₂_ord
  set γb : SL2 F₁ × SL2 F₂ := (x₁, x₂) with hγb
  have hcvb : γb * pairTw σ₁ σ₂ γb = negPair F₁ F₂ := Prod.ext hx₁ hx₂
  refine ⟨pairMap h γb * a, ⟨⟨pairMap h γb, pairMap_mem h γb, rfl⟩, ?_⟩, ?_, ?_⟩
  · rw [invol_eq, hcvb, pairMap_negPair]
  · intro hc
    have h1 := conj_a_cv h hc
    have h2 : γb.1 * slσ σ₁ γb.1 = slNegOne F₁ := hx₁
    rw [h1] at h2
    exact slNegOne_ne_one (LangC.two_ne_zero_of_odd h.odd₁.1) h2.symm
  · intro u hu
    obtain ⟨⟨k, hk, rfl⟩, hu2⟩ := hu
    obtain ⟨γ, rfl⟩ := exists_pairMap_eq h hk
    rw [invol_eq, pairMap_eq_one_iff] at hu2
    rcases hu2 with h0 | h0
    ·
      left
      have h01 : γ.1 * slσ σ₁ γ.1 = 1 := congrArg Prod.fst h0
      have h02 : γ.2 * slσ σ₂ γ.2 = 1 := congrArg Prod.snd h0
      obtain ⟨η₁, hη₁⟩ := cocycle_orbit h.odd₁.1 σ₁ h.σ₁_ord (ε := 1) (Or.inl rfl)
        (k := 1) (k' := γ.1) (by simp) h01
      obtain ⟨η₂, hη₂⟩ := cocycle_orbit h.odd₂.1 σ₂ h.σ₂_ord (ε := 1) (Or.inl rfl)
        (k := 1) (k' := γ.2) (by simp) h02
      have hγ : γ = (η₁, η₂) * 1 * (pairTw σ₁ σ₂ (η₁, η₂))⁻¹ := by
        refine Prod.ext ?_ ?_
        · simpa [pairTw_apply] using hη₁
        · simpa [pairTw_apply] using hη₂
      refine ⟨pairMap h (η₁, η₂), pairMap_mem h _, ?_⟩
      have := conj_pairMap h (η₁, η₂) 1
      rw [map_one, one_mul, ← hγ] at this
      exact this
    ·
      right
      have h01 : γ.1 * slσ σ₁ γ.1 = slNegOne F₁ := congrArg Prod.fst h0
      have h02 : γ.2 * slσ σ₂ γ.2 = slNegOne F₂ := congrArg Prod.snd h0
      obtain ⟨η₁, hη₁⟩ := cocycle_orbit h.odd₁.1 σ₁ h.σ₁_ord (ε := slNegOne F₁) (Or.inr rfl)
        (k := x₁) (k' := γ.1) hx₁ h01
      obtain ⟨η₂, hη₂⟩ := cocycle_orbit h.odd₂.1 σ₂ h.σ₂_ord (ε := slNegOne F₂) (Or.inr rfl)
        (k := x₂) (k' := γ.2) hx₂ h02
      have hγ : γ = (η₁, η₂) * γb * (pairTw σ₁ σ₂ (η₁, η₂))⁻¹ := by
        refine Prod.ext ?_ ?_
        · simpa [pairTw_apply, hγb] using hη₁
        · simpa [pairTw_apply, hγb] using hη₂
      refine ⟨pairMap h (η₁, η₂), pairMap_mem h _, ?_⟩
      have := conj_pairMap h (η₁, η₂) γb
      rw [← hγ] at this
      exact this

theorem LangHyp.z_class (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) :
    ConjUnder (K₁ ⊔ K₂) a (a * z) := by
  have _hfin : Finite (F₂ ≃+* F₂) := CFSG.GH74.GLS.IVK.finite_ringEquiv F₂
  obtain ⟨t, ht⟩ := exists_twist_neg_one h.odd₁.1 σ₁ h.σ₁_ord
  have hpz : pairMap h (slNegOne F₁, 1) = z := by
    rw [pairMap_apply, e₁_symm_negOne h]
    simp
  have hconj : a * z * a⁻¹ = z := by
    have h1 := pairMap_twist h (slNegOne F₁, 1)
    rw [hpz, pairTw_apply] at h1
    simp only [slσ_negOne, map_one] at h1
    rw [h1, hpz]
  have hza : a * z = z * a := mul_inv_eq_iff_eq_mul.1 hconj
  refine ⟨pairMap h (t, 1), pairMap_mem h _, ?_⟩
  have h2 := conj_pairMap h (t, 1) 1
  rw [map_one, one_mul] at h2
  have h3 : ((t, 1) * 1 * (pairTw σ₁ σ₂ (t, 1))⁻¹ : SL2 F₁ × SL2 F₂) = (slNegOne F₁, 1) := by
    refine Prod.ext ?_ ?_
    · simpa [pairTw_apply] using ht
    · simp [pairTw_apply]
  rw [h3, hpz] at h2
  rw [h2, hza]

theorem LangHyp.fuse (h : LangHyp K₁ K₂ z a e₁ e₂ σ₁ σ₂) {y c : H}
    (hy₁ : DiagOutE K₁ e₁ y) (hy₂ : DiagOutE K₂ e₂ y) (hc : c ∈ K₁ ⊔ K₂)
    (hya : y * a * y⁻¹ = c * a) :
    c * a ∈ invCoset (K₁ ⊔ K₂) a ∧ ¬ ConjUnder (K₁ ⊔ K₂) a (c * a) := by
  have _ := And.intro hy₂ (CFSG.GH74.GLS.IVK.finite_ringEquiv F₂)
  refine ⟨⟨⟨c, hc, rfl⟩, ?_⟩, ?_⟩
  · rw [← hya]
    calc y * a * y⁻¹ * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
      _ = 1 := by rw [h.a_sq]; group
  · obtain ⟨γ, rfl⟩ := exists_pairMap_eq h hc
    intro hconj
    have h1 := conj_a_cv h hconj
    obtain ⟨hynorm, d, hd, hdy⟩ := hy₁
    have hyac : y * a = pairMap h γ * a * y := by
      calc y * a = (y * a * y⁻¹) * y := by group
        _ = pairMap h γ * a * y := by rw [hya]
    have hsign : ∀ X : SL2 F₁, d * ((slσ σ₁ X : SL2 F₁) : GL (Fin 2) F₁) * d⁻¹ =
        (γ.1 : GL (Fin 2) F₁) * glAut σ₁ d * ((slσ σ₁ X : SL2 F₁) : GL (Fin 2) F₁) *
          (glAut σ₁ d)⁻¹ * (γ.1 : GL (Fin 2) F₁)⁻¹ := by
      intro X
      set Y : SL2 F₁ := slσ σ₁ X with hY
      set p : ↥K₁ := e₁.symm X with hp
      set p' : ↥K₁ := e₁.symm Y with hp'
      have hpp' : a * (p : H) * a⁻¹ = (p' : H) := e_symm_conj₁ h X
      have hxp : y * (p : H) * y⁻¹ ∈ K₁ := hynorm _ p.2
      have hxp' : y * (p' : H) * y⁻¹ ∈ K₁ := hynorm _ p'.2
      set q : ↥K₁ := ⟨y * (p : H) * y⁻¹, hxp⟩ with hq
      set q' : ↥K₁ := ⟨y * (p' : H) * y⁻¹, hxp'⟩ with hq'
      have hQ : ((e₁ q : SL2 F₁) : GL (Fin 2) F₁) = d * (X : GL (Fin 2) F₁) * d⁻¹ := by
        have h' : e₁ p = X := by rw [hp, MulEquiv.apply_symm_apply]
        have := hdy p hxp
        rw [h'] at this
        exact this
      have hZ : ((e₁ q' : SL2 F₁) : GL (Fin 2) F₁) = d * (Y : GL (Fin 2) F₁) * d⁻¹ := by
        have h' : e₁ p' = Y := by rw [hp', MulEquiv.apply_symm_apply]
        have := hdy p' hxp'
        rw [h'] at this
        exact this
      have hid : y * (a * (p : H) * a⁻¹) * y⁻¹ =
          pairMap h γ * (a * (y * (p : H) * y⁻¹) * a⁻¹) * (pairMap h γ)⁻¹ := by
        calc y * (a * (p : H) * a⁻¹) * y⁻¹ = (y * a) * (p : H) * (y * a)⁻¹ := by group
          _ = (pairMap h γ * a * y) * (p : H) * (pairMap h γ * a * y)⁻¹ := by rw [hyac]
          _ = _ := by group
      have hq'H : (q' : H) = pairMap h γ * (a * (q : H) * a⁻¹) * (pairMap h γ)⁻¹ := by
        show y * (p' : H) * y⁻¹ = _
        rw [← hpp']
        exact hid
      have hA : a * (q : H) * a⁻¹ = ((e₁.symm (slσ σ₁ (e₁ q)) : ↥K₁) : H) := by
        have := e_symm_conj₁ h (e₁ q)
        rwa [MulEquiv.symm_apply_apply] at this
      have hB := pairMap_conj_left h γ (slσ σ₁ (e₁ q))
      have hq'e : q' = e₁.symm (γ.1 * slσ σ₁ (e₁ q) * γ.1⁻¹) := by
        apply Subtype.ext
        rw [hq'H, hA, hB]
      have hZq : e₁ q' = γ.1 * slσ σ₁ (e₁ q) * γ.1⁻¹ := by
        rw [hq'e, MulEquiv.apply_symm_apply]
      have hGL := congrArg (fun w : SL2 F₁ => (w : GL (Fin 2) F₁)) hZq
      rw [hZ] at hGL
      have hσq : ((slσ σ₁ (e₁ q) : SL2 F₁) : GL (Fin 2) F₁) =
          glAut σ₁ d * (Y : GL (Fin 2) F₁) * (glAut σ₁ d)⁻¹ := by
        rw [slσ_coe, hQ, map_mul, map_mul, map_inv]
        rfl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hGL
      rw [hσq] at hGL
      rw [hGL]
      group
    have h2 := sign_lemma_cocycle h.odd₁.1 σ₁ h.σ₁_ord d hd γ.1 hsign
    rw [h1] at h2
    exact slNegOne_ne_one (LangC.two_ne_zero_of_odd h.odd₁.1) h2.symm

end LangClasses

end CFSG.GH74.GLS.IVK.Prod3
