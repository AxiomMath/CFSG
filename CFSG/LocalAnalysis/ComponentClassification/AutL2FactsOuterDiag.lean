module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsStated
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo Subgroup
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj projectiveSpecialLinearGroupEquivStatedProj)

theorem psl2_order_injective {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) / 2 = b * (b ^ 2 - 1) / 2) : a = b := by
  have hev : ∀ x : ℕ, 1 ≤ x → 2 ∣ x * (x ^ 2 - 1) := by
    intro x hx
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    have : (y + 1) * ((y + 1) ^ 2 - 1) = y * (y + 1) * (y + 2) := by
      rw [show (y + 1) ^ 2 - 1 = y * (y + 2) by
        rw [show (y + 1) ^ 2 = y * (y + 2) + 1 by ring]; omega]
      ring
    rw [this]
    exact Dvd.dvd.mul_right (Nat.even_mul_succ_self y).two_dvd _
  have h2 : a * (a ^ 2 - 1) = b * (b ^ 2 - 1) := by
    have := congrArg (· * 2) h
    rwa [Nat.div_mul_cancel (hev a ha), Nat.div_mul_cancel (hev b hb)] at this
  have ha2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    have h3 : a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
      have : a ^ 2 - 1 < b ^ 2 - 1 := by
        have := Nat.pow_lt_pow_left hab (two_ne_zero)
        omega
      exact Nat.mul_lt_mul_of_le_of_lt hab.le this hb
    omega
  · exact hab
  · exfalso
    have h3 : b * (b ^ 2 - 1) < a * (a ^ 2 - 1) := by
      have : b ^ 2 - 1 < a ^ 2 - 1 := by
        have := Nat.pow_lt_pow_left hab (two_ne_zero)
        omega
      exact Nat.mul_lt_mul_of_le_of_lt hab.le this ha
    omega

theorem congr_trans_apply {Y Z W : Type*} [Group Y] [Group Z] [Group W] (e₁ : Y ≃* Z)
    (e' : Z ≃* W) (α : MulAut Y) :
    MulAut.congr (e₁.trans e') α = MulAut.congr e' (MulAut.congr e₁ α) := by
  ext x
  simp [MulAut.congr_apply]

theorem card_eq_of_psl2_card_eq {F₁ F : Type} [Field F₁] [Finite F₁] [Field F] [Finite F]
    (h₁ : IsOddPrimePower (Nat.card F₁)) (h : IsOddPrimePower (Nat.card F))
    (hc : Nat.card (PSL2 F₁) = Nat.card (PSL2 F)) : Nat.card F₁ = Nat.card F := by
  rw [psl2_card_formula F₁ h₁, psl2_card_formula F h] at hc
  exact psl2_order_injective Finite.card_pos Finite.card_pos hc

theorem isOddPrimePower_of_ringChar {F₁ : Type} [Field F₁] [Finite F₁] (h2 : ringChar F₁ ≠ 2) :
    IsOddPrimePower (Nat.card F₁) := by
  have : Fintype F₁ := Fintype.ofFinite F₁
  obtain ⟨n, hp, hn⟩ := FiniteField.card F₁ (ringChar F₁)
  refine ⟨ringChar F₁, n, hp, hp.odd_of_ne_two h2, n.pos, ?_⟩
  rw [Nat.card_eq_fintype_card, hn]

theorem outerDiag_transport {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (e : Y ≃* PSL2 F) (σ : MulAut Y)
    (hσ : GSThmB.IsOuterDiagonalPSL2 σ) :
    (autEquiv e σ).right = 1 ∧ autEquiv e σ ∉ pGammaL2PSLRange F := by
  obtain ⟨⟨F₁, _, _, e₁, A, hA⟩, hnot⟩ := hσ
  constructor
  ·
    have hdet : ¬ IsSquare ((A : Matrix (Fin 2) (Fin 2) F₁).det) := by
      rintro ⟨μ, hμ⟩
      have hμ0 : μ ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hμ
        exact A.det_ne_zero hμ
      set s : GL (Fin 2) F₁ := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 μ hμ0)⁻¹
      set B : GL (Fin 2) F₁ := s * A
      have hs : ∀ X : GL (Fin 2) F₁, s * X = X * s := by
        intro X
        have hc : s ∈ Subgroup.center (GL (Fin 2) F₁) := by
          rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact ⟨_, rfl⟩
        exact (Subgroup.mem_center_iff.mp hc X).symm
      have hB : B ∈ StatedSL 2 F₁ := by
        rw [mem_statedSL_iff]
        simp only [B, s, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.det_mul, hμ, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
        rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, ← pow_two,
          inv_mul_cancel₀ (pow_ne_zero 2 hμ0)]
      have hconj : ∀ M : StatedSL 2 F₁, A * (M : GL (Fin 2) F₁) * A⁻¹ = B * M * B⁻¹ := by
        intro M
        calc A * (M : GL (Fin 2) F₁) * A⁻¹ = s * (A * M * A⁻¹) * s⁻¹ := by
              rw [hs, mul_inv_cancel_right]
          _ = B * M * B⁻¹ := by simp only [B, mul_inv_rev, mul_assoc]
      apply hnot
      refine ⟨e₁.symm (QuotientGroup.mk ⟨B, hB⟩)⁻¹, fun y => ?_⟩
      obtain ⟨M, hM⟩ := QuotientGroup.mk_surjective (e₁ y)
      have hy : y = e₁.symm (QuotientGroup.mk M) := by rw [hM, MulEquiv.symm_apply_apply]
      have h1 := hA M ⟨_, conj_mem_statedSL A M⟩ rfl
      rw [hy]
      apply e₁.injective
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
        inv_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hconj M
    have h2 : ringChar F₁ ≠ 2 := fun h => hdet (FiniteField.isSquare_of_char_two h _)
    have h₁ := isOddPrimePower_of_ringChar h2
    have hcard : Nat.card F₁ = Nat.card F := by
      apply card_eq_of_psl2_card_eq h₁ hodd
      rw [Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 F₁).toEquiv,
        ← Nat.card_congr e₁.toEquiv, Nat.card_congr e.toEquiv]
    have : Fintype F₁ := Fintype.ofFinite F₁
    have : Fintype F := Fintype.ofFinite F
    let θ : F₁ ≃+* F := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard])
    set e₂ : Y ≃* PSL2 F := e₁.trans (statedEquiv θ)
    have h₂ : autEquiv e₂ σ =
        SemidirectProduct.inl (Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map θ.toRingHom A)) := by
      rw [autEquiv_eq_iff, semilinearAction_inl, congr_trans_apply]
      apply congr_statedEquiv_conj θ A
      intro M N hN
      rw [MulAut.congr_apply]
      simp only [MulEquiv.trans_apply]
      exact hA M N hN
    rw [autEquiv_eq_conj e e₂, h₂]
    simp
  · intro hmem
    rw [← map_autEquiv_innAut e] at hmem
    obtain ⟨α, ⟨g, rfl⟩, hα⟩ := hmem
    have := (autEquiv e).injective hα
    apply hnot
    refine ⟨g⁻¹, fun y => ?_⟩
    rw [← this]
    simp [MulAut.conj_apply]

end CFSG.ComponentClassification.AutL2Facts
