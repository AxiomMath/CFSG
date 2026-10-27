module

public import CFSG.GH74.GLS.Stage4.T2Borel
public import CFSG.GH74.GLS.IVK.Lifted.SL2Aut
public import CFSG.GH74.GLS.Stage4.T2CentSL

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open CFSG.GH74.GLS.Stage4.Hex

theorem t6_aut_fix_u {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SL2 F)) (hα : ∀ c : F, α (sl2U c) = sl2U c) :
    ∃ s : F, ∀ g : SL2 F, α g = sl2U s * g * (sl2U s)⁻¹ := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨G, hG⟩ := CFSG.GH74.GLS.IVK.Lifted.exists_rep hodd h3 α
  obtain ⟨n, hp, hq⟩ := FiniteField.card F (ringChar F)
  have hcard : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hq]
  set σ := (CFSG.GH74.GLS.IVK.Lifted.gammaOf hodd h3 α).right with hσdef
  have hcond : ∀ A ∈ uSub F, G * Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map σ.toRingHom A) * G⁻¹ = Matrix.SpecialLinearGroup.toGL A := by
    intro A hA
    obtain ⟨c, rfl⟩ := mem_uSub.1 hA
    have h := hG (sl2U c)
    rw [hα] at h
    rw [CFSG.Semidihedral.MatrixCoverData.toGL_field_map]
    exact h.symm
  obtain ⟨hσ, A₀, hA₀, c, hGc⟩ :=
    CFSG.SL2MinimalFaithful.semilinear_centralizer_sylow hp hcard card_uSub G σ hcond
  obtain ⟨s, rfl⟩ := mem_uSub.1 hA₀
  refine ⟨s, fun g => ?_⟩
  apply Matrix.SpecialLinearGroup.toGL_injective
  have hmap : ∀ X : GL (Fin 2) F, Matrix.GeneralLinearGroup.map (σ : F →+* F) X = X := by
    intro X
    rw [hσ]
    rfl
  rw [hG g, hmap, hGc, map_mul, map_mul, map_inv]
  have e : ∀ S U X : GL (Fin 2) F, S * U * X * (S * U)⁻¹ = S * (U * X * U⁻¹) * S⁻¹ := by
    intro S U X
    group
  rw [e, Matrix.GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

theorem t6_cent_tSub {F : Type} [Field F] [Finite F] (h5 : 5 ≤ Nat.card F) (g : SL2 F)
    (hg : ∀ t ∈ tSub F, t * g = g * t) : g ∈ tSub F := by
  obtain ⟨a, ha⟩ := t2Bo_exists_sq_ne_one h5
  have h := hg (sl2D a) (sl2D_mem_tSub a)
  have e01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have e10 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  have hi : (a : F) * (a : F)⁻¹ = 1 := mul_inv_cancel₀ a.ne_zero
  have hsq : (a : F) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 ha
  refine ⟨?_, ?_⟩
  · have h0 : ((a : F) ^ 2 - 1) * (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
      linear_combination (a : F) * e01 + (g : Matrix (Fin 2) (Fin 2) F) 0 1 * hi
    exact (mul_eq_zero.1 h0).resolve_left hsq
  · have h0 : ((a : F) ^ 2 - 1) * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      linear_combination (-(a : F)) * e10 + (g : Matrix (Fin 2) (Fin 2) F) 1 0 * hi
    exact (mul_eq_zero.1 h0).resolve_left hsq

theorem t6_torus_inv_u {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (Y : Subgroup (SL2 F)) (hY : Y ≤ uSub F) (hT : ∀ t ∈ tSub F, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) :
    Y = ⊥ ∨ Y = uSub F := by
  by_cases h : ∃ c : F, c ≠ 0 ∧ sl2U c ∈ Y
  · right
    obtain ⟨c, hc0, hc⟩ := h
    have key : ∀ a : F, sl2U (a ^ 2 * c) ∈ Y := by
      intro a
      by_cases ha : a = 0
      · rw [ha, zero_pow two_ne_zero, zero_mul, sl2U_zero]
        exact Y.one_mem
      · have := hT (sl2D (Units.mk0 a ha)) (sl2D_mem_tSub _) _ hc
        rwa [t2A_conj_U] at this
    refine le_antisymm hY (fun y hy => ?_)
    obtain ⟨d, rfl⟩ := mem_uSub.1 hy
    obtain ⟨a, b, hab⟩ := CFSG.Semidihedral.OddFieldSL2.sum_two_squares F hodd (d / c)
    have hd : d = a ^ 2 * c + b ^ 2 * c := by
      field_simp at hab
      linear_combination -hab
    rw [hd, sl2U_add]
    exact Y.mul_mem (key a) (key b)
  · left
    push Not at h
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨c, rfl⟩ := mem_uSub.1 (hY hy)
    by_cases hc : c = 0
    · rw [hc, sl2U_zero]
      exact Subgroup.one_mem _
    · exact absurd hy (h c hc)

theorem t6_torus_inv_l {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (Y : Subgroup (SL2 F)) (hY : Y ≤ lSub F) (hT : ∀ t ∈ tSub F, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) :
    Y = ⊥ ∨ Y = lSub F := by
  by_cases h : ∃ c : F, c ≠ 0 ∧ sl2L c ∈ Y
  · right
    obtain ⟨c, hc0, hc⟩ := h
    have key : ∀ a : F, sl2L (a ^ 2 * c) ∈ Y := by
      intro a
      by_cases ha : a = 0
      · rw [ha, zero_pow two_ne_zero, zero_mul, sl2L_zero]
        exact Y.one_mem
      · have := hT (sl2D (Units.mk0 a ha)⁻¹) (sl2D_mem_tSub _) _ hc
        rwa [t2A_conj_L, inv_inv] at this
    refine le_antisymm hY (fun y hy => ?_)
    obtain ⟨d, rfl⟩ := mem_lSub.1 hy
    obtain ⟨a, b, hab⟩ := CFSG.Semidihedral.OddFieldSL2.sum_two_squares F hodd (d / c)
    have hd : d = a ^ 2 * c + b ^ 2 * c := by
      field_simp at hab
      linear_combination -hab
    rw [hd, sl2L_add]
    exact Y.mul_mem (key a) (key b)
  · left
    push Not at h
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨c, rfl⟩ := mem_lSub.1 (hY hy)
    by_cases hc : c = 0
    · rw [hc, sl2L_zero]
      exact Subgroup.one_mem _
    · exact absurd hy (h c hc)

theorem t6_pSub_torus {F : Type} [Field F] [Finite F] {p m : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ m) (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (B : Subgroup (SL2 F)) (hB : IsPGroup p ↥B)
    (hT : ∀ t ∈ tSub F, ∀ b ∈ B, t * b * t⁻¹ ∈ B) : B = ⊥ ∨ B = uSub F ∨ B = lSub F := by
  have := Fact.mk hp
  obtain ⟨Q, hBQ⟩ := hB.exists_le_sylow
  have hm : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hF
    omega
  have hpq : p ∣ Nat.card F := hF ▸ dvd_pow_self p hm
  have hQcard : Nat.card (Q : Subgroup (SL2 F)) = Nat.card F := by
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hndvd : ¬ p ∣ Nat.card F ^ 2 - 1 := by
      intro hd
      have h2 : p ∣ Nat.card F ^ 2 - 1 + 1 := by
        rw [Nat.sub_add_cancel h1]
        exact dvd_pow hpq two_ne_zero
      exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hd).mp h2))
    have hne1 : Nat.card F ^ 2 - 1 ≠ 0 := by
      have : 25 ≤ Nat.card F ^ 2 := by nlinarith
      omega
    have hne2 : Nat.card F ≠ 0 := by omega
    have hfac : (Nat.card F).factorization p = m := by
      rw [hF, Nat.Prime.factorization_pow hp]
      simp
    rw [Q.card_eq_multiplicity, t2C_card_sl2, Nat.factorization_mul hne2 hne1, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero, hfac]
    exact hF.symm
  have hcardF : Nat.card F = p ^ m := hF
  obtain ⟨g, hg⟩ := CFSG.SL2MinimalFaithful.exists_conj_unipotent_mem hp hcardF hQcard
  have hg' : ∀ t : F, g * sl2U t * g⁻¹ ∈ (Q : Subgroup (SL2 F)) := hg
  have hsurj : ∀ y ∈ (Q : Subgroup (SL2 F)), ∃ c : F, y = g * sl2U c * g⁻¹ := by
    let f : F → (Q : Subgroup (SL2 F)) := fun c => ⟨g * sl2U c * g⁻¹, hg' c⟩
    have hinj : Function.Injective f := by
      intro c c' h
      have h1 := congrArg Subtype.val h
      simp only [f] at h1
      exact sl2U_injective (mul_left_cancel (mul_right_cancel h1))
    have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hQcard])
    intro y hy
    obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  by_cases hbot : B = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hbot ((Subgroup.eq_bot_iff_forall B).2 hcon)
  obtain ⟨c, hc⟩ := hsurj b (hBQ hbB)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hb1
    rw [hc, sl2U_zero]
    group
  obtain ⟨a, ha⟩ := t2Bo_exists_sq_ne_one h5
  obtain ⟨c', hc'⟩ := hsurj _ (hBQ (hT (sl2D a) (sl2D_mem_tSub a) b hbB))
  obtain ⟨e00, e01, -, -⟩ := t2Bo_conj_sl2U_entries g c'
  obtain ⟨f00, f01, -, -⟩ := t2Bo_conj_sl2U_entries g c
  obtain ⟨k00, k01⟩ := t2Bo_sl2D_conj_entries a b
  have hc00 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 0) hc'
  have hc01 := congrArg (fun x : SL2 F => (x : Matrix (Fin 2) (Fin 2) F) 0 1) hc'
  rw [k00, hc, f00, e00] at hc00
  rw [k01, hc, f01, e01] at hc01
  have hprod : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    by_contra hne
    have hcc : c' = c := by
      have h : (c' - c) *
          ((g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0) = 0 := by
        linear_combination hc00
      exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hne)
    have hg0 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hne
    rw [hcc] at hc01
    apply ha
    have h : ((a : F) ^ 2 - 1) * (c * (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2) = 0 := by
      linear_combination hc01
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right (mul_ne_zero hc0 (pow_ne_zero 2 hg0)))
  rcases mul_eq_zero.1 hprod with h00 | h10
  · have hBl : B ≤ lSub F := by
      intro y hy
      obtain ⟨d, rfl⟩ := hsurj y (hBQ hy)
      obtain ⟨e00, e01, -, e11⟩ := t2Bo_conj_sl2U_entries g d
      exact ⟨by rw [e00, h00]; ring, by rw [e11, h00]; ring, by rw [e01, h00]; ring⟩
    rcases t6_torus_inv_l hodd B hBl hT with h | h
    · exact absurd h hbot
    · exact Or.inr h
  · have hBu : B ≤ uSub F := by
      intro y hy
      obtain ⟨d, rfl⟩ := hsurj y (hBQ hy)
      obtain ⟨e00, -, e10, e11⟩ := t2Bo_conj_sl2U_entries g d
      exact ⟨by rw [e00, h10]; ring, by rw [e11, h10]; ring, by rw [e10, h10]; ring⟩
    rcases t6_torus_inv_u hodd B hBu hT with h | h
    · exact absurd h hbot
    · exact Or.inl h

end CFSG.GH74.GLS.Stage4.Rest.T2
