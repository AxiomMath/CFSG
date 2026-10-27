module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93PGLType2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Leaves2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Sp4Rec
open scoped MatrixGroups

theorem ivk93l5_klein_sl3 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ u v : SL(3, F), u ^ 2 = 1 ∧ v ^ 2 = 1 ∧ (u * v) ^ 2 = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u * v ≠ 1 := by
  have hdet1 : (Matrix.diagonal ![(-1 : F), -1, 1]).det = 1 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]
  have hdet2 : (Matrix.diagonal ![(1 : F), -1, -1]).det = 1 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]
  have hne : (-1 : F) ≠ 1 := by
    intro h
    exact h2 (by linear_combination -h)
  obtain ⟨u, hu⟩ : ∃ u : SL(3, F),
      (u : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![(-1 : F), -1, 1] := ⟨⟨_, hdet1⟩, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : SL(3, F),
      (v : Matrix (Fin 3) (Fin 3) F) = Matrix.diagonal ![(1 : F), -1, -1] := ⟨⟨_, hdet2⟩, rfl⟩
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hu, Matrix.SpecialLinearGroup.coe_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hv, Matrix.SpecialLinearGroup.coe_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, hu, hv,
      Matrix.SpecialLinearGroup.coe_one, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  · intro h
    have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp [hu] at this
    exact hne this
  · intro h
    have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 1 1) h
    simp [hv] at this
    exact hne this
  · intro h
    have := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp [Matrix.mul_apply, Matrix.diagonal_apply, hu, hv] at this
    exact hne this

theorem ivk93l5_sl2_involution_unique {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {g h : SL(2, F)}
    (hg2 : g ^ 2 = 1) (hg1 : g ≠ 1) (hh2 : h ^ 2 = 1) (hh1 : h ≠ 1) : g = h := by
  have key : ∀ k : SL(2, F), k ^ 2 = 1 → k ≠ 1 → (k : Matrix (Fin 2) (Fin 2) F) = -1 := by
    intro k hk2 hk1
    have hsq : (k : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← pow_two, hk2, Matrix.SpecialLinearGroup.coe_one]
    rcases CFSG.SectionRank.Ccomm.eq_one_or_neg_one_of_sq_eq_one h2 k.2 hsq with h | h
    · exact absurd (Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_one]; exact h)) hk1
    · exact h
  exact Subtype.ext ((key g hg2 hg1).trans (key h hh2 hh1).symm)

theorem ivk93l5_mk_pPrimeCore_ne_one {X : Type*} [Group X] [Finite X] {y : X} (hy2 : y ^ 2 = 1)
    (hy1 : y ≠ 1) : QuotientGroup.mk' (pPrimeCore 2 X) y ≠ 1 := by
  intro h
  have hmem : y ∈ pPrimeCore 2 X := (QuotientGroup.eq_one_iff y).mp h
  have hord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  have hdvd : 2 ∣ Nat.card (pPrimeCore 2 X) := by
    have := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 X) hmem
    rwa [hord] at this
  exact absurd (Nat.Coprime.eq_one_of_dvd (CFSG.pPrimeCore_coprime_card (p := 2) (G := X)) hdvd)
    (by norm_num)

theorem Ivk93Cfg2.false_of_equiv_sl3 {J : Type} [Group J] [Finite J] {x : J} {q₁ q₂ : ℕ}
    {L₁ L₂ : Subgroup J} (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (e₂ : SL(3, F) ≃* ↥L₂) : False := by
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  obtain ⟨F', _, _, hq, ⟨f⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl₂
  have hodd' : Odd (Nat.card F') := by rw [hq]; exact h.odd₂
  have h2' : (2 : F') ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd'
  obtain ⟨u, v, hu2, hv2, huv2, hu1, hv1, huv1⟩ := ivk93l5_klein_sl3 h2
  let φ : SL(3, F) →* ↥L₂ ⧸ pPrimeCore 2 ↥L₂ :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥L₂)).comp e₂.toMonoidHom
  have hinv : ∀ g : SL(3, F), g ^ 2 = 1 → g ≠ 1 →
      (f.symm (φ g)) ^ 2 = 1 ∧ f.symm (φ g) ≠ 1 := by
    intro g hg2 hg1
    have hne : φ g ≠ 1 := by
      apply ivk93l5_mk_pPrimeCore_ne_one
      · rw [← map_pow, hg2, map_one]
      · exact fun h1 => hg1 (e₂.injective (h1.trans (map_one e₂).symm))
    refine ⟨?_, fun h1 => hne ?_⟩
    · rw [← map_pow, ← map_pow, hg2, map_one, map_one]
    · exact f.symm.injective (h1.trans (map_one f.symm).symm)
  obtain ⟨hu2', hu1'⟩ := hinv u hu2 hu1
  obtain ⟨hv2', hv1'⟩ := hinv v hv2 hv1
  obtain ⟨-, huv1'⟩ := hinv (u * v) huv2 huv1
  have heq : φ u = φ v := f.symm.injective (ivk93l5_sl2_involution_unique h2' hu2' hu1' hv2' hv1')
  apply huv1'
  rw [map_mul, ← heq, ← pow_two, ← map_pow, hu2, map_one, map_one]

theorem Ivk93Cfg2.false_of_equiv_sl2_sl3 {J : Type} [Group J] [Finite J] {x : J} {q₁ q₂ : ℕ}
    {L₁ L₂ : Subgroup J} (h : Ivk93Cfg2 x q₁ q₂ L₁ L₂) {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (_e₁ : SL(2, F) ≃* ↥L₁) (e₂ : SL(3, F) ≃* ↥L₂) : False :=
  h.false_of_equiv_sl3 hodd e₂

theorem ivk93_l52 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    Ivk93Empty2 (fun X _ => LieModel X .PSL 5 p f) := by
  intro p f hp hf hmod J _ _ hJ x hx q₁ q₂ L₁ L₂ h
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by rw [hF]; exact Nat.odd_iff.mpr (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have : Finite (StatedProj (StatedSL 5 F)) := Finite.of_equiv _ e.toEquiv
  have h' := h.of_equiv e
  obtain ⟨a, b, ha, hb, hab, ⟨e₁⟩, ⟨e₂⟩⟩ := h'.two_blocks h2 (by norm_num)
  have hab' : (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) := by omega
  rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h'.false_of_equiv_sl2_sl3 hodd e₁ e₂
  · exact h'.symm.false_of_equiv_sl2_sl3 hodd e₂ e₁

end CFSG.GH74.GLS.IVK.Proofs2
