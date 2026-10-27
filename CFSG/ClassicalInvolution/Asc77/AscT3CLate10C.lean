module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

theorem card_sl2_eq {F : Type} [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem card_dvd_mulAut_of_equiv_sl2 {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime)
    (hodd : Odd p) (hn : 1 ≤ n) (hF : Nat.card F = p ^ n) (h4 : 4 ≤ Nat.card F)
    {P : Type} [Group P] (e : P ≃* SL(2, F)) (A : Subgroup (MulAut P)) :
    Nat.card A ∣ Nat.card F * (Nat.card F ^ 2 - 1) * n := by
  have : Fact p.Prime := ⟨hp⟩
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, n, hp, hodd, hn, hF⟩
  have hc : 3 < Nat.card F := by omega
  have hperf : Group.IsPerfect P := CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4 e
  let e' : P ⧸ Subgroup.center P ≃* PSL2 F :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  let Φ : MulAut P →* MulAut (PSL2 F) := (MulAut.congr e').toMonoidHom.comp (centerDescend P)
  have hinj : Function.Injective (centerDescend P) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro α hα
    rw [MonoidHom.mem_ker] at hα
    rw [Subgroup.mem_bot]
    refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
    have h1 := congrArg (fun φ : MulAut (P ⧸ Subgroup.center P) =>
      φ (s : P ⧸ Subgroup.center P)) hα
    simp only [centerDescend_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    have := (Subgroup.center _).inv_mem h1
    simpa using this
  have hΦ : Function.Injective Φ := (MulAut.congr e').injective.comp hinj
  have h1 : Nat.card (A.map Φ) = Nat.card A := Subgroup.card_map_of_injective hΦ
  have h2 : Nat.card (A.map Φ) ∣ Nat.card (MulAut (PSL2 F)) := Subgroup.card_subgroup_dvd_card _
  have hbij : Function.Bijective (pGammaL2ToMulAutPSL2 F hK hc) :=
    ⟨pGammaL2ToMulAutPSL2_injective F hK hc,
      pGammaL2ToMulAutPSL2_surjective F (p := p) (f := n) hF hK hc⟩
  have h3 : Nat.card (MulAut (PSL2 F)) = Nat.card (PGammaL2 F) :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  have h5 : Nat.card (PGammaL2 F) = Nat.card (PGL2 F) * Nat.card (F ≃+* F) :=
    SemidirectProduct.card
  have h6 := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp F hF
  rw [← h1]
  refine h2.trans ?_
  rw [h3, h5, pgl2_card_formula]
  rw [show Nat.card (F ≃+* F) = n from h6.1]

theorem sixteen_dvd_pow_four_sub_one (a : ℕ) (ha : Odd a) : 16 ∣ (a * a) ^ 2 - 1 := by
  have h2 : a % 2 = 1 := Nat.odd_iff.mp ha
  have hpos : 1 ≤ (a * a) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos (by omega) (by omega))
  have h1 : (a * a) ^ 2 % 16 = 1 := by
    have : a % 16 = 1 ∨ a % 16 = 3 ∨ a % 16 = 5 ∨ a % 16 = 7 ∨ a % 16 = 9 ∨ a % 16 = 11 ∨
        a % 16 = 13 ∨ a % 16 = 15 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> simp [Nat.pow_mod, Nat.mul_mod, h]
  exact (Nat.modEq_iff_dvd' hpos).mp (by unfold Nat.ModEq; omega)

theorem odd_of_factorization_two_eq_three {p f : ℕ} (hodd : Odd p)
    (h : (p ^ f * ((p ^ f) ^ 2 - 1)).factorization 2 = 3) : Odd f := by
  by_contra hfe
  rw [Nat.not_odd_iff_even] at hfe
  obtain ⟨g, hg⟩ := hfe
  have haodd : Odd (p ^ g) := hodd.pow
  have hq : p ^ f = p ^ g * p ^ g := by rw [hg, pow_add]
  have hne : p ^ f * ((p ^ f) ^ 2 - 1) ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have h16 : 16 ∣ (p ^ g * p ^ g) ^ 2 - 1 := sixteen_dvd_pow_four_sub_one _ haodd
  have hdvd : 2 ^ 4 ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [hq]
    exact Dvd.dvd.mul_left (by norm_num; exact h16) _
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  omega

theorem card_dvd_eight_of_equiv_sl2 {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {P : Type} [Group P] (e : P ≃* SL(2, GaloisField p f))
    (h3 : (Nat.card P).factorization 2 = 3) (A : Subgroup (MulAut P)) (hA : IsPGroup 2 A) :
    Nat.card A ∣ 8 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hdvd := card_dvd_mulAut_of_equiv_sl2 (Fact.out : p.Prime) hodd
    (Nat.one_le_iff_ne_zero.mpr hf0) hF (by rw [hF]; omega) e A
  have hP : Nat.card P = p ^ f * ((p ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_sl2_eq, hF]
  rw [hP] at h3
  have hfodd : Odd f := odd_of_factorization_two_eq_three hodd h3
  rw [hF] at hdvd
  have hN0 : p ^ f * ((p ^ f) ^ 2 - 1) ≠ 0 := by
    intro h0
    rw [h0] at h3
    simp at h3
  have hf2 : f.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (by simpa [Nat.two_dvd_ne_zero] using hfodd.not_two_dvd_nat)
  have hN3 : (p ^ f * ((p ^ f) ^ 2 - 1) * f).factorization 2 = 3 := by
    rw [Nat.factorization_mul hN0 hf0]
    simp [h3, hf2]
  have hAne : Nat.card A ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    exact absurd (zero_dvd_iff.mp hdvd) (by
      have := hN0
      positivity)
  have hfin : Finite A := Nat.finite_of_card_ne_zero hAne
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  rw [hk] at hdvd ⊢
  have hne : p ^ f * ((p ^ f) ^ 2 - 1) * f ≠ 0 := by
    intro h0
    rw [h0] at hN3
    simp at hN3
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  rw [hN3] at this
  exact (pow_dvd_pow 2 this : 2 ^ k ∣ 2 ^ 3)

end CFSG.ClassicalInvolution.Asc77.T3CII
