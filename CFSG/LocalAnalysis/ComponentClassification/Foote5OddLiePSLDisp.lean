module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLRed
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLiePSLField

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.ComponentClassification.CatalogueBLinearSemilinear
open CFSG.ComponentClassification.CatalogueBGraphField

theorem commute_psl_of
    (hgr : ∀ {p f : ℕ} [Fact p.Prime], p ≠ 2 → 1 ≤ f → ∀ {n : ℕ}, 3 ≤ n →
      center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥ →
      ∀ (A : GL (Fin n) (GaloisField p f)) (σ : GaloisField p f ≃+* GaloisField p f),
      orderOf (graphFieldAction n (GaloisField p f) A σ) = 2 →
      ∀ R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f))),
      Odd (Nat.card R) →
      (∀ r ∈ R, r * graphFieldAction n _ A σ = graphFieldAction n _ A σ * r) →
      (∀ s, graphFieldAction n _ A σ s = s → Odd (orderOf s) → ∀ r ∈ R,
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁)
    (h3 : ∀ {p f : ℕ} [Fact p.Prime], p ^ f = 3 → ∀ {n : ℕ}, 3 ≤ n →
      center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥ →
      ∀ (A : GL (Fin n) (GaloisField p f)) (μ : (GaloisField p f)ˣ),
      A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ) →
      ∀ R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f))),
      Odd (Nat.card R) →
      (∀ r ∈ R, r * innerDiagonalAction n _ A = innerDiagonalAction n _ A * r) →
      (∀ s, innerDiagonalAction n _ A s = s → Odd (orderOf s) → ∀ r ∈ R,
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁)
    (hns : ∀ {p f : ℕ} [Fact p.Prime], p ≠ 2 → 1 ≤ f → ∀ {n : ℕ}, 3 ≤ n →
      center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥ →
      ∀ (A : GL (Fin n) (GaloisField p f)) (c : (GaloisField p f)ˣ),
      A * A = GeneralLinearGroup.scalar (Fin n) c → ¬ IsSquare (c : GaloisField p f) →
      ∀ R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f))),
      Odd (Nat.card R) →
      (∀ r ∈ R, r * innerDiagonalAction n _ A = innerDiagonalAction n _ A * r) →
      (∀ s, innerDiagonalAction n _ A s = s → Odd (orderOf s) → ∀ r ∈ R,
        MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁)
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) {n : ℕ} (hn : 3 ≤ n)
    (hZ : center (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)) = ⊥)
    (i : MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f))) (hi : orderOf i = 2)
    {R : Subgroup (MulAut (ProjectiveSpecialLinearGroup (Fin n) (GaloisField p f)))}
    (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * i = i * r)
    (hRc : ∀ s, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  set K := GaloisField p f with hK
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hcard : Nat.card K = p ^ f := GaloisField.card p f (by omega)
  have hoddK : Odd (Nat.card K) := by rw [hcard]; exact hpodd.pow
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero
    (CatalogueBHigherLinearInner.ringChar_ne_two_of_odd_card K hoddK)
  have hsq : i ^ 2 = 1 := by rw [← hi]; exact pow_orderOf_eq_one i
  have hne : i ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hi
    exact absurd hi (by norm_num)
  set e := CatalogueBLinearHigherB.nativeEquiv n K with he
  obtain ⟨-, hgen⟩ := LinearFlag.automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, hβ⟩ := hgen (MulAut.congr e.symm i)
  have hie : i = MulAut.congr e (MulAut.congr e.symm i) := by
    ext x
    simp
  rw [hβ] at hie
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hie
    subst hie
    by_cases hσ : σ = 1
    ·
      subst hσ
      have e1 : semilinearAction n K A 1 = innerDiagonalAction n K A := by
        rw [semilinearAction, map_one, mul_one]
      rw [e1] at hi hsq hne hRi hRc
      obtain ⟨-, -, c, hc⟩ := CatalogueBHigherLinearInner.inner_involution_projective_data n K
        (by omega) (Or.inl hn) A hne hsq
      have hAA : A * A = GeneralLinearGroup.scalar (Fin n) c := by rw [← sq]; exact hc
      by_cases hsqc : IsSquare (c : K)
      · obtain ⟨m, hm⟩ := hsqc
        have hm0 : m ≠ 0 := by
          rintro rfl
          exact c.ne_zero (by rw [hm, mul_zero])
        have hμ : c = Units.mk0 m hm0 * Units.mk0 m hm0 := Units.ext (by simp [hm])
        rw [hμ] at hAA
        have h3le : 3 ≤ p ^ f := by
          have hp3 : 3 ≤ p := by
            have := (Fact.out : p.Prime).two_le
            omega
          exact hp3.trans (Nat.le_self_pow (by omega) p)
        have hodd' : p ^ f % 2 = 1 := Nat.odd_iff.mp hpodd.pow
        by_cases hq3 : p ^ f = 3
        · exact h3 hq3 hn hZ A _ hAA R hRodd hRi hRc
        · exact commute_inner_split hp2 (by omega) hn hZ A _ hAA hRodd hRi hRc
      · exact hns hp2 hf hn hZ A c hAA hsqc R hRodd hRi hRc
    ·
      obtain ⟨heven, hfrob, H, hH⟩ :=
        odd_linear_field_involution_conjugacy n K p f Fact.out hpodd hf hcard (by omega)
          (Or.inl hn) A σ hσ hsq
      have : Fintype K := Fintype.ofFinite K
      have hσ2 : σ * σ = 1 := by
        obtain ⟨k, hk⟩ := heven
        refine RingEquiv.ext fun x => ?_
        change σ (σ x) = x
        rw [hfrob, hfrob, ← pow_mul, ← pow_add, show f / 2 + f / 2 = f by omega, ← hcard,
          Nat.card_eq_fintype_card, FiniteField.pow_card]
      refine commute_of_congr (innerDiagonalAction n K H)⁻¹ (fun R' hR'odd hR'i hR'c => ?_)
        hRodd hRi hRc
      have hcg : MulAut.congr (innerDiagonalAction n K H)⁻¹ (semilinearAction n K A σ) =
          pslFieldAut (Fin n) K σ := by
        rw [congr_eq_conj, hH]
        group
      rw [hcg] at hR'i hR'c
      have h1 := eq_one_field hn hZ h2 σ hσ hσ2 hR'odd hR'i hR'c
      intro r₁ h₁ r₂ h₂
      rw [h1 r₁ h₁, h1 r₂ h₂]
  ·
    rw [pow_one, CatalogueBLinearHigherB.congr_graphField] at hie
    subst hie
    exact hgr hp2 hf hn hZ A σ hi R hRodd hRi hRc

end CFSG.ComponentClassification.Foote5.OddLieCore
