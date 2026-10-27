module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2F4Inner
public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33E2GFE

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.LieType.Chevalley.E6SecondGraphFixed
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem graph_E6_not_isPGroup
    {G : Type} [Group G] {C J : Subgroup G} [Finite C] {P t : G}
    {k : Type} [Field k] [Finite k] {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hF4 : InvolutionCentralizerNotTwoGroup .F4)
    (hcan : CanonicalGraphFixedSubgroup C J P) (e : J ≃* adjointGroup Tag.F4 k)
    (hsec : SecondGraphFixedSubgroup C J P t e) {η : MulAut C}
    (hη : ∀ g : C, (η g : G) = P * g * P⁻¹) {α : MulAut C}
    (hcl : (∃ φ : MulAut C, φ * α * φ⁻¹ = η) ∨
      ∃ (htC : t ∈ C) (φ : MulAut C), φ * α * φ⁻¹ = MulAut.conj ⟨t, htC⟩ * η) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  obtain ⟨η₀, hη₀, -, hJC, hfix₀, -⟩ := hcan
  have hη₀η : η₀ = η := MulEquiv.ext fun g => Subtype.ext ((hη₀ g).trans (hη g).symm)
  rw [hη₀η] at hfix₀
  obtain ⟨htJ, hJC', η₁, hη₁, -, -, -, hfix₁, -, hord, -, -⟩ := hsec
  have hη₁η : η₁ = η := MulEquiv.ext fun g => Subtype.ext ((hη₁ g).trans (hη g).symm)
  rw [hη₁η] at hfix₁
  rcases hcl with ⟨φ, hφ⟩ | ⟨htC, φ, hφ⟩
  ·
    refine not_isPGroup_of_conj hφ ?_
    have hF : fixedPoints η = J.subgroupOf C := by
      ext g
      exact hfix₀ g
    rw [hF]
    exact fun hP => adjoint_not_isPGroup (τ := .F4) (Or.inr (Or.inl rfl)) hf hk
      (isPGroup_quot_of_equiv ((Subgroup.subgroupOfEquivOfLe hJC).trans e) hP)
  ·
    refine not_isPGroup_of_conj hφ ?_
    have hfix' : ∀ g : C, (MulAut.conj (⟨t, htC⟩ : C) * η) g = g ↔
        (g : G) ∈ J ∧ t * g = g * t := hfix₁
    set ι : adjointGroup Tag.F4 k →* C := (Subgroup.inclusion hJC).comp e.symm.toMonoidHom
      with hι
    have hιinj : Function.Injective ι :=
      (Subgroup.inclusion_injective hJC).comp e.symm.injective
    have hF : fixedPoints (MulAut.conj (⟨t, htC⟩ : C) * η) =
        (centralizer {e ⟨t, htJ⟩}).map ι := by
      ext g
      change (MulAut.conj (⟨t, htC⟩ : C) * η) g = g ↔ _
      rw [hfix' g, Subgroup.mem_map]
      constructor
      · rintro ⟨hgJ, hgt⟩
        refine ⟨e ⟨g, hgJ⟩, ?_, ?_⟩
        · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext hgt.symm
        · apply Subtype.ext
          simp [hι]
      · rintro ⟨h, hh, rfl⟩
        have hmem : ((ι h : C) : G) ∈ J := (e.symm h).2
        refine ⟨hmem, ?_⟩
        rw [mem_centralizer_singleton_iff] at hh
        have h1 : e.symm h * ⟨t, htJ⟩ = ⟨t, htJ⟩ * e.symm h := by
          apply e.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          exact hh
        exact (congrArg Subtype.val h1).symm
    rw [hF]
    exact fun hP => F4_centralizer_not_isPGroup hf hk hF4 _ hord
      (isPGroup_quot_of_equiv ((centralizer {e ⟨t, htJ⟩}).equivMapOfInjective ι hιinj).symm hP)

theorem not_isPGroup_of_derived {G : Type} [Group G] {C J : Subgroup G} [Finite C]
    {α β ψ : MulAut C} (hψ : (fixedSubgroup α).map ψ.toMonoidHom = fixedSubgroup β)
    (hJC : J ≤ C) (hder : ⁅fixedSubgroup β, fixedSubgroup β⁆ = J.subgroupOf C) {S : Type}
    [Group S] (eS : J ≃* S) (hS : _root_.commutator S = ⊤) (heven : 2 ∣ Nat.card S) :
    ¬ IsPGroup 2 (↥(fixedPoints α) ⧸ pPrimeCore 2 ↥(fixedPoints α)) := by
  have e₁ : ↥(fixedSubgroup α) ≃* ↥(fixedSubgroup β) :=
    ((fixedSubgroup α).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hψ)
  have hXF : J.subgroupOf C ≤ fixedSubgroup β := by
    rw [← hder]
    exact Subgroup.commutator_le_self _
  intro hP
  exact Ree.not_isPGroup_of_perfect_equiv hXF ((Subgroup.subgroupOfEquivOfLe hJC).trans eS) hS
    heven (isPGroup_quot_of_equiv e₁ hP)

theorem four_dvd_ordTwistedE6 {e : ℕ} (he : 1 ≤ e) : 4 ∣ ordTwistedE6 (2 ^ e) := by
  set q := 2 ^ e with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  set A := (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
    with hA
  have hdA : Nat.gcd 3 (q + 1) ∣ A := by
    have h1 : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := (Nat.gcd_dvd_right 3 (q + 1)).trans ⟨q - 1, by
      rw [show q ^ 2 = q * q by ring]
      zify [hq1, Nat.one_le_iff_ne_zero.2 (show q * q ≠ 0 by positivity)]
      ring⟩
    exact h1.trans (dvd_mul_left _ _)
  rw [ordTwistedE6, show q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) = q ^ 36 * A by rw [hA]; ring, Nat.mul_div_assoc _ hdA]
  refine Dvd.dvd.mul_right ?_ _
  rw [hq, ← pow_mul]
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ∣ 2 ^ (e * 36) := pow_dvd_pow 2 (by omega)

end CFSG.ComponentClassification.HarrisLit.L33.E2
