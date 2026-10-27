module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3CaseA
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Res

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LocalAnalysis.GLTheoremA

variable {n : ℕ} {K : Type} [Field K]

theorem exists_injective_units_of_normalizes (h : UnitaryFieldData 2 n K) (h1 : 1 < n)
    (E T : Subgroup (MulAut (pI h))) (hE : IsPGroup 3 E)
    (hED : E ≤ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hT : IsPGroup 2 T)
    (hTD : T ⊓ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ ⊥)
    (hnorm : E ≤ Subgroup.normalizer (T : Set (MulAut (pI h)))) :
    ∃ θ : E →* Kˣ, Function.Injective θ := by
  classical
  have : Finite K := h.finite
  have hq := hq_aux h1
  set T₀ := T ⊓ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hT.to_le inf_le_left
  haveI : Nontrivial T₀ := (Subgroup.nontrivial_iff_ne_bot T₀).2 hTD
  haveI : Nontrivial (Subgroup.center T₀) := hT₀2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center T₀) := hT₀2.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center T₀) := by
    obtain ⟨m, hm⟩ := hZ2.exists_card_eq
    have h1lt : 1 < Nat.card (Subgroup.center T₀) := Finite.one_lt_card
    rw [hm] at h1lt ⊢
    have : m ≠ 0 := by
      rintro rfl
      simp at h1lt
    exact dvd_pow_self 2 this
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center T₀) 2 hdvd
  set t : MulAut (pI h) := ((y : T₀) : MulAut (pI h)) with ht
  have htT₀ : t ∈ T₀ := (y : T₀).2
  have htord : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy
  have htcomm : ∀ s ∈ T₀, s * t = t * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 y.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have htD : t ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := htT₀.2
  have htT : t ∈ T := htT₀.1
  have hφ : primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq t = RingEquiv.refl K := by
    have := htD
    rw [← ker_primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq, MonoidHom.mem_ker]
      at this
    exact this
  obtain ⟨s, hs1, hss, hts⟩ := exists_sq_eq_one_of_fieldFactor_eq_one h isPrimeFormGram_one
    (by norm_num) hq t htord hφ
  set g : GL (Fin 3) K := (s : GL (Fin 3) K) with hg
  have hgU : g ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := s.2.1
  obtain ⟨St, ψ, hStU, hgSt, hscal, hcrit, hker⟩ := exists_stabilizer_data h g hgU hss hs1
  set Ψ := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hΨ
  have htΨ : Ψ ⟨g, hgU⟩ = t := hts.symm
  have hcl : ∀ A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      Ψ A ∈ E → (A : GL (Fin 3) K) ∈ St := by
    intro A hAE
    set g' : GL (Fin 3) K := (A : GL (Fin 3) K) * g * (A : GL (Fin 3) K)⁻¹ with hg'
    have hg'U : g' ∈ primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      mul_mem (mul_mem A.2 hgU) (inv_mem A.2)
    have hΨg' : Ψ ⟨g', hg'U⟩ = Ψ A * t * (Ψ A)⁻¹ := by
      rw [← htΨ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hmemT : Ψ ⟨g', hg'U⟩ ∈ T := by
      rw [hΨg']
      exact (Subgroup.mem_normalizer_iff.1 (hnorm hAE) t).1 htT
    have hmemT₀ : Ψ ⟨g', hg'U⟩ ∈ T₀ := ⟨hmemT, ⟨_, rfl⟩⟩
    have hcomm := htcomm _ hmemT₀
    have hΨX : Ψ (⟨g', hg'U⟩ * ⟨g, hgU⟩ * ⟨g', hg'U⟩⁻¹ * ⟨g, hgU⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, htΨ, hcomm]
      group
    have hΨX' : primeFormPsi h isPrimeFormGram_one
        ⟨(⟨g', hg'U⟩ * ⟨g, hgU⟩ * ⟨g', hg'U⟩⁻¹ * ⟨g, hgU⟩⁻¹ :
          primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)), 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one]
      exact hΨX
    obtain ⟨-, c, hc, hXc⟩ := (primeFormPsi_eq_one_iff h isPrimeFormGram_one (by norm_num) _).1 hΨX'
    have hXc' : g' * g * g'⁻¹ * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) c := hXc
    have hmem : g' * g * g'⁻¹ ∈ St := by
      have : g' * g * g'⁻¹ = GeneralLinearGroup.scalar (Fin 3) c * g := by
        calc g' * g * g'⁻¹ = (g' * g * g'⁻¹ * g⁻¹) * g := by group
          _ = GeneralLinearGroup.scalar (Fin 3) c * g := by rw [hXc']
      rw [this]
      obtain ⟨hs, -⟩ := hscal c hc
      exact mul_mem hs hgSt
    have hg'St : g' ∈ St := hcrit g' hg'U hmem
    exact hcrit (A : GL (Fin 3) K) A.2 hg'St
  let ι : (E.comap Ψ) →* St := MonoidHom.codRestrict
    ((primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).subtype.comp
      (E.comap Ψ).subtype) St (fun a => hcl a.1 a.2)
  let ψ' : (E.comap Ψ) →* Kˣ := ψ.comp ι
  have hker' : ∀ a : E.comap Ψ, Ψ a = 1 → ψ' a = 1 := by
    intro a ha
    have hΨa : primeFormPsi h isPrimeFormGram_one
        ⟨(a : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)), 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_one, mul_one]
      exact ha
    obtain ⟨-, c, hc, hac⟩ := (primeFormPsi_eq_one_iff h isPrimeFormGram_one (by norm_num) _).1 hΨa
    obtain ⟨hs, hψ1⟩ := hscal c hc
    have : ι a = ⟨GeneralLinearGroup.scalar (Fin 3) c, hs⟩ := Subtype.ext hac
    simp only [ψ', MonoidHom.comp_apply, this, hψ1]
  have hψ' : ∀ a : E.comap Ψ, ψ' a = 1 → (Ψ a) ^ 4 = 1 := by
    intro a ha
    obtain ⟨ν, hν, h4⟩ := hker (ι a) ha
    rw [← map_pow]
    have hν4 : h.norm (((ν ^ 4 : Kˣ)) : K) = 1 := by
      rw [Units.val_pow_eq_pow_val]
      simp only [UnitaryFieldData.norm, map_pow] at hν ⊢
      rw [← mul_pow, hν, one_pow]
    have hΨ4 : primeFormPsi h isPrimeFormGram_one
        ⟨(a : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) ^ 4, 1⟩ = 1 := by
      rw [primeFormPsi_eq_one_iff h isPrimeFormGram_one (by norm_num)]
      exact ⟨rfl, ν ^ 4, hν4, h4⟩
    rw [primeFormPsi_apply, map_one, mul_one] at hΨ4
    exact hΨ4
  exact card_dvd_of_hom Ψ E hE hED ψ' hker' hψ'

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1015PU3Res

end
