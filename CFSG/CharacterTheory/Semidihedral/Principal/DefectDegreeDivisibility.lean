module

public import CFSG.CharacterTheory.TwoRankLowerBound.BlockDefectExistence
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterResidueCongruence
public import CFSG.CharacterTheory.Wreathed.CoprimeClassUnitRatio

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem localizedComplexIntegerResidue_eq_zero_of_padicValNat_lt
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] {z w : localizedComplexIntegerRing ideal}
    {M N : ℕ} (hM : M ≠ 0) (hlt : padicValNat p M < padicValNat p N)
    (h : (z : ℂ) * M = N * w) : localizedComplexIntegerResidue ideal z = 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨u, hu⟩ := pow_padicValNat_dvd (p := p) (n := N)
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := p) (n := M)
  have hm' : ¬ p ∣ m := fun hd => pow_succ_padicValNat_not_dvd hM (by
    rw [pow_succ]
    nth_rw 2 [hm]
    exact mul_dvd_mul_left _ hd)
  have hres : ∀ t : ℕ, localizedComplexIntegerResidue ideal (t : localizedComplexIntegerRing ideal)
      = 0 ↔ p ∣ t := fun t => by
    rw [map_natCast]
    exact CharP.cast_eq_zero_iff _ p t
  have hresp : localizedComplexIntegerResidue ideal (p : localizedComplexIntegerRing ideal) = 0 :=
    (hres p).mpr dvd_rfl
  obtain ⟨e, he⟩ : ∃ e, padicValNat p N = padicValNat p M + e + 1 :=
    ⟨padicValNat p N - padicValNat p M - 1, by omega⟩
  have hO : z * (m : localizedComplexIntegerRing ideal) =
      (p : localizedComplexIntegerRing ideal) ^ (e + 1) * u * w := by
    apply Subtype.ext
    push_cast
    apply mul_left_cancel₀ (pow_ne_zero (padicValNat p M) hp0)
    have hM' : (M : ℂ) = (p : ℂ) ^ padicValNat p M * m := by
      conv_lhs => rw [hm]
      push_cast
      ring
    have hN' : (N : ℂ) = (p : ℂ) ^ padicValNat p N * u := by
      conv_lhs => rw [hu]
      push_cast
      ring
    calc (p : ℂ) ^ padicValNat p M * ((z : ℂ) * m) = (z : ℂ) * M := by rw [hM']; ring
      _ = N * w := h
      _ = (p : ℂ) ^ padicValNat p M * ((p : ℂ) ^ (e + 1) * u * w) := by rw [hN', he]; ring
  have e' := congrArg (localizedComplexIntegerResidue ideal) hO
  rw [map_mul, map_mul, map_mul, map_pow, hresp, zero_pow (Nat.succ_ne_zero e), zero_mul,
    zero_mul] at e'
  exact (mul_eq_zero.mp e').resolve_right fun h0 => hm' ((hres m).mp h0)

theorem block_class_defect_witness_character_degree_dvd
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (label : basis.index) (D : Subgroup G) (hD : coefficientBlockDefect basis ideal p label D) :
    IsPGroup p D ∧ (∃ d : ℕ, Nat.card D = p ^ d) ∧
      ∀ d : ℕ, Nat.card D = p ^ d → d ≤ padicValNat p (Nat.card G) ∧
        ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
          p ^ (padicValNat p (Nat.card G) - d) ∣
            Module.finrank ℂ (basis.representation χ).vector := by
  have hp : p.Prime := Fact.out
  have hpg : IsPGroup p D := coefficientBlockDefect_isPGroup basis ideal hD
  refine ⟨hpg, hpg.exists_card_eq, fun d hd => ?_⟩
  obtain ⟨K, hK, hres⟩ := hD.1
  obtain ⟨x, hxK, S, hS⟩ := hK
  have hDS : Nat.card D = Nat.card S := by
    rw [hS]
    exact Subgroup.card_map_of_injective (Subgroup.centralizer ({x} : Set G)).subtype_injective
  have hdC : d = padicValNat p (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
    have e := hDS.symm.trans hd
    rw [Sylow.card_eq_multiplicity, Nat.factorization_def _ hp] at e
    exact (Nat.pow_right_injective hp.two_le e).symm
  have hGKC : (Subgroup.centralizer ({x} : Set G)).index *
      Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card G := by
    rw [← CFSG.LyonsUnitaryFour.card_conjClass_eq_index]
    exact CFSG.LyonsUnitaryFour.card_conjClass_mul_card_centralizer x
  have hindex0 : (Subgroup.centralizer ({x} : Set G)).index ≠ 0 :=
    (Subgroup.centralizer ({x} : Set G)).index_ne_zero_of_finite
  have hC0 : Nat.card (Subgroup.centralizer ({x} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hval : padicValNat p (Nat.card G) =
      padicValNat p (Subgroup.centralizer ({x} : Set G)).index + d := by
    rw [← hGKC, padicValNat.mul hindex0 hC0, hdC]
  refine ⟨by omega, fun χ hχ => ?_⟩
  have hsub : padicValNat p (Nat.card G) - d =
      padicValNat p (Subgroup.centralizer ({x} : Set G)).index := by omega
  rw [hsub]
  set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) K with hv
  have hsame : centralCharacterResidueHom basis ideal label =
      centralCharacterResidueHom basis ideal χ :=
    (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal label χ).mp
      ((coefficientBlock_mem_iff _ _ _ _).mp hχ)
  have hresχ : localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ v) ≠
      0 := by
    have e := hres
    rw [hsame] at e
    exact e
  have hscalar : (localCentralCharacterHom basis ideal χ v : ℂ) =
      ((Subgroup.centralizer ({x} : Set G)).index : ℂ) * (basis.representation χ).character x /
        (basis.representation χ).character 1 := by
    rw [localCentralCharacterHom_coe, hv, ← hxK]
    exact CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis x χ
  have hdeg : (basis.representation χ).character 1 =
      (Module.finrank ℂ (basis.representation χ).vector : ℂ) := Representation.char_one _
  have hfin0 : Module.finrank ℂ (basis.representation χ).vector ≠ 0 := by
    intro h0
    apply hresχ
    have hz : localCentralCharacterHom basis ideal χ v = 0 := by
      apply Subtype.ext
      rw [hscalar, hdeg, h0, Nat.cast_zero, div_zero]
      rfl
    rw [hz, map_zero]
  rw [padicValNat_dvd_iff_le hfin0]
  by_contra hlt
  replace hlt := not_le.mp hlt
  apply hresχ
  refine localizedComplexIntegerResidue_eq_zero_of_padicValNat_lt ideal p
    (w := ⟨_, complexAlgebraicInteger_mem_localized_ring ideal
      (algebraicCharacterValue (basis.representation χ) x)⟩) hfin0 hlt ?_
  rw [hscalar, hdeg]
  have hfin : (Module.finrank ℂ (basis.representation χ).vector : ℂ) ≠ 0 := by
    exact_mod_cast hfin0
  field_simp
  rfl

end CFSG.Semidihedral.Principal
