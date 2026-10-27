module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZLinRank
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZLinData
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution
import CFSG.LieType.SeitzGeneration.OutdiagScope
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {K : Type} [Field K] [Finite K]

private theorem natCast_eq_one_iff_dvd {p n : ℕ} (hn : 1 ≤ n) :
    ((n : ℕ) : ZMod p) = 1 ↔ p ∣ n - 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hn, Nat.cast_one, sub_eq_zero]

private theorem exists_lam {p : ℕ} (hp : p.Prime) {σ : K ≃+* K}
    (hK0 : p ∣ Nat.card (semilinearFixedSubfield σ) - 1)
    (hK9 : p = 3 → 9 ∣ Nat.card K - 1) :
    ∃ lam : K, IsPrimitiveRoot (lam ^ 3) p ∧ σ (lam ^ 3) = lam ^ 3 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set K₀ := semilinearFixedSubfield σ with hK₀
  have : Fintype K₀ˣ := Fintype.ofFinite _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := K₀ˣ) p (by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    exact hK0)
  have hz0 : IsPrimitiveRoot ((z : K₀) : K) p := by
    have h1 : IsPrimitiveRoot (z : K₀) p := by
      rw [← hz]
      exact IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.orderOf z)
    exact (IsPrimitiveRoot.map_iff_of_injective (f := K₀.subtype) Subtype.val_injective).2 h1
  have hzσ : σ ((z : K₀) : K) = ((z : K₀) : K) := ((z : K₀)).2
  by_cases h3 : p = 3
  · subst h3
    have : Fintype Kˣ := Fintype.ofFinite _
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    have h9 : 9 ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hK9 rfl
    obtain ⟨m, hm⟩ := h9
    have hpos : 0 < Nat.card Kˣ := Nat.card_pos
    have hgm : orderOf (g ^ m) = 9 := by
      rw [orderOf_pow' g (by rintro rfl; simp at hm <;> omega), hg, hm,
        Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (by
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp at hm <;> omega
          · exact h)]
    set lam : K := ((g ^ m : Kˣ) : K) with hlam
    have hl : IsPrimitiveRoot lam 9 := by
      rw [hlam, IsPrimitiveRoot.coe_units_iff, ← hgm]
      exact IsPrimitiveRoot.orderOf _
    have hl3 : IsPrimitiveRoot (lam ^ 3) 3 := hl.pow (by norm_num) (by norm_num)
    refine ⟨lam, hl3, ?_⟩
    obtain ⟨i, -, hi⟩ := hz0.eq_pow_of_pow_eq_one hl3.pow_eq_one
    rw [← hi, map_pow, hzσ]
  · refine ⟨((z : K₀) : K), ?_, by rw [map_pow, hzσ]⟩
    exact hz0.pow_of_coprime 3 ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm h3))

theorem z1Model_psl3 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hℓ2 : ℓ ≠ 2) : Z1Model p (projectiveSL 3 K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h).symm
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K ℓ] at h'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h')
  refine ⟨fun E hE => card_le_cube hp hp2 hpK hE, fun E hE hc => ?_⟩
  obtain ⟨-, hdvd, α, hαE, hαD⟩ := cube_facts hp hp2 hpK hE hc
  have hα1 : α ≠ 1 := fun h => hαD (h ▸ (linearAutGroup 3 K).one_mem)
  have hαp : orderOf α = p := orderOf_eq_prime (hE.2 α hαE) hα1
  have hαS : α ∈ semilinearAutGroup 3 K :=
    CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL.mem_semilinearAutGroup_of_odd
      (le_refl 3) (by rw [hαp]; exact hp.odd_of_ne_two hp2)
  obtain ⟨hpf, σ, hσ, ⟨h, -, hαh⟩, hcard0⟩ :=
    CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.higher_linear_prime_semilinear_field_descent'
      hℓ hf (le_refl 3) hK hp α hαS hαD hαp
  set q₀ := Nat.card (semilinearFixedSubfield σ) with hq₀
  have hKq : Nat.card K = q₀ ^ p := by
    rw [hK, hcard0, ← pow_mul, Nat.div_mul_cancel hpf]
  have hq₀1 : 1 ≤ q₀ := Nat.card_pos
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  have hK0 : p ∣ q₀ - 1 := by
    rw [← natCast_eq_one_iff_dvd hq₀1]
    have h1 := (natCast_eq_one_iff_dvd (p := p) hK1).2 hdvd
    rw [hKq, Nat.cast_pow, ZMod.pow_card] at h1
    exact h1
  have hK9 : p = 3 → 9 ∣ Nat.card K - 1 := by
    intro h3
    subst h3
    obtain ⟨t, ht⟩ := hK0
    have hq : q₀ = 3 * t + 1 := by omega
    rw [hKq, hq]
    exact ⟨3 * t ^ 3 + 3 * t ^ 2 + t, by
      rw [show (3 * t + 1) ^ 3 - 1 = 27 * t ^ 3 + 27 * t ^ 2 + 9 * t by
        rw [show (3 * t + 1) ^ 3 = 27 * t ^ 3 + 27 * t ^ 2 + 9 * t + 1 by ring]; omega]
      ring⟩
  have h4 : 4 ≤ q₀ := by
    have h2 : 2 ≤ q₀ := by
      have : Nontrivial (semilinearFixedSubfield σ) := inferInstance
      exact Finite.one_lt_card
    have hpos : 0 < q₀ - 1 := by omega
    have := Nat.le_of_dvd hpos hK0
    have := hp.two_le
    have : p ≠ 2 := hp2
    omega
  have hF : 4 ≤ Nat.card K := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    have hpos : 0 < Nat.card K - 1 := by omega
    have := Nat.le_of_dvd hpos hdvd
    have := hp.two_le
    omega
  obtain ⟨lam, hζ, hζσ⟩ := exists_lam hp hK0 hK9
  refine ⟨α, hαE, ?_, ?_⟩
  · rintro ⟨m, hm⟩
    exact hαD (hm ▸ CFSG.LieType.SeitzGeneration.conj_mem_linearAutGroup m)
  · rw [hαh]
    exact z1AutData_conj hp h (z1AutData_fieldAut hp hp2 h2K hF h4 hζ hζσ)

theorem z1LinBranch_holds : Z1LinBranch := by
  intro p Q hp hp2 hQ2 hQp M _ _ hcat
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  obtain ⟨i, hi, ⟨e₀⟩⟩ := hcat
  rcases i with _ | _ | ⟨⟨d, hv⟩⟩ | _
  · exact absurd hi id
  · exact absurd hi id
  swap
  · exact absurd hi id
  change d = .A 2 Q at hi
  subst hi
  let F := GaloisField Q.p Q.exponent
  let e : M ≃* projectiveSL 3 F := e₀.trans
    ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 Q hv).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F))
  have hcardF : Nat.card F = Q.p ^ Q.exponent := GaloisField.card Q.p Q.exponent Q.exponent_pos.ne'
  exact z1Model_congr hp e.symm
    (z1Model_psl3 Q.prime_p Q.exponent_pos hcardF hp hp2 (Ne.symm hQp) hQ2)

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin

end
