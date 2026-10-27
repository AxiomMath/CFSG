module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporSpec2
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import Certificates.Certificate5191
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67RedAut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporAbs2
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionDefs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier CFSG.OddStandard CFSG.Certificates CFSG.Sporadic.Mathieu

theorem triples_false_M12 :
    ∀ (r s : ℕ) (a b y : ↥NativeSporadic.M12), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  have hgG : ∀ g ∈ [m12gA, m12gB], g ∈ NativeSporadic.M12 := by
    intro g hg
    have := m12_gens_mem g hg
    rwa [m12Certificate_originalSubgroup] at this
  have hok : Certificates.CF67.M12.m12CF67OK = true := Certificates.certificate5191
  obtain ⟨P, Es, hPcard, hk, hcover, hC⟩ :=
    cf67_gen_data hn m12Certificate hQ m12Certificate_originalSubgroup hgG
      (by norm_num : (3 : ℕ).Prime) hok
  have hcard : Nat.card ↥NativeSporadic.M12 = 95040 := m12_card
  have hsq : ∀ q : ℕ, q.Prime → Odd q → q ^ 2 ∣ Nat.card ↥NativeSporadic.M12 → q = 3 := by
    intro q hq hodd hd
    rw [hcard] at hd
    have hdv : q ∣ 95040 := (dvd_pow_self q two_ne_zero).trans hd
    have hp : ∀ p : ℕ, p.Prime → q ∣ p → q = p := fun p hp hd =>
      (Nat.prime_dvd_prime_iff_eq hq hp).1 hd
    have hf : (95040 : ℕ) = 2 * 2 * 2 * 2 * 2 * 2 * 3 * 3 * 3 * 5 * 11 := by norm_num
    rw [hf] at hdv
    simp only [Nat.Prime.dvd_mul hq, or_assoc] at hdv
    rcases hdv with h | h | h | h | h | h | h | h | h | h | h
    · obtain rfl := hp 2 (by norm_num) h
      exact absurd hodd (by decide)
    · obtain rfl := hp 2 (by norm_num) h
      exact absurd hodd (by decide)
    · obtain rfl := hp 2 (by norm_num) h
      exact absurd hodd (by decide)
    · obtain rfl := hp 2 (by norm_num) h
      exact absurd hodd (by decide)
    · obtain rfl := hp 2 (by norm_num) h
      exact absurd hodd (by decide)
    · obtain rfl := hp 2 (by norm_num) h
      exact absurd hodd (by decide)
    · exact hp 3 (by norm_num) h
    · exact hp 3 (by norm_num) h
    · exact hp 3 (by norm_num) h
    · obtain rfl := hp 5 (by norm_num) h
      omega
    · obtain rfl := hp 11 (by norm_num) h
      omega
  exact triples_false_of_sylow_cover (by norm_num) hPcard hk hcover hC hsq

theorem noN2_M12 :
    ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M12 → NoN2 Y := by
  intro Y _ hY
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥NativeSporadic.M12 := e
  have hcard : Nat.card (MulAut ↥NativeSporadic.M12) ≤ 2 * Nat.card ↥NativeSporadic.M12 := by
    have := m12_mulAut_card
    omega
  exact NoN2.of_mulEquiv e' (noN2_of_outer_card m12_center_eq_bot' hcard triples_false_M12)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
