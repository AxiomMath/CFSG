module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import Certificates.Certificate5190
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67RedAut
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporAbs
public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionDefs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Sporadic.Schreier CFSG.OddStandard CFSG.Certificates CFSG.Sporadic.Mathieu

theorem triples_false_M11 :
    ∀ (r s : ℕ) (a b y : ↥NativeSporadic.M11), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  have hgG : ∀ g ∈ [m11gA, m11gB], g ∈ NativeSporadic.M11 := by
    intro g hg
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact m11a.2
    · exact m11b.2
  have hok : Certificates.CF67.M11.m11CF67OK = true := Certificates.certificate5190
  obtain ⟨a0, b0, ha0, hb0, hab0, ha01, hb01, hcube, hC⟩ :=
    cf67_data hn m11Certificate hQ m11Certificate_originalSubgroup hgG
      (by norm_num : (3 : ℕ).Prime) hok
  have hcard : Nat.card ↥NativeSporadic.M11 = 7920 := m11_card
  have hsq : ∀ q : ℕ, q.Prime → Odd q → q ^ 2 ∣ Nat.card ↥NativeSporadic.M11 → q = 3 := by
    intro q hq hodd hd
    rw [hcard] at hd
    have hdv : q ∣ 7920 := (dvd_pow_self q two_ne_zero).trans hd
    have hp : ∀ p : ℕ, p.Prime → q ∣ p → q = p := fun p hp hd =>
      (Nat.prime_dvd_prime_iff_eq hq hp).1 hd
    have hf : (7920 : ℕ) = 2 * 2 * 2 * 2 * 3 * 3 * 5 * 11 := by norm_num
    rw [hf] at hdv
    simp only [Nat.Prime.dvd_mul hq, or_assoc] at hdv
    rcases hdv with h | h | h | h | h | h | h | h
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
    · obtain rfl := hp 5 (by norm_num) h
      omega
    · obtain rfl := hp 11 (by norm_num) h
      omega
  exact triples_false_of_sylow (by norm_num) ha0 hb0 hab0 ha01 hb01 hcube hC hsq

theorem noN2_M11 :
    ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .M11 → NoN2 Y := by
  intro Y _ hY
  obtain ⟨e⟩ := hY
  have e' : Y ≃* ↥NativeSporadic.M11 := e
  have hcard : Nat.card (MulAut ↥NativeSporadic.M11) ≤ 2 * Nat.card ↥NativeSporadic.M11 := by
    have := m11_mulAut_card
    omega
  exact NoN2.of_mulEquiv e' (noN2_of_outer_card m11_center_eq_bot' hcard triples_false_M11)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
