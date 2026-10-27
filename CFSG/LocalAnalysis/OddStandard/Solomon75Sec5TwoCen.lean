module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoThm5
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseTools
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5TwoCover

public section

namespace CFSG.OddStandard.Solomon75

namespace Sec5Two

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.ABGLocalTools
  CFSG.OddStandard.Solomon75.AhatData

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X}
  {S : Sylow 2 ↥(normalizer ((zpowers z : Subgroup X) : Set X))}

theorem exists_conj_le_sylow' {K P E : Subgroup X} (hP : IsSylowOf 2 P K) (hEK : E ≤ K)
    (hE : IsPGroup 2 ↥E) : ∃ k ∈ K, ∀ x ∈ E, k * x * k⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE' : IsPGroup 2 ↥(E.subgroupOf K) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  have hQK : IsSylowOf 2 ((Q : Subgroup ↥K).map K.subtype) K := ⟨Q, rfl⟩
  obtain ⟨k, hk, hconj⟩ := hQK.exists_mem_conj hP
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [hconj]
  have : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rw [this]
  exact ⟨⟨x, hEK hx⟩, hQ hx, rfl⟩

theorem exists_four_le_sylow {H A Q : Subgroup X} (hn8 : 8 ≤ n) (hA : Sec5Comp X n H A)
    (hQ : IsSylowOf 2 Q A) :
    ∃ E : Subgroup X, E ≤ Q ∧ Open.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E := by
  have hrank := two_le_pRank_comp hn8 hA
  obtain ⟨E₀, hE₀A, hE₀, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) A
  have hE₀2 : IsPGroup 2 ↥E₀ := isPGroup_two_of_sq hE₀.2
  obtain ⟨k, -, hk⟩ := exists_conj_le_sylow' hQ hE₀A hE₀2
  let E : Subgroup X := E₀.map (MulAut.conj k).toMonoidHom
  have hEQ : E ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
  have hsq : ∀ e ∈ E, e * e = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have := sq_of_isElemAbelian hE₀ x hx
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc k * x * k⁻¹ * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
      _ = 1 := by rw [this]; group
  refine ⟨E, hEQ, isElemAbelian_of_sq hsq, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ Open.pRank 2 A := Nat.pow_le_pow_right (by norm_num) hrank

omit [Finite X] in
theorem exists_comp_ne {H : Subgroup X} (A : Subgroup X)
    (hne : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n H A₁ ∧ Sec5Comp X n H A₂ ∧ A₁ ≠ A₂) :
    ∃ A' : Subgroup X, Sec5Comp X n H A' ∧ A' ≠ A := by
  obtain ⟨A₁, A₂, h₁, h₂, h₁₂⟩ := hne
  by_cases e : A₁ = A
  · exact ⟨A₂, h₂, fun e' => h₁₂ (e.trans e'.symm)⟩
  · exact ⟨A₁, h₁, e⟩

theorem exists_sylow_le_cen {A : Subgroup X} {w : X} (hw2 : orderOf w = 2)
    (hnorm : w ∈ normalizer (A : Set X)) (hcomm : ∀ a ∈ A, ⁅a, w⁆ ∈ oddCoreOf A) :
    ∃ Q : Subgroup X, IsSylowOf 2 Q A ∧ Q ≤ centralizer ({w} : Set X) := by
  have hw_sq : w ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hw2]
    exact pow_orderOf_eq_one w
  have hwO : w ∈ normalizer (oddCoreOf A : Set X) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hnorm
  have hcov : ∀ a ∈ A, ∃ x ∈ centralizer ({w} : Set X), ∃ o ∈ oddCoreOf A, a = x * o := by
    intro a ha
    have hy : a⁻¹ * (w * a * w⁻¹) ∈ oddCoreOf A := by
      have h1 := hcomm a⁻¹ (A.inv_mem ha)
      have e : ⁅a⁻¹, w⁆ = a⁻¹ * (w * a * w⁻¹) := by simp only [commutatorElement_def]; group
      rwa [e] at h1
    obtain ⟨p, hp, hcent⟩ :=
      exists_mul_mem_centralizer_of_fixes_coset (odd_card_oddCoreOf A) hw_sq hwO hy
    exact ⟨a * p, hcent, p⁻¹, (oddCoreOf A).inv_mem hp, by group⟩
  exact exists_sylow_le_of_covers (le_normalizer_oddCoreOf A) (odd_card_oddCoreOf A)
    ((oddCoreOf_le A).trans Subgroup.le_normalizer) hcov

end Sec5Two

end CFSG.OddStandard.Solomon75
