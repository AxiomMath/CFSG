module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCBranch
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitCUniqSA

public section

namespace CFSG.EvenSmallLie.OmegaEight.SplitC

open CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.Monster.B.Co2 (permOfArr)
open CFSG.Sporadic.Th (Rep)

theorem sylowT_plus_unique
    (F₁ F₂ : Subgroup (Equiv.Perm (Fin 360))) (h₁ : IsNSC OmegaEight.sylowT F₁ 64)
    (h₂ : IsNSC OmegaEight.sylowT F₂ 64) : F₁ = F₂ := by
  obtain ⟨W, hJ, hy, hcl, h⟩ := uniqPlus_check
  exact sylowT_plus_uniqueW hJ hy hcl h F₁ F₂ h₁ h₂

theorem sylowT_minus_unique
    (F₁ F₂ : Subgroup (Equiv.Perm (Fin 136))) (h₁ : IsNSC OmegaEightMinus.sylowT F₁ 64)
    (h₂ : IsNSC OmegaEightMinus.sylowT F₂ 64) : F₁ = F₂ := by
  obtain ⟨W, hJ, hy, hcl, h⟩ := uniqMinus_check
  exact OmegaEightMinus.sylowT_minus_uniqueW hJ hy hcl h F₁ F₂ h₁ h₂

theorem eq_Q_of_mulEquiv_plus
    {G : Type*} [Group G] {S₀ Q : Subgroup G} (e : S₀ ≃* OmegaEight.sylowT)
    (hQ : IsNSC S₀ Q 64) : ∀ F, IsNSC S₀ F 64 → F = Q :=
  fun _ hF => IsNSC.eq_of_equiv e sylowT_plus_unique hF hQ

theorem eq_Q_of_mulEquiv_minus
    {G : Type*} [Group G] {S₀ Q : Subgroup G} (e : S₀ ≃* OmegaEightMinus.sylowT)
    (hQ : IsNSC S₀ Q 64) : ∀ F, IsNSC S₀ F 64 → F = Q :=
  fun _ hF => IsNSC.eq_of_equiv e sylowT_minus_unique hF hQ

namespace Setting

open CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G] {ε : Eps} {t : G} {L H₀ U Q P S₀ : Subgroup G} {a : G}
  {ψ : V6 → G} {p : Fin 6 → G}

theorem Zset_cases_plus
    [Finite G] (hS : Setting ε t L H₀ U Q P S₀ a ψ p)
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (e : S₀ ≃* OmegaEight.sylowT) :
    (∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) ∨ ∀ v, v ∈ Zset t Q ψ :=
  hS.Zset_cases hG hnab (eq_Q_of_mulEquiv_plus e hS.isNSC_Q)

theorem Zset_cases_minus
    [Finite G] (hS : Setting ε t L H₀ U Q P S₀ a ψ p)
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (e : S₀ ≃* OmegaEightMinus.sylowT) :
    (∀ v, v ∈ Zset t Q ψ ↔ qfV ε v = 0) ∨ ∀ v, v ∈ Zset t Q ψ :=
  hS.Zset_cases hG hnab (eq_Q_of_mulEquiv_minus e hS.isNSC_Q)

end Setting

end CFSG.EvenSmallLie.OmegaEight.SplitC
