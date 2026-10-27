module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Case0
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Case1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Seg27.Case2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

private theorem seg27_pair01_lift {S₀ S₁ X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))}
    (hX₀ : X₀ ≤ S₀) (hX₁ : X₁ ≤ S₁) (h : ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2) :
    ∃ g ∈ S₀ ⊓ S₁, orderOf g = 2 := by
  obtain ⟨g, hg, hg2⟩ := h
  exact ⟨g, inf_le_inf hX₀ hX₁ hg, hg2⟩

private theorem seg27_pair01_case2_same {X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))}
    {p₀ q₀ p₁ q₁ : Fin 8} (h02 : p₀ = p₁) (h13 : q₀ = q₁)
    (h₀ : Seg27Six X₀ p₀ q₀) (h₁ : Seg27Six X₁ p₁ q₁) :
    ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2 := by
  subst h02
  subst h13
  exact seg27_case2 h₀ h₁

private theorem seg27_pair01_case2_swap {X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))}
    {p₀ q₀ p₁ q₁ : Fin 8} (h03 : p₀ = q₁) (h12 : q₀ = p₁)
    (h₀ : Seg27Six X₀ p₀ q₀) (h₁ : Seg27Six X₁ p₁ q₁) :
    ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2 := by
  subst h03
  subst h12
  exact seg27_case2 h₀ h₁.symm

private theorem seg27_pair01_case1_pp {X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))}
    {p₀ q₀ p₁ q₁ : Fin 8} (h02 : p₀ = p₁) (h13 : q₀ ≠ q₁)
    (h₀ : Seg27Six X₀ p₀ q₀) (h₁ : Seg27Six X₁ p₁ q₁) :
    ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2 := by
  subst h02
  exact seg27_case1 h13 h₀ h₁

private theorem seg27_pair01_case1_pq {X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))}
    {p₀ q₀ p₁ q₁ : Fin 8} (h03 : p₀ = q₁) (h12 : q₀ ≠ p₁)
    (h₀ : Seg27Six X₀ p₀ q₀) (h₁ : Seg27Six X₁ p₁ q₁) :
    ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2 := by
  subst h03
  exact seg27_case1 h12 h₀ h₁.symm

private theorem seg27_pair01_case1_qp {X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))}
    {p₀ q₀ p₁ q₁ : Fin 8} (h12 : q₀ = p₁) (h03 : p₀ ≠ q₁)
    (h₀ : Seg27Six X₀ p₀ q₀) (h₁ : Seg27Six X₁ p₁ q₁) :
    ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2 := by
  subst h12
  exact seg27_case1 h03 h₀.symm h₁

private theorem seg27_pair01_case1_qq {X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))}
    {p₀ q₀ p₁ q₁ : Fin 8} (h13 : q₀ = q₁) (h02 : p₀ ≠ p₁)
    (h₀ : Seg27Six X₀ p₀ q₀) (h₁ : Seg27Six X₁ p₁ q₁) :
    ∃ g ∈ X₀ ⊓ X₁, orderOf g = 2 := by
  subst h13
  exact seg27_case1 h02 h₀.symm h₁.symm

theorem seg27_pair01 {S₀ S₁ X₀ X₁ : Subgroup (Equiv.Perm (Fin 8))} {p₀ q₀ p₁ q₁ : Fin 8}
    (h₀ : Seg27Six X₀ p₀ q₀) (h₁ : Seg27Six X₁ p₁ q₁)
    (hS₀ : S₀ ≤ alternatingGroup (Fin 8)) (hS₁ : S₁ ≤ alternatingGroup (Fin 8))
    (hcS₀ : Nat.card S₀ = 120) (hcS₁ : Nat.card S₁ = 120) (hX₀ : X₀ ≤ S₀) (hX₁ : X₁ ≤ S₁) :
    ∃ g ∈ S₀ ⊓ S₁, orderOf g = 2 := by
  by_cases h02 : p₀ = p₁
  · by_cases h13 : q₀ = q₁
    · exact seg27_pair01_lift hX₀ hX₁ (seg27_pair01_case2_same h02 h13 h₀ h₁)
    · exact seg27_pair01_lift hX₀ hX₁ (seg27_pair01_case1_pp h02 h13 h₀ h₁)
  · by_cases h03 : p₀ = q₁
    · by_cases h12 : q₀ = p₁
      · exact seg27_pair01_lift hX₀ hX₁ (seg27_pair01_case2_swap h03 h12 h₀ h₁)
      · exact seg27_pair01_lift hX₀ hX₁ (seg27_pair01_case1_pq h03 h12 h₀ h₁)
    · by_cases h12 : q₀ = p₁
      · by_cases h13 : q₀ = q₁
        · exact absurd (h12.symm.trans h13) h₁.ne
        · exact seg27_pair01_lift hX₀ hX₁ (seg27_pair01_case1_qp h12 h03 h₀ h₁)
      · by_cases h13 : q₀ = q₁
        · exact seg27_pair01_lift hX₀ hX₁ (seg27_pair01_case1_qq h13 h02 h₀ h₁)
        · exact seg27_case0 h02 h03 h12 h13 h₀ h₁ hS₀ hS₁ hcS₀ hcS₁ hX₀ hX₁

end CFSG.EvenSporadicStandard.HNRecog.Section3
