module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BTClass
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3q510Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

local notation "𝓡" => sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)

theorem sec5z8_sq_mem (h : Sec510Ctx G t L S z r ρ B A φ)
    (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b) {x : G} (hx : x ∈ 𝓡) :
    x * x ∈ zpowers z ∨ x * x = t ∨ x * x = t * z := by
  have hEA : sec5p510_E t a b ≤ A := sec5p510_E_le_A h hs.ab
  by_cases hxE : x ∈ sec5p510_E t a b
  · refine Or.inl ?_
    rw [sec5p510_A_sq h (hEA hxE)]
    exact one_mem _
  rcases hs.R_cases with hRE | ⟨-, hrel⟩
  · exact absurd (hRE ▸ hx) hxE
  obtain ⟨hxa, hxb⟩ := hs.swap hrel x hx hxE
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 hx.1)
  have hxtc : x * t * x⁻¹ = t := by
    rw [hxt]
    group
  have hx2E : x * x ∈ sec5p510_E t a b := by
    have hidx : ((sec5p510_E t a b).subgroupOf 𝓡).index = 2 := hrel
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mul_self_mem_of_index_two hidx (⟨x, hx⟩ : ↥𝓡))
  have hfix : x * (x * x) * x⁻¹ = x * x := by group
  have hta : x * (t * a) * x⁻¹ = t * b := by
    calc x * (t * a) * x⁻¹ = (x * t * x⁻¹) * (x * a * x⁻¹) := by group
      _ = t * b := by rw [hxtc, hxa]
  have htb : x * (t * b) * x⁻¹ = t * a := by
    calc x * (t * b) * x⁻¹ = (x * t * x⁻¹) * (x * b * x⁻¹) := by group
      _ = t * a := by rw [hxtc, hxb]
  rw [sec5p510_mem_E_iff h hs.ab] at hx2E
  rcases hx2E with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · rw [h1]
    exact Or.inl (one_mem _)
  · exact Or.inr (Or.inl h1)
  · rw [h1] at hfix
    exact absurd (hfix.symm.trans hxa) hs.ab.ne
  · rw [h1] at hfix
    exact absurd (hxb.symm.trans hfix) hs.ab.ne
  · rw [h1, hta] at hfix
    exact absurd (mul_left_cancel hfix) (Ne.symm hs.ab.ne)
  · rw [h1, htb] at hfix
    exact absurd (mul_left_cancel hfix) hs.ab.ne
  · exact Or.inr (Or.inr (h1.trans (hs.ab.ab_eq h)))
  · refine Or.inl ?_
    rw [h1, hs.ab.prod]
    exact Subgroup.mem_zpowers z

end CFSG.OddStandard.SmallF3.Omega
