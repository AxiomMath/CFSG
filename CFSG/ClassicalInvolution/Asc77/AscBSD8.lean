module

public import CFSG.ClassicalInvolution.Asc77.AscBSD7
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofPSp
public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSp4
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.ClassicalInvolution.Asc77.BSC.BSD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD.Exotic (fundCorr_odd fundCorr_minus exists_inv_planeGroup)
open CFSG.ClassicalInvolution.RouteD (ModelFund planeGroupSet fundamentalSubgroups_psp_eq)
open CFSG.ClassicalInvolution.RouteD.SCRSp4 (mat_scalar_of_mem_center)
open CFSG.ClassicalInvolution.Asc77 (finrank_eq_eight_of_proj hproj_quadMinus
  fund_noncentral_modelUniv)
open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Symplectic.SpExtras
open scoped MatrixGroups

section Sp

variable {F : Type} [Field F]

theorem sp_four_centralSqCard : CentralSqCard (StatedSp 2 F) := by
  intro c₁ c₂ h₁ h₂ e₁ e₂
  have : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have key : ∀ {c : StatedSp 2 F}, c ∈ Subgroup.center (StatedSp 2 F) → c * c = 1 →
      c = 1 ∨ mat 2 F c = Matrix.scalar _ (-1 : F) := by
    intro c hc hc2
    obtain ⟨r, hr⟩ := mat_scalar_of_mem_center hc
    have hsq : Matrix.scalar (Fin 2 ⊕ Fin 2) (r * r) = Matrix.scalar (Fin 2 ⊕ Fin 2) 1 := by
      rw [map_mul, ← hr, ← map_mul, hc2, map_one, map_one]
    rcases mul_self_eq_one_iff.mp (Matrix.scalar_inj.mp hsq) with h | h
    · left
      apply mat_injective
      rw [hr, h, map_one, map_one]
    · right
      rw [hr, h]
  rcases key h₁ e₁ with h | h
  · exact Or.inl h
  rcases key h₂ e₂ with h' | h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (mat_injective (h.trans h'.symm)))

theorem planeGroup_eq_of_mem_inv (h2 : (2 : F) ≠ 0) {n : ℕ}
    {P P' : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P)
    (hP' : IsHyperbolicPlane P') {r : StatedSp n F} (hr : IsInvIn (planeGroup P) r)
    (hr' : IsInvIn (planeGroup P') r) : planeGroup P = planeGroup P' := by
  obtain ⟨i, hi, hm⟩ := exists_inv_planeGroup h2 hP
  obtain ⟨i', hi', hm'⟩ := exists_inv_planeGroup h2 hP'
  have h2' : r ^ 2 = 1 := by simpa [pow_two] using hr.2.1
  have e : r = i := hi.eq_of_orderOf_eq_two h2 hr.1 (orderOf_eq_prime h2' hr.2.2)
  have e' : r = i' := hi'.eq_of_orderOf_eq_two h2 hr'.1 (orderOf_eq_prime h2' hr.2.2)
  have : P = P' := by rw [← hm, ← hm', ← e, ← e']
  rw [this]

end Sp

section Models

variable {p : ℕ} [Fact p.Prime]


theorem fundTwoBound_psp_two : FundTwoBound p .PSp 2 := by
  intro e hp2 hq hadm R₁ R₂ R₃ h₁ h₂ h₃ r₁ r₂ r₃ hr₁ hr₂ hr₃ h12 h23
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have e₁ : R₁ ∈ planeGroupSet (GaloisField p e) 2 := by
    rw [← fundamentalSubgroups_psp_eq (p := p) (f := e) hadm]
    exact h₁
  have e₂ : R₂ ∈ planeGroupSet (GaloisField p e) 2 := by
    rw [← fundamentalSubgroups_psp_eq (p := p) (f := e) hadm]
    exact h₂
  have e₃ : R₃ ∈ planeGroupSet (GaloisField p e) 2 := by
    rw [← fundamentalSubgroups_psp_eq (p := p) (f := e) hadm]
    exact h₃
  obtain ⟨P₁, hP₁, rfl⟩ := e₁
  obtain ⟨P₂, hP₂, rfl⟩ := e₂
  obtain ⟨P₃, hP₃, rfl⟩ := e₃
  rcases eq_of_three_ratios sp_four_centralSqCard hr₁.2.1 hr₂.2.1 hr₃.2.1 h12 h23 with h | h | h
  · subst h
    exact Or.inl (planeGroup_eq_of_mem_inv h2 hP₁ hP₂ hr₁ hr₂)
  · subst h
    exact Or.inr (Or.inl (planeGroup_eq_of_mem_inv h2 hP₂ hP₃ hr₂ hr₃))
  · subst h
    exact Or.inr (Or.inr (planeGroup_eq_of_mem_inv h2 hP₁ hP₃ hr₁ hr₃))

end Models

end CFSG.ClassicalInvolution.Asc77.BSC.BSD
