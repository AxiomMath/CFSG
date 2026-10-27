module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FA8FinRefl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFClassModelAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fa8fin_refl_cent (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {s : OGroup Q} (hs : s * s = 1) (hW : Module.finrank (ZMod 3) (commSp s) = 4)
    (hP : Module.finrank (ZMod 3) (fixSp s) = 2) (hsgn : quadSign (Q.restrict (fixSp s)) = -1)
    {R : Subgroup (OGroup Q)} (hΩ : R ≤ omegaGroup hQ) (hcent : ∀ g ∈ R, g * s = s * g)
    (hsq : ∀ g ∈ R, g * g = 1 ∨ g * g = s)
    (hpartner : ∀ g ∈ R, g ≠ 1 → g ≠ s → ∃ h ∈ R, h * g * h⁻¹ = s * g)
    {t₀ t₁ : OGroup Q} (h0 : t₀ * t₀ = 1) (h01 : invDim t₀ = 1) (h1 : t₁ * t₁ = 1)
    (h11 : invDim t₁ = 1) (hcomm : toProj Q (t₀ * s) = toProj Q (s * t₀))
    (hprod : toProj Q t₁ = toProj Q (t₀ * s)) : ∀ g ∈ R, t₀ * g = g * t₀ := by
  have hs4 : invDim s = 4 := hW
  have hts : t₀ * s = s * t₀ := by
    rcases toProj_eq_or_eq_piOrth hcomm with h | h
    · exact h
    · exfalso
      have hconj : t₀ * s * t₀⁻¹ = piOrth Q * s := by
        rw [h, mul_assoc, mul_inv_cancel_right]
      have h2 := two_mul_invDim_of_conj hQ hs hconj
      omega
  have hts2 : (t₀ * s) * (t₀ * s) = 1 := by
    calc (t₀ * s) * (t₀ * s) = t₀ * (s * t₀) * s := by group
      _ = t₀ * (t₀ * s) * s := by rw [hts]
      _ = (t₀ * t₀) * (s * s) := by group
      _ = 1 := by rw [h0, hs, one_mul]
  have hdt : invDim (t₀ * s) = 1 ∨ invDim (t₀ * s) = 5 := by
    rcases toProj_eq_or_eq_piOrth hprod with h | h
    · left
      rw [← h]
      exact h11
    · right
      have h3 := congrArg Prod.fst (invType_piOrth_mul hQ hts2)
      rw [← h] at h3
      have h4 : invDim t₁ = Module.finrank (ZMod 3) V - invDim (t₀ * s) := h3
      omega
  obtain ⟨a, ha⟩ : ∃ a : OGroup (Q.restrict (fixSp s)), t₀ = blockHom hs (a, 1) := by
    rcases fa8fin_refl_split hQ hs h0 hts h01 with h | h
    · exact h
    · exfalso
      omega
  intro g hg
  obtain ⟨p, hp, hp1⟩ := fa8fin_claimS hQ hs hW hP hsgn hΩ hcent hsq hpartner hg
  have hpa : a * p.1 = p.1 * a := by
    rcases hp1 with h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
      exact Subgroup.mem_center_iff.mp piOrth_mem_center a
  rw [ha, ← hp, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext hpa (by simp)

end CFSG.OddStandard.SmallF3.Omega
