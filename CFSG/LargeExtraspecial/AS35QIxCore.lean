module

public import CFSG.LargeExtraspecial.AS35QIxEnd4
public import CFSG.LargeExtraspecial.AS35QIxBad4
public import CFSG.LargeExtraspecial.AS35QIxEnd3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxLift

variable (T : IxLift S)

theorem comm_zeta (hS : S.SixHyp) : ∀ m ∈ S.Mbar, m * T.ζ = T.ζ * m := by
  by_contra h
  push Not at h
  obtain ⟨m₁, hm₁, hm₁ζ⟩ := h
  obtain ⟨B, rfl⟩ := T.exists_bad hS hm₁ hm₁ζ
  obtain ⟨a, ha, haa, hat, hax, haρ, hg, hgζ⟩ := B.exists_astar hS
  have haζ : S.ρ ⟨a, ha⟩ * B.ζ ≠ B.ζ * S.ρ ⟨a, ha⟩ := by
    rw [haρ]
    exact B.F_not_comm
  obtain ⟨k, hk⟩ := B.exists_conj_mem_M0 hS ha haa haζ
  obtain ⟨hyM, hyζ⟩ := B.mem_M0.mp hk
  have hyy : (k⁻¹ * a * k) * (k⁻¹ * a * k) = 1 := by
    rw [show k⁻¹ * a * k * (k⁻¹ * a * k) = k⁻¹ * (a * a) * k by group, haa]
    group
  have hy1 : k⁻¹ * a * k ≠ 1 := by
    intro h
    apply haζ
    have ha1 : a = 1 := by
      calc a = k * (k⁻¹ * a * k) * k⁻¹ := by group
        _ = 1 := by rw [h]; group
    subst ha1
    rw [show (⟨1, ha⟩ : S.M) = 1 from rfl, map_one, one_mul, mul_one]
  have hPy : PropP (k⁻¹ * a * k) := by
    rcases B.isConj_of_involution hS hyM hyζ hyy hy1 with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.mp h
      rw [← hc]
      exact B.propP_z.conj c
    · obtain ⟨c, hc⟩ := isConj_iff.mp h
      rw [← hc]
      exact (B.propP_zt hS).conj c
  have hPa : PropP a := by
    have h := hPy.conj k
    rwa [show k * (k⁻¹ * a * k) * k⁻¹ = a by group] at h
  exact B.not_propP hS ha haa hat hax haρ hg hgζ hPa

end IxLift

end CFSG.LargeExtraspecial.AS35QIx
