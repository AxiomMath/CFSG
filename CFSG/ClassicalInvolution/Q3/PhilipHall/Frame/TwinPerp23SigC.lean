module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.SigC

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_W_of_dstarAdj (hΩ : HypOmegaGen Ω) {K J : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hadj : dstarAdj Ω K J) :
    ∃ W₁ ∈ WSet Ω, z ∈ W₁ ∧ ∃ T ∈ DSet Ω W₁, IsSylow2In T J := by
  obtain ⟨hJΩ, h' | h'⟩ := hadj
  · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ⟩ :=
      CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hK h'
    exact ⟨W₁, hW₁, (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hR₁ hR₁K hz).2, T, hT, hTJ⟩
  · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J, hTK⟩ :=
      CFSG.ClassicalInvolution.Q8P.Asc77.Thompson.exists_W_of_mem_omegaStarNbr hΩ hJΩ h'
    exact ⟨W₁, hW₁, (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hW₁ hK hT hTK hz).2, R₁, hR₁, hR₁J⟩

theorem exists_conj_of_dstarComp (hΩ : HypOmegaGen Ω) {K X : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z)
    (hkey : ∀ W₁ ∈ WSet Ω, z ∈ W₁ → ∀ J ∈ Ω, (∃ T ∈ DSet Ω W₁, IsSylow2In T J) →
      ∃ g ∈ X, conjSub g K = J) :
    ∀ J ∈ dstarComp Ω K, ∃ g ∈ X, conjSub g K = J := by
  intro J hc
  induction hc with
  | refl => exact ⟨1, X.one_mem, conjSub_one K⟩
  | @tail J₁ J₂ _ hadj ih =>
    obtain ⟨h₁, hh₁, hJ₁⟩ := ih
    have hadj' : dstarAdj Ω K (conjSub h₁⁻¹ J₂) := by
      obtain ⟨hJ₂, h' | h'⟩ := hadj
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inl ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h' h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inr ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h' h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
    obtain ⟨W₁, hW₁, hzW₁, hT⟩ := exists_W_of_dstarAdj hΩ hK hz hadj'
    obtain ⟨h₂, hh₂, hJ₂⟩ := hkey W₁ hW₁ hzW₁ _ hadj'.1 hT
    refine ⟨h₁ * h₂, X.mul_mem hh₁ hh₂, ?_⟩
    rw [conjSub_mul, hJ₂, conjSub_conjSub_inv]

theorem le_of_mem_dstarComp (hΩ : HypOmegaGen Ω) {K X : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hKX : K ≤ X)
    (hkey : ∀ W₁ ∈ WSet Ω, z ∈ W₁ → ∀ J ∈ Ω, (∃ T ∈ DSet Ω W₁, IsSylow2In T J) →
      ∃ g ∈ X, conjSub g K = J) :
    ∀ J ∈ dstarComp Ω K, J ≤ X := by
  intro J hJ
  obtain ⟨g, hg, rfl⟩ := exists_conj_of_dstarComp hΩ hK hz hkey J hJ
  calc conjSub g K ≤ conjSub g X := conjSub_mono hKX
    _ = X := conjSub_eq_self_of_mem hg

theorem key_of_trans (hΩ : HypOmegaGen Ω) {K X W₀ : Subgroup G} {z : G}
    (hi : ∀ W₁ ∈ WSet Ω, z ∈ W₁ → ∃ c ∈ X, conjSub c W₀ = W₁)
    (hii : ∀ J ∈ Ω, (∃ T ∈ DSet Ω W₀, IsSylow2In T J) → ∃ m ∈ X, conjSub m K = J) :
    ∀ W₁ ∈ WSet Ω, z ∈ W₁ → ∀ J ∈ Ω, (∃ T ∈ DSet Ω W₁, IsSylow2In T J) →
      ∃ g ∈ X, conjSub g K = J := by
  rintro W₁ hW₁ hzW₁ J hJΩ ⟨T, hTD, hTJ⟩
  obtain ⟨c, hc, rfl⟩ := hi W₁ hW₁ hzW₁
  have hJ0Ω : conjSub c⁻¹ J ∈ Ω := hΩ.conjInvariant c⁻¹ J hJΩ
  have hT0D : conjSub c⁻¹ T ∈ DSet Ω W₀ := by
    refine ⟨Q3CL.Thompson.conjSub_mem_RSet hΩ hTD.1 c⁻¹, fun x hx => ?_⟩
    rw [mem_conjSub_iff, inv_inv] at hx
    have h1 := hTD.2 hx
    rw [Asc77.Thompson.conjSub_normalizer, mem_conjSub_iff] at h1
    simpa [mul_assoc] using h1
  obtain ⟨m, hm, hmK⟩ := hii _ hJ0Ω ⟨_, hT0D, hTJ.conj c⁻¹⟩
  refine ⟨c * m, X.mul_mem hc hm, ?_⟩
  rw [conjSub_mul, hmK, conjSub_conjSub_inv]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.SigC
