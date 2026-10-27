module

public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Defs

variable {G : Type} [Group G]

@[expose] def PspNoA2Syl (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∀ L ∈ Ω, ∀ l : G, IsUniqueInvolution L l → l ≠ z → l * z = z * l →
    ∃ P : Subgroup G, IsSylow2In P L ∧ P ≤ Subgroup.centralizer ({z} : Set G)

end Defs

section Residual


@[expose] def PspNoA2ResidualSyl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (K' : Subgroup G),
    PspSetting Ω K J S R T W z t K' → PspNbhdDouble Ω K z → PspNoA2Syl Ω z

end Residual

section Bridge


variable {G : Type} [Group G] [Finite G]

theorem PspSetting.noA2At_iff_syl [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') : PspNoA2At Ω K z ↔ PspNoA2Syl Ω z := by
  have hstd := hset.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hNC : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G) :=
    hset.bad.normalizer_eq_centralizer
  constructor
  · intro h L hL l hl hlz hcomm
    obtain ⟨-, -, R', hR', hR'L, hR'N⟩ := h L hL l hl hlz hcomm
    exact ⟨R', Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hL hR' hR'L, hNC ▸ hR'N⟩
  · intro h L hL l hl hlz hcomm
    obtain ⟨P, hP, hPC⟩ := h L hL l hl hlz hcomm
    refine ⟨hL, ?_, P, mem_RSet_of_isSylow2In hL hP, hP.1, ?_⟩
    · rintro rfl
      exact hlz (hstd.hz.eq hl).symm
    · rw [hNC]
      exact hPC

theorem pspNoA2Residual_of_syl (h : PspNoA2ResidualSyl) : PspNoA2Residual :=
  fun G _ _ _ Ω K J S R T W z t K' hset hD =>
    (hset.noA2At_iff_syl).mpr (h G Ω K J S R T W z t K' hset hD)

end Bridge

end CFSG.ClassicalInvolution.Q3.Q3AM
