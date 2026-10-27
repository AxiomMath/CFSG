module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCaseI
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FCaseII

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.A_pgroup (h : Sec4FSetup t L S z A B φ) : IsPGroup 2 ↥A := by
  intro a
  refine ⟨1, Subtype.ext ?_⟩
  simpa [pow_two] using h.A_sq a.2

theorem asc82Lemma47_of_frames (I : Sec4FInputs) (hsplit : Asc82Split47) : Asc82Lemma47 := by
  intro G _ _ t L S z hctx
  by_contra hnot
  obtain ⟨A, B, φ, hD⟩ := I.hAD G t L S z hctx
  have h : Sec4FSetup t L S z A B φ := sec4FSetup_of_data I hctx hnot hD
  obtain ⟨P, hAP, hPM, hP2, hmax⟩ := sec4F_exists_sylow_M h.A_pgroup
  by_cases hS : IsSylow2Of P ⊤
  · exact h.caseI hsplit hPM (hAP h.t_mem_A) hS
  · obtain ⟨x, hxN, hxP, hx2, hT2⟩ := sec4F_exists_normalizer_elt hP2 hS
    have hxM : x ∉ normalizer (A : Set G) := by
      intro hxM
      have hle : P ⊔ zpowers x ≤ normalizer (A : Set G) :=
        sup_le hPM (Subgroup.zpowers_le.mpr hxM)
      have heq : P ⊔ zpowers x = P := hmax _ le_sup_left hle hT2
      exact hxP (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    exact h.caseII ⟨hAP, hPM, hP2, hmax, hxN, hx2, hT2, hxM⟩

end CFSG.OddStandard.SmallF3.Omega
