module

public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts

public section

namespace CFSG.OddStandard.ThmC

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC.T

theorem conclTwoClasses : ConclTwoClasses := by
  intro X _ _ T hT hC
  obtain ⟨-, hcase⟩ := hC
  rcases hcase with ⟨hD, -⟩ | ⟨-, hcard, hsq, -, -, -⟩
  ·
    have hTn : (T : Subgroup X).Normal := hD ▸ (inferInstance : (pCore 2 X).Normal)
    obtain ⟨z, hzc, hz2, hz1⟩ := IsT.exists_central_involution hT
    obtain ⟨x, hx2, hx1, hxc⟩ := IsT.exists_involution_not_mem hT
      (E := Subgroup.center (T : Subgroup X)) (fun y hy => IsT.sq_eq_one_of_mem_center hT hy)
    refine ⟨(z : X), (x : X), ?_, ?_, ?_⟩
    · exact orderOf_eq_two_iff_sq.2 ⟨by simpa using congrArg Subtype.val hz2,
        fun h => hz1 (Subtype.ext h)⟩
    · exact orderOf_eq_two_iff_sq.2 ⟨by simpa using congrArg Subtype.val hx2,
        fun h => hx1 (Subtype.ext h)⟩
    · intro hconj
      obtain ⟨g, hg⟩ := isConj_iff.1 hconj
      apply hxc
      rw [Subgroup.mem_center_iff]
      intro t
      have hts : g⁻¹ * (t : X) * g ∈ (T : Subgroup X) := by
        have := hTn.conj_mem (t : X) t.2 g⁻¹
        simpa using this
      have h1 := Subgroup.mem_center_iff.1 hzc ⟨g⁻¹ * (t : X) * g, hts⟩
      have h2 : g⁻¹ * (t : X) * g * (z : X) = (z : X) * (g⁻¹ * (t : X) * g) :=
        congrArg Subtype.val h1
      apply Subtype.ext
      show (t : X) * x = x * t
      rw [← hg]
      calc (t : X) * (g * z * g⁻¹) = g * (g⁻¹ * (t : X) * g * (z : X)) * g⁻¹ := by group
        _ = g * ((z : X) * (g⁻¹ * (t : X) * g)) * g⁻¹ := by rw [h2]
        _ = g * z * g⁻¹ * t := by group
  ·
    obtain ⟨v, hv2, hv1, hvD⟩ := IsT.exists_involution_not_mem hT
      (E := (pCore 2 X).subgroupOf (T : Subgroup X)) (fun y hy => Subtype.ext (hsq y hy))
    have hne : pCore 2 X ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hcard
      omega
    obtain ⟨u, hu⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    refine ⟨(u : X), ((v : ↥T) : X), ?_, ?_, ?_⟩
    · exact orderOf_eq_two_iff_sq.2 ⟨hsq u u.2, fun h => hu (Subtype.ext h)⟩
    · exact orderOf_eq_two_iff_sq.2 ⟨by simpa using congrArg Subtype.val hv2,
        fun h => hv1 (Subtype.ext h)⟩
    · intro hconj
      obtain ⟨g, hg⟩ := isConj_iff.1 hconj
      apply hvD
      rw [Subgroup.mem_subgroupOf, ← hg]
      exact (inferInstance : (pCore 2 X).Normal).conj_mem (u : X) u.2 g

end CFSG.OddStandard.ThmC
