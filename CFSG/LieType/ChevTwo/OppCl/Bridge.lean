module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

section Bridge

open CFSG.Blueprint TauCeti

theorem isClassicalTwoOrG2_cases
    {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : CFSG.AGLEmbedding.IsClassicalTwoOrG2 S) :
    (∃ (t : StatedLieTag) (n f : ℕ), (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨
        t = .POmegaMinus) ∧ StatedClassicalModel S t n 2 f) ∨
      (∃ f : ℕ, ChevalleyExceptionalModel S .G2 2 f) ∨
      Nonempty (S ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel S .PSU 3 3 1 := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨⟨i, hv⟩, hi, ⟨e⟩⟩
  ·
    rcases CFSG.AGLEmbedding.ParabAutIrr.classical_model_or_g2 d hd e with
      ⟨t, n, f, ht, hm⟩ | ⟨q, hv, hq, rfl⟩
    · exact .inl ⟨t, n, f, ht, hm⟩
    · have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
      have h3 : 3 ≤ 2 ^ q.exponent := by
        have h3 : 3 ≤ q.card := hr
        rwa [PrimePower.card_def, hq] at h3
      exact .inr (.inl ⟨q.exponent, ⟨Nat.prime_two, q.exponent_pos, rfl, h3⟩,
        CFSG.StandardType.ChevTwo.untwistedChevalleyModel_of_bridge
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv hq e⟩)
  ·
    rcases hn with rfl | rfl | rfl
    · exact .inl ⟨.PSL, 2, 2, Or.inl rfl,
        (CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e).statedClassicalModel
          (by simp [classicalTags])⟩
    · exact .inr (.inr (.inl ⟨e⟩))
    · exact .inl ⟨.PSL, 4, 1, Or.inl rfl,
        (CFSG.StandardType.ChevTwo.lieModel_psl_four_two_of_alternating_eight e).statedClassicalModel
          (by simp [classicalTags])⟩
  ·
    rcases hi with ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩
    · simp only at hiq
      subst hiq
      exact .inl ⟨.PSL, 3, 1, Or.inl rfl,
        (CFSG.StandardType.ChevTwo.lieModel_psl_three_two_of_A_one q hv hq e).statedClassicalModel
          (by simp [classicalTags])⟩
    · simp only at hiq
      subst hiq
      exact .inr (.inr (.inr
        (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hq e)))

end Bridge

end CFSG.LieType.ChevTwo.OppCl
