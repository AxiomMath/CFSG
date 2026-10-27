module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEMod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SE16
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82E16InnerT_of (hT6 : Asc82Tab6M) : Asc82E16InnerT := by
  intro G _ _ L F hL hFN hF hFC hinv
  obtain ⟨V, _, _, _, Q, hQ, hd, hs, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus hL
  have hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := ⟨hd, hs⟩
  have hLperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have key := innerOn_of_model asc82E16Model hm e hLperf hFN hF hFC (fun f hf hne => by
    have hf2 : orderOf f = 2 := orderOf_eq_prime (hF.1.2 f hf) hne
    rcases hinv f hf hf2 with hin | ⟨α, h3⟩
    · refine Or.inl ⟨(innerOn_iff_simInOmegaStar hm e hLperf (hFN hf)).mp hin, ?_⟩
      have hnot : f ∉ Subgroup.centralizer (L : Set G) := by
        intro hc
        apply hne
        have hbot : f ∈ F ⊓ Subgroup.centralizer (L : Set G) := ⟨hf, hc⟩
        rw [hFC] at hbot
        exact Subgroup.mem_bot.mp hbot
      exact simHasDim_of_inducesTypeSome hm e (hFN hf)
        ((hT6.inner_iff G L hL f hf2 (hFN hf)).mp ⟨hin, hnot⟩)
    · exact Or.inr (simHasDim_of_inducesTypeSome hm e (hFN hf) h3))
  intro f hf
  exact (innerOn_iff_simInOmegaStar hm e hLperf (hFN hf)).mpr (key f hf)

theorem asc82Lemma91_of_tab (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h66 : Asc82Lemma66)
    (h82 : Asc82Lemma82) (hT6 : Asc82Tab6M) (hB8 : Asc82Sec8B) : Asc82Lemma91 :=
  asc82Lemma91_of_inputs h36 h37 h66 h82 hT6 hB8 (asc82E16InnerT_of hT6)

end CFSG.OddStandard.SmallF3.Omega
