module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Interfaces

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

@[expose] def ConstrainedSetupAt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G), UniqueSetting G T M →
    ¬ fusionIsBenderGroup G → ¬ UniqueSmallModel G → IsGamma0 M H → CharTwo H →
    IsSylowTwoOf S (H ⊓ M) → S ≤ T →
    ∃ P L : Subgroup G, P ≤ H ∧ ConstrainedSetting G T M P S L

theorem constrainedSetupAt_of_blockProduction (hBP : BlockProduction) : ConstrainedSetupAt := by
  intro G _ _ T M H S hset hnb hns hH hc hS hST
  obtain ⟨hSH, hSc, hlt⟩ := IsGamma.sylow_properties hset hH.isGamma hS
  obtain ⟨P, L, hSP, hPH, hPM, hmin, hcP, hblock, hth, hjoin, hblocks, hmaxInf⟩ :=
    hBP G T M H S hset hH hc hS
  have hT : IsSylowTwoOf T M := hset.isSylowTwoOf_M
  have hQS : pCoreOf 2 H ≤ S := hSH.pCoreOf_le
  have hQP : pCoreOf 2 H ≤ pCoreOf 2 P :=
    le_pCoreOf_of_normalizes (hQS.trans hSP)
      (hPH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hcore : pCoreOf 2 P ≠ ⊥ := fun hbot =>
    hH.isGamma.1 (le_bot_iff.mp (hbot ▸ hQP))
  have hpair : IsWitnessPair M S P := ⟨hSc, hSP, hcore, hcP, hPM⟩
  have hcase : IsGamma2 M H ∨ (IsGammaU M H ∧ IsGammaTop M P) := by
    rcases hH with hU | h2
    · exact Or.inr ⟨hU, hpair.isGammaTop_of_le le_rfl hcore
        (fun V hV => hU.1.card_le_of_isSylowTwoOf hSH hV)⟩
    · exact Or.inl h2
  obtain ⟨hP0, hSP', hSPM, -, -⟩ :=
    hH.overgroup_of_sylow_le hset hS hpair.isGamma hSP hcase
  obtain ⟨hZ, hlt', -⟩ := hH.center_le_of_le_sylow hset hS hT hST
  have hnotle : ¬ L ≤ M := by
    intro hLM
    obtain ⟨-, -, K, hSK, hKP, hK⟩ := hmin
    have hPMK : P ⊓ M ≤ K := hK _ (le_inf hSP (hSc.1)) (lt_of_le_of_ne inf_le_left
      (fun h => hPM (h ▸ inf_le_right)))
    have hLK : L ≤ K := fun x hx => hPMK ⟨hblock.1.2.1 hx, hLM hx⟩
    have hjK : conjJoin S L ≤ K := by
      refine iSup_le fun s => ?_
      calc L.map (MulAut.conj (s : G)).toMonoidHom ≤ K.map (MulAut.conj (s : G)).toMonoidHom :=
            Subgroup.map_mono hLK
        _ = K := map_conj_eq_self_of_mem (hSK s.2)
    exact absurd (hjoin ▸ sup_le hjK hSK) (not_le_of_gt hKP)
  exact ⟨P, L, hPH, hset, hnb, hns, hP0, hcP, hSP', hSPM, hST, hZ.trans inf_le_left,
    hlt'.ne, hpair, hblock, hnotle, hth, hjoin, hblocks, hmin, hmaxInf⟩

end CFSG.QuasithinUnique
