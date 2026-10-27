module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

@[expose] def TCKGroupBridge : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.SQTKTauCeti.KGroup X → CFSG.SectionRank.IsKGroupCat X

structure PushUpObstruction {G : Type} [Group G] (S P : Subgroup G) : Prop where
  sylow : IsSylowTwoOf S P
  charTwo : CharTwo P
  minParabolic : IsMinimalParabolic S P
  sqtk : CFSG.SectionRank.IsSQTKCat P
  noCharNormal : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ S → (R.subgroupOf S).Characteristic →
    ¬ P ≤ Subgroup.normalizer (R : Set G)

@[expose] def MinParabolicBlocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S P : Subgroup G), PushUpObstruction S P →
    ∃ L : Subgroup G, IsChi0Block P L ∧ ⁅L, CFSG.Quasithin.thompsonJ S⁆ = L ∧
      P = conjJoin S L ⊔ S ∧
      (conjJoin S L = L ∨ ∃ t ∈ S, L.map (MulAut.conj t).toMonoidHom ≠ L ∧
        conjJoin S L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
        ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)

@[expose] def BlockProduction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G), UniqueSetting G T M →
    IsGamma0 M H → CharTwo H → IsSylowTwoOf S (H ⊓ M) →
    ∃ P L : Subgroup G, S ≤ P ∧ P ≤ H ∧ ¬ P ≤ M ∧ IsMinimalParabolic S P ∧ CharTwo P ∧
      IsChi0Block P L ∧ ⁅L, CFSG.Quasithin.thompsonJ S⁆ = L ∧ P = conjJoin S L ⊔ S ∧
      (conjJoin S L = L ∨ ∃ t ∈ S, L.map (MulAut.conj t).toMonoidHom ≠ L ∧
        conjJoin S L = L ⊔ L.map (MulAut.conj t).toMonoidHom ∧
        ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥) ∧
      ∀ X : Subgroup G, S ≤ X → X < P → X ≤ M

theorem constrainedSetup_of_blockProduction (hBP : BlockProduction) : ConstrainedSetup := by
  intro G _ _ T M H hset hnb hns hH hc
  obtain ⟨S, hS⟩ := exists_isSylowTwoOf (H ⊓ M)
  obtain ⟨hSH, hSc, hlt⟩ := IsGamma.sylow_properties hset hH.isGamma hS
  obtain ⟨P, L, hSP, hPH, hPM, hmin, hcP, hblock, hth, hjoin, hblocks, hmaxInf⟩ :=
    hBP G T M H S hset hH hc hS
  obtain ⟨T', hST', hT'⟩ := exists_isSylowTwoOf_of_le hSc.1 hS.isPGroup
  have hset' : UniqueSetting G T' M :=
    ⟨hset.simple, hset.nonabelian, hset.qtke, hset.isSylowTwoOf_top_of_isSylowTwoOf_M hT',
      hset.maxLocal, hT'.le, hset.unique_of_isSylowTwoOf_M hT'⟩
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
  obtain ⟨hZ, hlt', -⟩ := hH.center_le_of_le_sylow hset hS hT' hST'
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
  exact ⟨T', P, S, L, hset', hnb, hns, hP0, hcP, hSP', hSPM, hST', hZ.trans inf_le_left,
    hlt'.ne, hpair, hblock, hnotle, hth, hjoin, hblocks, hmin, hmaxInf⟩


@[expose] def PositiveTwoCoreSQTK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    ∀ P : Subgroup G, pCoreOf 2 P ≠ ⊥ → CFSG.SectionRank.IsSQTKCat P

theorem blockProduction_of_minParabolicBlocks (hsqtk : PositiveTwoCoreSQTK)
    (hMB : MinParabolicBlocks) : BlockProduction := by
  intro G _ _ T M H S hset hH hc hS
  obtain ⟨hSH, hSc, hlt⟩ := IsGamma.sylow_properties hset hH.isGamma hS
  have hHM : ¬ H ≤ M := hH.isGamma.not_le
  have hQS : pCoreOf 2 H ≤ S := hSH.pCoreOf_le
  have hQ1 : pCoreOf 2 H ≠ ⊥ := hH.isGamma.1
  obtain ⟨P, ⟨hSP, hPH, hPM⟩, hPmin⟩ :=
    WellFounded.has_min (wellFounded_lt (α := Subgroup G))
      {X : Subgroup G | S ≤ X ∧ X ≤ H ∧ ¬ X ≤ M} ⟨H, hSH.le, le_rfl, hHM⟩
  have hSP' : IsSylowTwoOf S P :=
    isSylowTwoOf_of_card_eq hSP hSH.isPGroup
      (le_antisymm (card_le_twoPart hSP hSH.isPGroup) (hSH.card_eq ▸ twoPart_mono hPH))
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hQP : pCoreOf 2 H ≤ pCoreOf 2 P :=
    le_pCoreOf_of_normalizes (hQS.trans hSP) (hPH.trans hHN)
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
  have hcore : pCoreOf 2 P ≠ ⊥ := fun hbot => hQ1 (le_bot_iff.mp (hbot ▸ hQP))
  have hcP : CharTwo P := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast hQP) hx.2
    exact hQP (hc ⟨hPH hx.1, hxC⟩)
  have hnoChar : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ S → (R.subgroupOf S).Characteristic →
      ¬ P ≤ Subgroup.normalizer (R : Set G) := by
    intro R hR1 hRS hRc hPN
    exact hPM ((le_inf hPH hPN).trans
      ((hH.normalizer_inf_le_of_characteristic hset hc hS hR1 hRS hRc).trans inf_le_right))
  have hS1 : S ≠ ⊥ := fun h => hQ1 (le_bot_iff.mp (h ▸ hQS))
  have hmin : IsMinimalParabolic S P := by
    refine ⟨hSP', fun hPS => ?_, P ⊓ M, le_inf hSP hSc.1, lt_of_le_of_ne inf_le_left
      (fun h => hPM (h ▸ inf_le_right)), fun X hSX hXP => ?_⟩
    · refine hnoChar S hS1 le_rfl ?_ hPS
      rw [Subgroup.subgroupOf_self]
      infer_instance
    · by_contra hXM
      have hXM' : ¬ X ≤ M := fun hXM'' => hXM (le_inf hXP.le hXM'')
      exact hPmin X ⟨hSX, hXP.le.trans hPH, hXM'⟩ hXP
  have hsq : PushUpObstruction S P := ⟨hSP', hcP, hmin, hsqtk G T M hset P hcore, hnoChar⟩
  obtain ⟨L, hL⟩ := hMB G S P hsq
  have hmaxInf : ∀ X : Subgroup G, S ≤ X → X < P → X ≤ M := fun X hSX hXP => by
    by_contra hXM
    exact hPmin X ⟨hSX, hXP.le.trans hPH, hXM⟩ hXP
  exact ⟨P, L, hSP, hPH, hPM, hmin, hcP, hL.1, hL.2.1, hL.2.2.1, hL.2.2.2, hmaxInf⟩

end CFSG.QuasithinUnique
