module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem untwistedChevalleyModel_of_bridge {τ : Tag} {c : PrimePower → LieTypeIndex}
    (hB : Even.UntwistedBridgeAll τ c) {X : Type} [Group X] {q : PrimePower}
    {hv : (c q).Valid} (e : X ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    UntwistedChevalleyModel X τ (q.p ^ q.exponent) := by
  obtain ⟨K, _, _, -, hK⟩ := exists_field_card q.p q.exponent q.prime_p q.exponent_pos
  obtain ⟨b⟩ := hB q hv K (by rw [hK, PrimePower.card_def])
  exact ⟨K, inferInstance, inferInstance, hK, ⟨e.trans b.symm⟩⟩

theorem blueprintLieModel_of_models
    {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ} (hm : CFSG.Models.LieModel X t n p f) :
    CFSG.Blueprint.LieModel X t n p f := by
  obtain ⟨hadm, hcl | ⟨h0, ⟨idx, hv⟩, hnames, ⟨e⟩⟩⟩ := hm
  · refine Or.inl ⟨?_, hcl⟩
    cases t <;> first | decide | exact hcl.2.elim
  · subst h0
    cases t
    all_goals first
      | (exfalso; cases idx <;> simp only [CFSG.Models.NamesTag] at hnames; done)
      | skip
    case G2 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm, untwistedChevalleyModel_of_bridge
        (c := LieTypeIndex.G2) Even.chevalleyBridgesAll.g2 e⟩)
    case F4 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm, untwistedChevalleyModel_of_bridge
        (c := LieTypeIndex.F4) Even.chevalleyBridgesAll.f4 e⟩)
    case E6 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm, untwistedChevalleyModel_of_bridge
        (c := LieTypeIndex.E6) Even.chevalleyBridgesAll.e6 e⟩)
    case E7 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm, untwistedChevalleyModel_of_bridge
        (c := LieTypeIndex.E7) Even.chevalleyBridgesAll.e7 e⟩)
    case E8 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm, untwistedChevalleyModel_of_bridge
        (c := LieTypeIndex.E8) Even.chevalleyBridgesAll.e8 e⟩)
    case twistedE6 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm, twistedChevalleyModel_of_bridge (t := .E6)
        (c := LieTypeIndex.twistedE6) Even.chevalleyBridgesAll.twistedE6 e⟩)
    case trialityD4 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i q
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inl ⟨rfl, by decide, hadm, twistedChevalleyModel_of_bridge (t := .D4)
        (c := LieTypeIndex.trialityD4) Even.chevalleyBridgesAll.trialityD4 e⟩)
    case twistedB2 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i m
      obtain ⟨rfl, rfl⟩ := hnames
      obtain ⟨K, _, _, hchar, hK⟩ := exists_field_card 2 (2 * m + 1) Nat.prime_two (by omega)
      have e₂ : ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩ ≃* CFSG.Blueprint.suzukiGroup m K :=
        (BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).trans
          (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).symm
      have h3 : 3 ≤ 2 * m + 1 := hadm.2.2.2.2.2
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, m, by omega, K, inferInstance, inferInstance,
        rfl, hK, ⟨e.trans e₂⟩⟩))
    case twistedG2 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i m
      obtain ⟨rfl, rfl⟩ := hnames
      obtain ⟨K, _, _, hchar, hK⟩ := exists_field_card 3 (2 * m + 1) Nat.prime_three (by omega)
      obtain ⟨b⟩ := reeG2Bridge m hv K hK
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, m, rfl, K, inferInstance, inferInstance,
        hK, ⟨e.trans b.symm⟩⟩⟩))
    case twistedF4 =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      rename_i m
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, reeTitsModel_reeF4_of_equiv hadm e⟩))
    case Tits =>
      cases idx <;> simp only [CFSG.Models.NamesTag] at hnames
      obtain ⟨rfl, rfl⟩ := hnames
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, reeTitsModel_tits_of_equiv e⟩))

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
