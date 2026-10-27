module

public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Main
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TwistedRank
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TwistedRankE6
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.UntwistedRank
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.LargeReeRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open CFSG.Assembly.LowTwoRank CFSG.Models CFSG.Blueprint.Chevalley CFSG.TauCetiBridge TauCeti
open CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem pRank_three_ne_one_of_not_dvd {X : Type} [Group X] [Finite X]
    (h : ¬ 3 ∣ Nat.card X) : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≠ 1 := by
  intro h1
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  rw [h1, pow_one] at hE
  exact h (hE ▸ Subgroup.card_subgroup_dvd_card E)

theorem two_le_pRank_three_of_untwistedBridge
    {τ : Tag} {c : PrimePower → LieTypeIndex} (hB : Even.UntwistedBridgeAll τ c)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {X : Type} [Group X] [Finite X]
    {q : PrimePower} {hv : (c q).Valid} (e : X ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨K, _, _, -, hK⟩ := exists_field_card q.p q.exponent q.prime_p q.exponent_pos
  obtain ⟨b⟩ := hB q hv K (by rw [hK, PrimePower.card_def])
  have : Finite (CFSG.Blueprint.AdjointQuotient τ K) := Finite.of_equiv X (e.trans b.symm).toEquiv
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (e.trans b.symm)]
  exact Untw.two_le_pRank_three_adjointQuotient hτ

theorem exceptionalRankTwo_holds :
    ExceptionalRankTwo := by
  intro X _ _ t n p f hm h1 h2 h3 h4 h5 h6
  obtain ⟨hadm, hc | ⟨rfl, d, hnames, ⟨e⟩⟩⟩ := hm
  · exfalso
    cases t
    all_goals first
      | exact h1 rfl | exact h2 rfl | exact h3 rfl | exact h4 rfl | exact h5 rfl | exact h6 rfl
      | exact hc.2.elim
  obtain ⟨idx, hv⟩ := d
  cases t
  case PSL => exact absurd rfl h1
  case PSU => exact absurd rfl h2
  case PSp => exact absurd rfl h3
  case POmegaOdd => exact absurd rfl h4
  case POmegaPlus => exact absurd rfl h5
  case POmegaMinus => exact absurd rfl h6
  case G2 =>
    cases idx <;> simp only [NamesTag] at hnames
    have := two_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.G2)
      Even.chevalleyBridgesAll.g2 (Or.inl rfl) e
    omega
  case F4 =>
    cases idx <;> simp only [NamesTag] at hnames
    have := two_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.F4)
      Even.chevalleyBridgesAll.f4 (Or.inr (Or.inl rfl)) e
    omega
  case E6 =>
    cases idx <;> simp only [NamesTag] at hnames
    have := two_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.E6)
      Even.chevalleyBridgesAll.e6 (Or.inr (Or.inr (Or.inl rfl))) e
    omega
  case E7 =>
    cases idx <;> simp only [NamesTag] at hnames
    have := two_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.E7)
      Even.chevalleyBridgesAll.e7 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) e
    omega
  case E8 =>
    cases idx <;> simp only [NamesTag] at hnames
    have := two_le_pRank_three_of_untwistedBridge (c := LieTypeIndex.E8)
      Even.chevalleyBridgesAll.e8 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) e
    omega
  case twistedE6 =>
    cases idx <;> simp only [NamesTag] at hnames
    have := two_le_pRank_three_twistedE6 e
    omega
  case trialityD4 =>
    cases idx <;> simp only [NamesTag] at hnames
    have := two_le_pRank_three_trialityD4 e
    omega
  case twistedB2 =>
    cases idx <;> simp only [NamesTag] at hnames
    rename_i m
    obtain ⟨rfl, rfl⟩ := hnames
    obtain ⟨K, _, _, -, hK⟩ := exists_field_card 2 (2 * m + 1) Nat.prime_two (by omega)
    have e₂ : ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩ ≃* CFSG.Blueprint.suzukiGroup m K :=
      (BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).trans
        (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).symm
    refine pRank_three_ne_one_of_not_dvd fun h3 => ?_
    rw [Nat.card_congr (e.trans e₂).toEquiv, CFSG.LieType.Ree.suzuki_order hK] at h3
    exact not_three_dvd_suzuki_order' m h3
  case twistedG2 =>
    cases idx <;> simp only [NamesTag] at hnames
    rename_i m
    obtain ⟨rfl, rfl⟩ := hnames
    obtain ⟨K, _, _, -, hK⟩ := exists_field_card 3 (2 * m + 1) Nat.prime_three (by omega)
    obtain ⟨b⟩ := reeG2Bridge m hv K hK
    have hmodel : CFSG.Blueprint.ReeTitsModel X .twistedG2 3 (2 * m + 1) :=
      ⟨hadm, m, rfl, K, inferInstance, inferInstance, hK, ⟨e.trans b.symm⟩⟩
    obtain ⟨-, h3f, hr⟩ := CFSG.SectionRank.smallReeModel_rank hmodel
    omega
  case twistedF4 =>
    cases idx <;> simp only [NamesTag] at hnames
    rename_i m
    obtain ⟨rfl, rfl⟩ := hnames
    have := two_le_pRank_three_largeRee_model (reeTitsModel_reeF4_of_equiv hadm e)
    omega
  case Tits =>
    cases idx <;> simp only [NamesTag] at hnames
    have := two_le_pRank_three_of_titsModel (reeTitsModel_tits_of_equiv e)
    omega

end CFSG.HardMathSupport.Timmesfeld.FieldBonus
