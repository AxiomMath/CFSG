module

public import CFSG.HardMathSupport.Foote.E27.Split
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 TauCeti

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem false_of_not_dvd_card_K (h : E27Config X K R T z) (hz : z ∈ K)
    (h27 : ¬ 27 ∣ Nat.card K) : False := by
  have := Subgroup.card_dvd_of_le (h.le_of_mem hz)
  rw [h.card_R] at this
  exact h27 this

theorem false_of_suzuki (h : E27Config X K R T z) (hz : z ∈ K)
    {m : ℕ} (hv : (LieTypeIndex.suzuki m).Valid)
    (e : Nonempty (↥K ≃* ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩)) : False := by
  obtain ⟨e⟩ := e
  obtain ⟨F, _, _, hchar, hF⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.Census.exists_field_card
    2 (2 * m + 1) Nat.prime_two (by omega)
  have e₂ : ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩ ≃* CFSG.Blueprint.suzukiGroup m F :=
    (BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).trans
      (ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hF).symm
  refine false_of_not_dvd_card_K h hz ?_
  rw [Nat.card_congr (e.trans e₂).toEquiv, CFSG.LieType.Ree.suzuki_order hF]
  intro hd
  exact CFSG.HardMathSupport.Timmesfeld.Tables.Census.not_three_dvd_suzuki_order' m
    (Nat.dvd_trans (by norm_num) hd)

end CFSG.HardMathSupport.Malle.E27Lie
