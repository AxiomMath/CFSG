module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GKnown
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6DerModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Assembly CFSG.StandardType


theorem cAll_geomBody_e6_three {n : ℕ} (hn : 1 ≤ n) (heven : Even n) :
    MI.CAll ⟨.E6, 0, n⟩ (GeomBody 3 ⟨.E6, 0, n⟩) := by
  have hraw : ∀ (k : ℕ) (Q : LargeEvenRawCont), CFSG.Assembly.LargeEvenRawDatum ⟨.E6, 0, k⟩ Q =
      LargeEvenRecipeChevalley CFSG.Blueprint.Chevalley.Tag.E6.cartan (2 ^ k) false Q :=
    fun _ _ => rfl
  intro Q hQ
  rw [hraw] at hQ ⊢
  refine recipeChevalley_and (fun K _ _ hK => ?_) hQ
  refine geomBody_of_field (by simp) fun _ _ f hf hord => ?_
  obtain ⟨K₀, _, _, hK₀, -⟩ := e6_fixStd_der hn hK heven Nat.prime_three (by norm_num) hf hord
  have hlab₀ : LargeEvenInLambda2 ⟨.E6, 0, n / 3⟩ := ⟨one_le_of_card_field hK₀, rfl⟩
  refine fixAlt_of_raw hlab₀ ?_
  rw [hraw]
  exact e6_fixStd_der hn hK heven Nat.prime_three (by norm_num) hf hord

end CFSG.LocalAnalysis.GLTheoremA.T156

end
