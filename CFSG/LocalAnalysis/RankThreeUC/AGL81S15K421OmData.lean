module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421OmIota
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421OmTrans

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421OmDataProof

open CFSG.Open K421SpProof K421OmProof K421OmTransProof

theorem not_three_dvd_pow_add {Q : ℕ} (h : Q % 3 = 1 ∨ Q % 3 = 2) : ¬ 3 ∣ Q ^ 7 + Q ^ 3 := by
  intro hd
  have h1 := Nat.mod_eq_zero_of_dvd hd
  rcases h with h2 | h2 <;> simp [Nat.add_mod, Nat.pow_mod, h2] at h1

theorem two_pow_mod_three (f : ℕ) : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by
  induction f with
  | zero => left; rfl
  | succ k ih => rw [pow_succ]; omega

theorem K421DataOm_holds : K421DataOm := by
  intro S _ _ p hp hp5 h
  obtain ⟨F, _, _, _, b, d, hirr, hc, ⟨f, hf, hF⟩, hcard, ⟨e⟩⟩ := exists_model h
  have hΩ : Nat.card ↥(OmG F b d) = ordTwistedD 4 (Nat.card F) := by
    rw [← hcard]
    exact (Nat.card_congr e.toEquiv).symm
  have hι : Function.Injective
      (e.symm.toMonoidHom.comp ((iotaOm hirr hf hF hΩ).comp (spIEquiv F).toMonoidHom)) :=
    e.symm.injective.comp ((iotaOm_injective hirr hf hF hΩ).comp (spIEquiv F).injective)
  have hk : Nat.card S = (Nat.card F ^ 7 + Nat.card F ^ 3) * Nat.card ↥(SpI F) := by
    rw [hcard, ordTwistedD_four_eq hF hf, Nat.card_congr (spIEquiv F).toEquiv]
  have h3 : ¬ 3 ∣ Nat.card F ^ 7 + Nat.card F ^ 3 :=
    not_three_dvd_pow_add (by rw [hF]; exact two_pow_mod_three f)
  exact data421_of_embedding hp hp5 hc _ hι (not_dvd_index_of_card hι hk h3)

end K421OmDataProof

end CFSG.LocalAnalysis.RankThreeUC.S15
