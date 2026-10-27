module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedA

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration

theorem outTowerAt_catA_or {m : ℕ} (hm : 2 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : RankLE2 p (Cat ⟨.A m q, hv⟩)) :
    OutTowerAt (TauCeti.CFSGIndex.lie ⟨.A m q, hv⟩).Group p ∨
      (p ∣ Nat.totient (Nat.gcd (m + 1) (q.card - 1)) ∧ ¬ p ∣ q.card - 1) := by
  by_cases hφ : p ∣ Nat.totient (Nat.gcd (m + 1) (q.card - 1))
  · right
    refine ⟨hφ, fun hq1 => ?_⟩
    have hd0 : 0 < Nat.gcd (m + 1) (q.card - 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd : 2 * p ≤ Nat.gcd (m + 1) (q.card - 1) := by
      by_contra h
      exact not_dvd_totient_of_lt hp hp2 hd0 (by omega) hφ
    have hn : 2 * p ≤ m + 1 := hd.trans (Nat.gcd_le_left _ (by omega))
    have h2 := hp.two_le
    exact not_rankLE2_linear hv hp hq1 (by omega) hrk
  · exact Or.inl (outTowerAt_catA hm hv hp hφ)

open CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower in
theorem outTowerAt_cat_twistedA_or {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : RankLE2 p (Cat ⟨.twistedA m q, hv⟩)) :
    OutTowerAt (TauCeti.CFSGIndex.lie ⟨.twistedA m q, hv⟩).Group p ∨
      (p ∣ Nat.totient (Nat.gcd (m + 1) (q.card + 1)) ∧ ¬ p ∣ q.card + 1) := by
  have hm2 : 2 ≤ m := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  by_cases hφ : p ∣ Nat.totient (Nat.gcd (m + 1) (q.card + 1))
  · right
    refine ⟨hφ, fun hq1 => ?_⟩
    have hd0 : 0 < Nat.gcd (m + 1) (q.card + 1) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd : 2 * p ≤ Nat.gcd (m + 1) (q.card + 1) := by
      by_contra h
      exact not_dvd_totient_of_lt hp hp2 hd0 (by omega) hφ
    have hn : 2 * p ≤ m + 1 := hd.trans (Nat.gcd_le_left _ (by omega))
    have h2 := hp.two_le
    exact not_rankLE2_unitary hv hp hq1 (by omega) hrk
  · left
    have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _)
    have hq : ¬ (m + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun h => hmodel.1.2.2.2 (by rw [h.1, h.2])
    obtain ⟨K, _, hU, ⟨e₀⟩, ⟨e⟩⟩ := exists_primeFormP_mulEquiv_of_statedModel hmodel
    have hφ' : ¬ p ∣ Nat.totient (Nat.gcd (m + 1) (q.p ^ q.exponent + 1)) := by
      rwa [TauCeti.PrimePower.card_def] at hφ
    exact OutTowerAt.of_mulEquiv e (outTowerAt_primeFormP hU (by omega) hq hp hφ')

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
