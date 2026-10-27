module

public import CFSG.LieType.Steinberg.CentralExt.PSLMultiplier
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.LieType.Steinberg.CentralExt.SLClosed

theorem card_center_dvd_gcd_of_psl_of_five_le
    {Q K : Type} [Group Q] [Finite Q] [Field K] [Finite K]
    (hQ : Group.IsPerfect Q) {n : ℕ} (hn : 5 ≤ n)
    (e : (Q ⧸ Subgroup.center Q) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin n) K) :
    Nat.card (Subgroup.center Q) ∣ Nat.gcd n (Nat.card K - 1) := by
  letI : Fintype K := Fintype.ofFinite K
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hQ e
  obtain ⟨eM⟩ := (CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_hopfMultiplier_of_five_le
    (k := K) hn).2
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier
      (Matrix.ProjectiveSpecialLinearGroup (Fin n) K)) =
      Nat.gcd n (Nat.card K - 1) := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      Fintype.card_eq_nat_card]
  rwa [hcard] at hdvd

end CFSG.LieType.Steinberg.CentralExt.SLClosed
