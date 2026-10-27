module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.LieType.Simplicity.Classical
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge

public section

namespace CFSG.AGLEmbedding

theorem kFactSpTwoSimple_holds : KFactSpTwoSimple := by
  intro k d hk ⟨q, hq2, hd⟩
  have hpe : q.p ^ q.exponent = 2 := (TauCeti.PrimePower.card_def q).symm.trans hq2
  have hdvd : q.p ∣ 2 := hpe ▸ dvd_pow_self q.p q.exponent_pos.ne'
  have hqp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
  have hqe : q.exponent = 1 := by
    rw [hqp] at hpe
    exact Nat.pow_right_injective le_rfl (by simpa using hpe)
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hv⟩ := d
    obtain rfl : x = TauCeti.LieTypeIndex.B k q := hd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hv hqp hk
      (MulEquiv.refl _)
    exact (LieType.Simplicity.fam_classical_converse _
      ((Milestones.fam_classical_model_membership_alltags _).2 ⟨_, _, _, _, hm⟩)).2.2
  · have hN : Nat.card (CatGroup d) = CFSG.Open.ordBC k (2 ^ q.exponent) :=
      card_catGroup_B_even hk hqp hd
    change 2 ^ 9 ∣ Nat.card (CatGroup d)
    rw [hN, hqe]
    have h9 : 9 ≤ k * k := Nat.mul_le_mul hk hk
    unfold CFSG.Open.ordBC
    rw [show Nat.gcd 2 (2 ^ 1 - 1) = 1 by norm_num, Nat.div_one]
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 h9) _

end CFSG.AGLEmbedding
