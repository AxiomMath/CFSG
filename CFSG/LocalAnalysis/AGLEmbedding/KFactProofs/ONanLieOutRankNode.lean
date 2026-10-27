module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankLevi
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.ComponentClassification

section Generic

variable {K : Type*} [Group K]

theorem QuasiNode.of_equiv [Finite K] {D : UniversalRootDatum K} {i : Fin D.rank} {p : ℕ}
    (hp : p.Prime) {G : Type*} [Group G] (e : ↥(rankOne D.rootGroup i) ≃* G)
    (hq : CFSG.Open.IsQuasisimple G) (hsq : p ^ 2 ∣ Nat.card G)
    (hc : ¬ p ∣ Nat.card ↥(Subgroup.center G)) : QuasiNode D p i where
  quasisimple := Components.quasisimple_of_equiv e hq
  sq_dvd := (Nat.card_congr e.toEquiv) ▸ hsq
  center_coprime := fun hd => by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
    apply hc
    have hzc : e (z : ↥(rankOne D.rootGroup i)) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨a, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e ((Subgroup.mem_center_iff.1 z.2 a))
    have hzG : orderOf (e (z : ↥(rankOne D.rootGroup i))) = p := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hz]
    have hw : orderOf (⟨e (z : ↥(rankOne D.rootGroup i)), hzc⟩ : Subgroup.center G) = p := by
      rw [← Subgroup.orderOf_coe]
      exact hzG
    rw [← hw]
    exact orderOf_dvd_natCard _

end Generic

section SL2

variable {k : Type} [Field k] [Finite k] [CharP k 2]

omit [Finite k] in
theorem sl2_isQuasisimple (h4 : 4 ≤ Nat.card k) :
    CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) k) := by
  have := sl2_isSimpleGroup h4
  exact ⟨(sl2_isPerfect h4).commutator_eq_top,
    ((QuotientGroup.quotientMulEquivOfEq sl2_center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩

theorem QuasiNode.of_equiv_sl2 {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K}
    {i : Fin D.rank} {p : ℕ} (hp : p.Prime) (h4 : 4 ≤ Nat.card k)
    (hpk : p ^ 2 ∣ Nat.card k ^ 2 - 1)
    (e : ↥(rankOne D.rootGroup i) ≃* Matrix.SpecialLinearGroup (Fin 2) k) : QuasiNode D p i :=
  QuasiNode.of_equiv hp e (sl2_isQuasisimple h4)
    (by rw [card_sl2]; exact Dvd.dvd.mul_left hpk _)
    (by rw [sl2_center_eq_bot, Subgroup.card_bot]; exact hp.not_dvd_one)

end SL2

end CFSG.AGLEmbedding.LieOut
