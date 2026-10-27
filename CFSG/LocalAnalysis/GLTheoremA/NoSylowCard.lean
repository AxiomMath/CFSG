module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcAbs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

theorem NoSylowNormalizesTwo.card_le_pow_factorization_sub_one {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hN : NoSylowNormalizesTwo p X) {E U : Subgroup X}
    (hE : IsPGroup p E) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set X)) :
    Nat.card E ≤ p ^ ((Nat.card X).factorization p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hE.exists_card_eq
  have hlt : k < (Nat.card X).factorization p := by
    by_contra hle
    exact hN U E hU hU2 hEU (hk ▸ Nat.pow_dvd_pow p (not_lt.1 hle))
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

end
