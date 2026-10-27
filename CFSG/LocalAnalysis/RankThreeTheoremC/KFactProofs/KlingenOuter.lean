module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.KlingenSpFour
import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

theorem kFactKlingenLocal_outer :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (d : TauCeti.ValidLieTypeIndex),
    IsKlingenIndex p d → ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* CatGroup d) →
      ¬ p ∣ Nat.card (Outer K) := by
  intro p _ hp2 d hd K _ _ ⟨e⟩
  have hp : p.Prime := Fact.out
  rcases hd with hd | ⟨hp3, hd⟩
  ·
    obtain ⟨eK⟩ := KlingenSpFour.nonempty_mulEquiv_psp4 hp2
      (KlingenSpFour.statedClassicalModel_of_spFourIndex d hd e)
    rw [Nat.card_congr (equivalence eK).toEquiv]
    have hK : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
    have h := (CFSG.RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
      (r := 2) hp hp2 le_rfl le_rfl hK).1
    rw [one_mul] at h
    intro hdvd
    have h2 : p ∣ 2 := hdvd.trans (h.trans (Nat.gcd_dvd_left 2 _))
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  ·
    obtain ⟨q, hqp, hqe, hdq⟩ := hd
    obtain ⟨i, hv⟩ := d
    simp only at hdq
    subst hdq
    obtain ⟨e₂⟩ := CFSG.RankThree.PartTwo.Census.nonempty_typeBGroupEquiv_sp6 q hv hqp hqe
    rw [Nat.card_congr (equivalence (e.trans e₂)).toEquiv,
      CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.card_outer_H6]
    intro h
    exact absurd (Nat.le_of_dvd one_pos h) (by rw [hp3]; norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
