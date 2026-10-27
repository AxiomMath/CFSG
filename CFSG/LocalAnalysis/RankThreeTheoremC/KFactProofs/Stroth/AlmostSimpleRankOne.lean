module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleOrderP
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleCyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC

section Certificates


theorem false_of_pRank_le_one {X : Type} [Group X] [Finite X] {p : ℕ} {L D : Subgroup X}
    [L.Normal] (hs : IsSimpleGroup L) (hnab : ∃ a b : L, a * b ≠ b * a) (hcat : IsCatalogGroup L)
    (hC : Subgroup.centralizer (L : Set X) = ⊥) (hF : ThompsonFrame p D)
    (hE : NormalizerExponent p D) (hrk : CFSG.Open.pRank p (⊤ : Subgroup L) ≤ 1) : False := by
  haveI : Fact p.Prime := ⟨hF.prime⟩
  have hr : CFSG.pRank p ↥L ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥L]
    exact hrk
  obtain ⟨P₀⟩ : Nonempty (Sylow p L) := inferInstance
  have hPp : IsPGroup p (P₀ : Subgroup L) := P₀.isPGroup'
  have hLX : (P₀ : Subgroup L).map L.subtype ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcycX : IsCyclic ((P₀ : Subgroup L).map L.subtype) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one hF.prime hF.odd hLX (hPp.map L.subtype) hr
  have hcyc : IsCyclic (P₀ : Subgroup L) :=
    (Subgroup.equivMapOfInjective (P₀ : Subgroup L) L.subtype L.subtype_injective).isCyclic.mpr
      hcycX
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    ·
      have hk1 : Nat.card (P₀ : Subgroup L) = 1 := by rw [hk, pow_zero]
      have hLcard : Nat.card L = (P₀ : Subgroup L).index := by
        have h := Subgroup.card_mul_index (P₀ : Subgroup L)
        rw [hk1, one_mul] at h
        exact h.symm
      have hidx : ¬ p ∣ (P₀ : Subgroup L).index := Sylow.not_dvd_index P₀
      have hcop : Nat.Coprime (p ^ 2) (Nat.card L) := by
        rw [hLcard]
        exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hF.prime).mpr hidx)
      have hD0 : D ⊓ L = ⊥ := by
        rw [Subgroup.eq_bot_iff_card]
        have h1 : Nat.card (D ⊓ L : Subgroup X) ∣ p ^ 2 := by
          have h := Subgroup.card_dvd_of_le (inf_le_left : D ⊓ L ≤ D)
          rwa [hF.card] at h
        have h2 : Nat.card (D ⊓ L : Subgroup X) ∣ Nat.card L :=
          Subgroup.card_dvd_of_le (inf_le_right : D ⊓ L ≤ L)
        exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
      exact false_of_inf_eq_bot_of_cyclic hs hnab hcat hC hF P₀ hcyc hD0
    ·
      exact false_of_sylow_card_eq_prime hs hnab hcat hC hF P₀ (by rw [hk, pow_one])
  ·
    exact false_of_cyclic_sylow_ge_sq hF hE P₀ hcyc (by rw [hk]; exact pow_dvd_pow p hk2)

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
