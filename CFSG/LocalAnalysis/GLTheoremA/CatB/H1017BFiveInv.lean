module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BTwoBLocal
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5AssemblyInv
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  Subgroup


theorem card_le_of_involution_B (t : NativeSporadic.B) (ht : orderOf t = 2)
    (E : Subgroup NativeSporadic.B)
    (hEt : E ≤ centralizer ({t} : Set NativeSporadic.B)) (hE : IsElemAbelian 5 E) :
    Nat.card E ≤ 5 ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE.isPGroup
  obtain ⟨k, hk⟩ := CFSG.Monster.Existence.babyTableIII.1 t ht
  have hdvd : 5 ^ n ∣ babyCentOrder k := by
    rw [← hn, ← hk.2]
    exact card_dvd_of_le hEt
  have hk1 : k = 1 ∨ ¬ 5 ^ 3 ∣ babyCentOrder k := by
    fin_cases k <;> decide
  rcases hk1 with rfl | h3
  ·
    obtain ⟨g, hg⟩ := isConj_iff.1
      (CFSG.Monster.Existence.babyTableIII.2 1 t xB hk babyInv_one_xB)
    obtain ⟨F, hF, hker⟩ := exists_hom_centralizer_xB
    haveI : Finite NativeSporadic.Co2 :=
      Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co2.card_Co2]; norm_num)
    have hr := CFSG.AGLEmbedding.pRank_le_two_of_hasNoncommPair Nat.prime_five
      (by rw [CFSG.Sporadic.Co2.card_Co2]; decide) CFSG.RankThree.PartOne.CTP.hasNoncommPair_Co2
    have hCo2 : ∀ E' : Subgroup NativeSporadic.Co2, IsElemAbelian 5 E' → Nat.card E' ≤ 5 ^ 2 := by
      intro E' hE'
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hE'.isPGroup
      rw [hm]
      exact Nat.pow_le_pow_right (by norm_num)
        ((CFSG.SectionRank.le_pRank (by norm_num) le_top hE' hm).trans hr)
    have hE'C : E.map (MulAut.conj g).toMonoidHom ≤ centralizer ({xB} : Set NativeSporadic.B) := by
      rintro _ ⟨y, hy, rfl⟩
      have hyt := mem_centralizer_singleton_iff.1 (hEt hy)
      rw [mem_centralizer_singleton_iff, ← hg]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hyt]
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
    rw [← card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective]
    exact H1016M5.card_le_of_le_quot Nat.prime_five (by norm_num) (IsPGroup.of_card hker) hCo2
      (QuotientGroup.quotientKerEquivOfSurjective F hF) hE'C (hE.map _)
  ·
    rw [hn]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hlt
    exact h3 ((Nat.pow_dvd_pow 5 (by omega)).trans hdvd)

end CFSG.LocalAnalysis.GLTheoremA.H1017
