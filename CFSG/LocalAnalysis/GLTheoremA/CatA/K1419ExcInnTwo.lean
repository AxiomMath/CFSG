module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcInnArith
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcInner
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.RankThree.Chevalley

section Two


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} [CharP L 2]
  {S : LangSetup τ L p₀} {a : Fin τ.rank → Lˣ} {i : KernelComponent (rootCharHom a)}

theorem l3u3_inn_a1_false (hF : L3U3Facts) (D : InnerData S a i)
    (hrank : ∀ α ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      δ = α ∨ δ = -α)
    (hL : L3U3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))) : False := by
  classical
  haveI := D.hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := finite_rationalComponent S a i
  have hN := hF.order _ hL
  obtain ⟨e⟩ := nonempty_mulEquiv_sl2_of_rank_one (rootCharHom a) i hrank (fixSubfield D.σ)
  by_cases hQ : 4 ≤ Nat.card (fixSubfield D.σ)
  · have hQ' : 4 ≤ 2 ^ (D.e * D.s) := D.hKcard ▸ hQ
    obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) D.σ D.hσ (Nat.mul_pos D.he D.hs0) hQ'
    have hperf := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield D.σ)
      (χ := rootCharHom a) ht i
    obtain ⟨g, hg, hgk⟩ := exists_surjective_central_of_perfect D hperf
    have hcard := l3u3_inn_card_centerQuotient_mul hperf g hg hgk
    have hZ : Nat.card (Subgroup.center ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i)) =
        1 := by
      rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, center_sl2_eq_bot_two,
        Subgroup.card_bot]
    have hC : Nat.card ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) =
        Nat.card (fixSubfield D.σ) * (Nat.card (fixSubfield D.σ) ^ 2 - 1) := by
      rw [← Nat.card_congr e.toEquiv, card_sl2_eq]
    rw [hZ, mul_one, hC, D.hKcard] at hcard
    rw [hcard] at hN
    exact l3u3_inn_not_order_sl2 (Nat.mul_pos D.he D.hs0) hN
  · have hK2 : Nat.card (fixSubfield D.σ) = 2 := by
      have hes : D.e * D.s = 1 := by
        by_contra h
        have h2 : 2 ≤ D.e * D.s := by
          have := Nat.mul_pos D.he D.hs0
          omega
        have : 4 ≤ 2 ^ (D.e * D.s) :=
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (D.e * D.s) := Nat.pow_le_pow_right (by norm_num) h2
        rw [D.hKcard] at hQ
        omega
      rw [D.hKcard, hes]
      norm_num
    have hC6 := card_componentRootSpan_rankOne_le_six (rootCharHom a) i hrank
      (fixSubfield D.σ) hK2
    haveI : Finite ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) := inferInstance
    haveI : Finite ↥D.f.range :=
      Finite.of_surjective D.f.rangeRestrict D.f.rangeRestrict_surjective
    have h1 : Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ≤ Nat.card ↥D.f.range :=
      Subgroup.card_le_of_le D.hf1
    have h2 : Nat.card ↥D.f.range ≤
        Nat.card ↥(componentRootSpan (fixSubfield D.σ) (rootCharHom a) i) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd D.f)
    have h3 := hN.ge_20160
    have h4 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
        Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≤
        Nat.card ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    omega

end Two

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
