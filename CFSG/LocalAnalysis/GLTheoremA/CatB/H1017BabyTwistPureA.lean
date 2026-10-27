module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureAFi
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Twist
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BRank0
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalThreeB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance


theorem babyNoPureFourAt_zero : BabyNoPureFourAt 0 := by
  intro t ht D hDt hD hDcard
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hr : BabyInv 0 (BThreeFi23.phiB (CFSG.Sporadic.Fi23.conjPt 770)) :=
    babyInv_zero_map_of_isConj_d _ BThreeFi23.phiB_injective
      ((CFSG.Sporadic.Fi23.isConj_d_iff _).2 ⟨⟨770, by norm_num⟩, rfl⟩)
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Monster.Existence.babyTableIII.2 0 t _ ht hr)
  obtain ⟨S, hSC, hScard, hSpure⟩ := PureA.exists_sylow_centralizer_conjPt_pure
  have hS1 : S.map BThreeFi23.phiB ≤
      Subgroup.centralizer {BThreeFi23.phiB (CFSG.Sporadic.Fi23.conjPt 770)} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← map_mul, (Subgroup.mem_centralizer_singleton_iff).1 (hSC hy), map_mul]
  have hS1card : Nat.card (S.map BThreeFi23.phiB) = 3 ^ (Nat.card (Subgroup.centralizer
      {BThreeFi23.phiB (CFSG.Sporadic.Fi23.conjPt 770)})).factorization 3 := by
    rw [Subgroup.card_map_of_injective BThreeFi23.phiB_injective, hScard, hr.2,
      show babyCentOrder 0 = 3 ^ 9 * (2 ^ 38 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19) by
        norm_num [babyCentOrder],
      Fi23Sylow.factorization_three_pow_mul 9 _ (by norm_num)]
  have hD1 : D.map (MulAut.conj c).toMonoidHom ≤
      Subgroup.centralizer {BThreeFi23.phiB (CFSG.Sporadic.Fi23.conjPt 770)} := by
    rintro _ ⟨x, hx, rfl⟩
    have hxt := (Subgroup.mem_centralizer_singleton_iff).1 (hDt hx)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * x * c⁻¹ * (c * t * c⁻¹) = c * (x * t) * c⁻¹ := by group
      _ = c * (t * x) * c⁻¹ := by rw [hxt]
      _ = c * t * c⁻¹ * (c * x * c⁻¹) := by group
  obtain ⟨g, -, hg⟩ := exists_conj_into_of_card hS1 hS1card hD1 (hD.map _).isPGroup
  obtain ⟨E, hE⟩ : ∃ E : Subgroup NativeSporadic.B,
      E = (D.map (MulAut.conj c).toMonoidHom).map (MulAut.conj g).toMonoidHom := ⟨_, rfl⟩
  rw [← hE] at hg
  have hEcard : Nat.card E = 3 ^ 4 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj _).injective,
      Subgroup.card_map_of_injective (MulAut.conj _).injective, hDcard]
  have hEab : IsElemAbelian 3 E := hE ▸ (hD.map _).map _
  have hErange : E ≤ BThreeFi23.phiB.range := hg.trans (Subgroup.map_le_range _ _)
  have hD3S : E.comap BThreeFi23.phiB ≤ S := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 (hg (Subgroup.mem_comap.1 hy))
    rw [← BThreeFi23.phiB_injective hsy]
    exact hs
  have hD3c : Nat.card (E.comap BThreeFi23.phiB) = 3 ^ 4 := by
    rw [← Subgroup.card_map_of_injective BThreeFi23.phiB_injective,
      Subgroup.map_comap_eq_self hErange, hEcard]
  obtain ⟨y, hy, hy1, hyc⟩ :=
    hSpure _ hD3S (hEab.comap BThreeFi23.phiB_injective) hD3c
  have hyE : BThreeFi23.phiB y ∈ E := Subgroup.mem_comap.1 hy
  rw [hE] at hyE
  obtain ⟨z, hz, hxy⟩ := Subgroup.mem_map.1 hyE
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
  have hconj : IsConj x (BThreeFi23.phiB y) := by
    refine isConj_iff.2 ⟨g * c, ?_⟩
    rw [← hxy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hy1
    apply BThreeFi23.phiB_injective
    rw [← hxy]
    simp
  have hx0 : IsConj x (BThreeFi23.phiB (BThreeFi23.t3 0)) := by
    rcases hyc with h0 | h2
    · exact hconj.trans (BThreeFi23.phiB.map_isConj h0)
    · exact hconj.trans ((BThreeFi23.phiB.map_isConj h2).trans BThreeFi23.bThreeRc_holds)
  refine ⟨x, hx, hx1, fun h3B => ?_⟩
  obtain ⟨k, hk⟩ := isConj_iff.1 (hx0.symm.trans h3B)
  have e := BSevenLocal.rk_conj k (BThreeFi23.phiB (BThreeFi23.t3 0))
  rw [hk, BSevenLocal.rk_phiB_t3_one.1,
    CFSG.HardMathSupport.Solomon.Coordinator.B3B.rk_phiB_t3_zero] at e
  omega

end CFSG.LocalAnalysis.GLTheoremA.H1017
