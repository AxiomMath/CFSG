module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3ConjGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (U3LineWC GenericComponentClass)

variable {G : Type} [Group G] [Finite G]

theorem lemma42_routeW (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hClass : GenericComponentClass G) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p)
    {x : G} (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hwc : U3LineWC x (P : Subgroup G)) (hxD : x ∉ ⁅(P : Subgroup G), (P : Subgroup G)⁆)
    (hrank3 : ∀ y ∈ (P : Subgroup G), y ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set G)))
    (hfacts : ∀ (Q : Type) [Group Q] [Finite Q], IsRankTwoSEGroupE3 p Q → Subgroup.center Q = ⊥ →
      SecondPointFacts p Q)
    (hSz : p = 5 → Sz32SecondPointFalse p P M x) :
    ∀ y ∈ (P : Subgroup G), y ^ p = 1 → y ∉ Subgroup.zpowers x →
      Subgroup.centralizer ({y} : Set G) ≤ M := by
  intro y hyP hyp hyx
  by_contra hbad
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hobs : IsLargeObstruction p M y := ⟨hPM hyP, hy1, hyp, hrank3 y hyP hyp, hbad⟩
  obtain ⟨m, hmM, hmP, hgen⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_conj_isGenericPoint hS hU0 hp hM hobs
  set u : G := MulAut.conj m y with hu
  have hu1 : u ≠ 1 := hgen.2.1.2.1
  have hup : u ^ p = 1 := hgen.2.1.2.2.1
  have hux : u ∉ Subgroup.zpowers x := by
    intro hu_mem
    have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
    have huo : orderOf u = p := orderOf_eq_prime hup hu1
    have hzu : Subgroup.zpowers u = Subgroup.zpowers x := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu_mem) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hxo, huo]
    have hmap : (Subgroup.zpowers x).map (MulAut.conj m⁻¹).toMonoidHom = Subgroup.zpowers y := by
      rw [← hzu, MonoidHom.map_zpowers]
      congr 1
      simp only [hu, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hle : (Subgroup.zpowers x).map (MulAut.conj m⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
      rw [hmap]
      exact Subgroup.zpowers_le.2 hyP
    have heq := hwc m⁻¹ hle
    apply hyx
    rw [← heq, hmap]
    exact Subgroup.mem_zpowers y
  obtain ⟨J, hJC, hCJ, hperf, hlt, hmin, hnot, Q, hQg, ψ, hψ, hker, hlist, -⟩ :=
    hClass p hp P M hM hfail hIH u hgen h5
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hz : Subgroup.center Q = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.u3main_center_bot (CFSG.AGLEmbedding.glbPrimeCore_le p J)
      hperf hlt hmin ψ hψ hker
  rcases hlist with hE | ⟨h5', hSzQ⟩
  · exact second_point_false hS hU0 hD1 h5 hp hM hxp hxC hwc hxD hgen hux hJC hCJ hperf hlt hmin
      hnot ψ hψ hker (hfacts Q hE hz)
  · exact hSz h5' hgen hux hJC hCJ hperf hlt hmin hnot ψ hψ hker hSzQ

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
