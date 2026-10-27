module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.SecondPointWPow
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3ConjGeneric
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (GenericComponentClass u3_sylow_data)

variable {G : Type} [Group G] [Finite G]

theorem spw_normalizerPowers_of_class {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsRankTwoSEGroupE3 p Q) (hTits : TitsFacts) (hA10 : A10Facts) (hXe : A10Ext)
    (hMcL : ExtraFacts IsMcLType 5 McLShape) (hJ4 : ExtraFacts IsJ4Type 11 J4Shape) :
    SylowIsPlane p Q → NormalizerPowers p Q := by
  intro hpl
  rcases hQ with ⟨hpp, ⟨e⟩⟩ | ⟨q, hqp, hqe, hiso⟩ | ⟨rfl, hA | hT | hM⟩ | ⟨rfl, hJ⟩
  · exact spw_normalizerPowers_of_equiv e (spw_normalizerPowers_psl2 (by omega))
  · exfalso
    have hU : IsU3Pred p Q := ⟨q, hqp, hqe, hiso⟩
    obtain ⟨S⟩ : Nonempty (Sylow p Q) := inferInstance
    have h3 := (u3_sylow_data h5 hU S).1
    have h2 := (hpl S).2
    rw [h3] at h2
    exact absurd (Nat.pow_right_injective (Fact.out : p.Prime).two_le h2) (by norm_num)
  · exact spw_normalizerPowers_five hpl (hXe.scalars Q ⟨rfl, hA⟩)
  · exact spw_normalizerPowers_of_transitive hpl (hTits.trans Q ⟨rfl, hT⟩)
  · exfalso
    obtain ⟨S⟩ : Nonempty (Sylow 5 Q) := inferInstance
    have h3 := (hMcL.sylow Q ⟨rfl, hM⟩ S).1
    have h2 := (hpl S).2
    rw [h3] at h2
    exact absurd (Nat.pow_right_injective (Fact.out : Nat.Prime 5).two_le h2) (by norm_num)
  · exfalso
    obtain ⟨S⟩ : Nonempty (Sylow 11 Q) := inferInstance
    have h3 := (hJ4.sylow Q ⟨rfl, hJ⟩ S).1
    have h2 := (hpl S).2
    rw [h3] at h2
    exact absurd (Nat.pow_right_injective (Fact.out : Nat.Prime 11).two_le h2) (by norm_num)

theorem lemma42_routeW' (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hClass : GenericComponentClass G) {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p)
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hfail : ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M) (hIH : LargerPrimesUnique G p)
    {x : G} (hxP : x ∈ (P : Subgroup G)) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxC : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G))
    (hD₁ : (conjLines x (P : Subgroup G)).ncard ≤ 3)
    (hD₂ : ∀ W : Subgroup G, W ≤ (P : Subgroup G) → Nat.card W = p ^ 2 →
      (∀ A ∈ conjLines x (P : Subgroup G), A ≤ W) →
        conjLines x (P : Subgroup G) = {Subgroup.zpowers x})
    (hab : conjLines x (P : Subgroup G) ≠ {Subgroup.zpowers x} → IsMulCommutative (P : Subgroup G))
    (hxD : x ∉ ⁅(P : Subgroup G), (P : Subgroup G)⁆)
    (hrank3 : ∀ y ∈ (P : Subgroup G), y ^ p = 1 →
      3 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({y} : Set G)))
    (hfacts : ∀ (Q : Type) [Group Q] [Finite Q], IsRankTwoSEGroupE3 p Q → Subgroup.center Q = ⊥ →
      SecondPointFacts p Q)
    (hpow : ∀ (Q : Type) [Group Q] [Finite Q], IsRankTwoSEGroupE3 p Q → Subgroup.center Q = ⊥ →
      SylowIsPlane p Q → NormalizerPowers p Q)
    (hSz : p = 5 → Sz32SecondPointFalse p P M x) :
    ∀ y ∈ (P : Subgroup G), y ≠ 1 → y ^ p = 1 → Subgroup.zpowers y ∉ conjLines x (P : Subgroup G) →
      Subgroup.centralizer ({y} : Set G) ≤ M := by
  intro y hyP hy1 hyp hyD
  by_contra hbad
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have hobs : IsLargeObstruction p M y := ⟨hPM hyP, hy1, hyp, hrank3 y hyP hyp, hbad⟩
  obtain ⟨m, hmM, hmP, hgen⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_conj_isGenericPoint hS hU0 hp hM hobs
  set u : G := MulAut.conj m y with hu
  have hu1 : u ≠ 1 := hgen.2.1.2.1
  have hup : u ^ p = 1 := hgen.2.1.2.2.1
  have hux : Subgroup.zpowers u ∉ conjLines x (P : Subgroup G) := by
    rintro ⟨g, hg, -⟩
    apply hyD
    refine ⟨m⁻¹ * g, ?_, Subgroup.zpowers_le.2 hyP⟩
    have h1 : (Subgroup.zpowers x).map (MulAut.conj (m⁻¹ * g)).toMonoidHom =
        ((Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom).map (MulAut.conj m⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext z
      simp [mul_assoc]
    rw [h1, ← hg, MonoidHom.map_zpowers]
    congr 1
    simp only [hu, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨J, hJC, hCJ, hperf, hlt, hmin, hnot, Q, hQg, ψ, hψ, hker, hlist, -⟩ :=
    hClass p hp P M hM hfail hIH u hgen h5
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hz : Subgroup.center Q = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.u3main_center_bot (CFSG.AGLEmbedding.glbPrimeCore_le p J)
      hperf hlt hmin ψ hψ hker
  rcases hlist with hE | ⟨h5', hSzQ⟩
  · exact second_point_false' hS hU0 hD1 h5 hp hM hxp hxC hxD hD₁ hD₂ hab hgen hux hJC hCJ hperf
      hlt hmin hnot ψ hψ hker (hfacts Q hE hz) (fun _ => hpow Q hE hz)
  · have hux' : u ∉ Subgroup.zpowers x := by
      intro hu_mem
      apply hux
      have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
      have huo : orderOf u = p := orderOf_eq_prime hup hu1
      have hzu : Subgroup.zpowers u = Subgroup.zpowers x := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu_mem) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, hxo, huo]
      refine ⟨1, ?_, ?_⟩
      · rw [hzu, spw_zpowers_conj]
        simp
      · rw [hzu]
        exact Subgroup.zpowers_le.2 hxP
    exact hSz h5' hgen hux' hJC hCJ hperf hlt hmin hnot ψ hψ hker hSzQ

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
