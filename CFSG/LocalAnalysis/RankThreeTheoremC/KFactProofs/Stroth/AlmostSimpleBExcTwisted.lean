module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcAbs
public import CFSG.RankThree.PartOne.K1214.SylowShape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits CFSG.Timmesfeld.ExceptionalOrders CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.K1214

section Shape

variable {X : Type*} [Group X] [Finite X]

theorem centralizer_pPart_of_sylowShape {p r e : ℕ} (hp : p.Prime) (hS : SylowShape p r e X)
    {d : X} (hdp : d ^ p = 1) :
    (Nat.card X).factorization p ≤
      (Nat.card (Subgroup.centralizer ({d} : Set X))).factorization p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hdP : IsPGroup p (Subgroup.zpowers d) := by
    intro g
    obtain ⟨n, hn⟩ := g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hdp, one_zpow]
  obtain ⟨Q, hdQ⟩ := hdP.exists_le_sylow
  obtain ⟨φ⟩ := hS (Q : Subgroup X) Q.isPGroup' Q.not_dvd_index
  have hcomm : ∀ a ∈ (Q : Subgroup X), ∀ b ∈ (Q : Subgroup X), a * b = b * a := by
    intro a ha b hb
    have h1 : φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩ := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (φ.injective h1)
  have hQc : (Q : Subgroup X) ≤ Subgroup.centralizer ({d} : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm x hx d (hdQ (Subgroup.mem_zpowers d))
  have hdvd : Nat.card (Q : Subgroup X) ∣ Nat.card (Subgroup.centralizer ({d} : Set X)) :=
    Subgroup.card_dvd_of_le hQc
  rw [Sylow.card_eq_multiplicity] at hdvd
  exact (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd

theorem pClosureOdd_of_sylowShape {p r e : ℕ} (hp : p.Prime) (hS : SylowShape p r e X)
    (h : NoSylowNormalizesTwo p X) : PClosureOdd p X := by
  intro d _ hdp
  refine OddPCoreInClosure.of_odd_core fun N hN hcop => ?_
  haveI := hN
  exact odd_card_of_normal_of_noSylowNormalizes hp h (Subgroup.centralizer ({d} : Set X))
    (centralizer_pPart_of_sylowShape hp hS hdp) N hcop

end Shape

section Fixed


theorem noSylowNormalizesTwo_graphFixed_of_parabolic (t : TwistTag) {K : Type} [Field K]
    [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hH : Holds (graphFixedRootGroup t K σ.toRingHom) 2) {p : ℕ}
    (hpar : ∀ J : Set (Fin t.foldedTag.rank), J ≠ Set.univ →
      ¬ p ^ (Nat.card (graphFixedRootGroup t K σ.toRingHom)).factorization p ∣
        Nat.card (graphFixedParabolic t K σ.toRingHom J)) :
    NoSylowNormalizesTwo p (graphFixedRootGroup t K σ.toRingHom) := by
  intro R E hR hR2 hE hdvd
  obtain ⟨J, φ, hJ, hφ, hmem⟩ :=
    exists_hom_into_graphFixedParabolic_of_normalizes t σ hH hR hR2 hE
  refine hpar J hJ (hdvd.trans ?_)
  have hfin : Finite (ModGL t.tag K) := finite_modGL
  have hle : φ.range ≤ graphFixedParabolic t K σ.toRingHom J := by
    rintro _ ⟨e, rfl⟩
    exact hmem e
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at h1

open Classical in
theorem card_graphFixedRootGroup_eq_borel_mul {t : TwistTag} {K : Type} [Field K] [Finite K]
    [Fintype (WeylGroup t.tag)] {σ : K →+* K} {q : ℕ} (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card) :
    Nat.card (graphFixedRootGroup t K σ) = Nat.card (graphFixedRootBorel t K σ) *
      ∑ w ∈ Finset.univ.filter (· ∈ relWeylTwist t), q ^ (coxeterSystem t.tag).length w := by
  rw [card_graphFixedRootGroup hσ hq, card_graphFixedRootBorel hσ,
    graphFixedRootTorus_eq_compatTorus hσ, card_graphFixedPosUnipotent hσ hq, mul_assoc]

end Fixed

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
