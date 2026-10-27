module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleSplit
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleGeom
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleGlue
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleWitt
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpinOdd
public import CFSG.ClassicalInvolution.RouteD.TypeDLocal
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDLocal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

variable {p f : ℕ} [Fact p.Prime]

theorem odd_card_galoisField (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : Odd (Nat.card (GaloisField p f)) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  rw [hK]
  exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow

section Quotient

variable {KY V : Type} [Group KY] [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}
  {𝓕 : Set (Subgroup KY)} {π : KY →* (V ≃ₗ[GaloisField p f] V)}

theorem facts_of_centralQuot
    (h : Gaps.CentralQuot π 𝓕 (fundSet Q) (scalars (GaloisField p f) V)) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank (GaloisField p f) V) (hTC : TwinWithinCentralizer (fundSet Q))
    (hker : ∃ ε ∈ π.ker, ∀ k ∈ π.ker, k = 1 ∨ k = ε) :
    FundTwinsExist 𝓕 ∧ FundHubUnique 𝓕 ∧ TwinWithinCentralizer 𝓕 ∧ FundHasOrthogonal 𝓕 ∧
      TwinInvolutionKernel 𝓕 :=
  ⟨FundTwinsExist.of_central π h.ker_le h.perf h.map_mem h.surj
      fun _ hL => exists_isFundTwin_fundSet (odd_card_galoisField hp2 hq) hL,
    FundHubUnique.of_central π h.ker_le h.perf h.map_mem h.surj
      (fundSet_hubUnique (odd_card_galoisField hp2 hq) hQ (Or.inl hdim)),
    TwinWithinCentralizer.of_central π h.ker_le h.perf h.map_mem h.surj hTC,
    FundHasOrthogonal.of_central π h.ker_le h.perf h.map_mem h.surj
      (fundSet_hasOrthogonal (odd_card_galoisField hp2 hq) hQ hdim),
    TwinInvolutionKernel.of_centralQuot (odd_card_galoisField hp2 hq) hQ hdim h hker⟩

end Quotient

theorem exists_kernel_elem {X : Type*} [Group X] {S : Subgroup X} {e : X}
    (h : (S : Set X) = {1, e}) : ∃ ε ∈ S, ∀ k ∈ S, k = 1 ∨ k = ε := by
  refine ⟨e, ?_, fun k hk => ?_⟩
  · have : e ∈ (S : Set X) := by rw [h]; exact Set.mem_insert_of_mem _ rfl
    exact this
  · have : k ∈ (S : Set X) := hk
    rw [h] at this
    simpa using this

theorem oddGlueFacts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) (hn : 4 ≤ n) : GlueFacts p f .POmegaOdd n := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hQ := nondegenerate_polarBilin_quadOdd n (GaloisField p f) h2
  have hdim := Gaps.finrank_odd p f n
  have hker : ∃ ε ∈ (spinAction (quadOdd n (GaloisField p f))).ker,
      ∀ k ∈ (spinAction (quadOdd n (GaloisField p f))).ker, k = 1 ∨ k = ε := by
    have h := coe_ker_spinMatrix_quadOdd (n := n) (K := GaloisField p f) h2
    rw [ker_spinMatrix] at h
    exact exists_kernel_elem h
  obtain ⟨ht, hh, htc, ho, hk⟩ := facts_of_centralQuot (Gaps.centralQuot_odd hp2 hn3 hq) hp2 hq hQ
    (by omega) (fundSet_twinWithinCentralizer (odd_card_galoisField hp2 hq) hQ (by omega)) hker
  exact ⟨RouteD.nonempty_fund_odd hn3, ht, hh, htc, ho, hk⟩

theorem rowSingleOddLarge : RowPiece p f ShapeSingleOddLarge := by
  intro a t n hs
  obtain ⟨rfl, rfl, hn⟩ := hs
  exact shapePiece_of_glueFacts (by decide) fun hp2 hq hadm =>
    ⟨RouteD.yData_odd hadm.2.2.1 hadm (by omega), oddGlueFacts hp2 hq hadm hn⟩

theorem glueFacts_plus_of_datum {n : ℕ} (hn3 : 3 ≤ n)
    (h : GlueFactsOn (fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField p f) hn3))) :
    GlueFacts p f .POmegaPlus n := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) hn3
  show GlueFactsOn (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D)
  rw [e]
  exact h

theorem plusGlueFacts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    GlueFacts p f .POmegaPlus n := by
  have hn3 : 3 ≤ n := by omega
  have hQ := nondegenerate_polarBilin_quadPlus n (GaloisField p f)
  have hdim := Gaps.finrank_plus p f n
  have hker : ∃ ε ∈ (spinAction (quadPlus n (GaloisField p f))).ker,
      ∀ k ∈ (spinAction (quadPlus n (GaloisField p f))).ker, k = 1 ∨ k = ε := by
    have : NeZero n := ⟨by omega⟩
    have h := coe_ker_spinMatrix_quadPlus (n := n) (K := GaloisField p f)
    rw [ker_spinMatrix] at h
    exact exists_kernel_elem h
  obtain ⟨ht, hh, htc, ho, hk⟩ := facts_of_centralQuot (Gaps.centralQuot_plus hp2 (by omega) hn3 hq)
    hp2 hq hQ (by omega)
    (fundSet_twinWithinCentralizer (odd_card_galoisField hp2 hq) hQ (by omega)) hker
  exact glueFacts_plus_of_datum hn3
    ⟨⟨_, rankOne_mem_fundamentalSubgroups_plusDatum hn3 (⟨0, by omega⟩ : Fin n)⟩, ht, hh, htc, ho,
      hk⟩

theorem rowSinglePlusLarge : RowPiece p f ShapeSinglePlusLarge := by
  intro a t n hs
  obtain ⟨rfl, rfl, hn, hn6⟩ := hs
  exact shapePiece_of_glueFacts (by decide) fun hp2 hq hadm =>
    ⟨RouteD.yData_plus hadm.2.2 hadm (by omega), plusGlueFacts hp2 hq hn hn6⟩

section Minus

theorem spinAction_center_mem_scalars_minus {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 4 ≤ m)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {z : spinGroup (quadMinus m K b c)}
    (hz : z ∈ Subgroup.center (spinGroup (quadMinus m K b c))) :
    spinAction (quadMinus m K b c) z ∈ scalars K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
  obtain ⟨-, hcomap, hZ⟩ := spinToStatedProj_quadMinus hm hirr
  have hz' : z ∈ (spinToStatedProj (quadMinus m K b c) (range_spinMatrix_quadMinus hm hirr)).ker :=
    hZ ▸ hz
  rw [hcomap, Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hz'
  exact hz'

theorem centralQuot_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus m p f) :
    Gaps.CentralQuot (spinAction (quadMinus m (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2))
      (fundamentalSubgroups .POmegaMinus (Twisted.minusDatum m (minusCoeffs_irr p f)))
      (fundSet (quadMinus m (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
      (scalars (GaloisField p f) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField p f)) := by
  have hm4 : 4 ≤ m := hadm.2.2
  have hY := RouteD.yData_minus hm4 hp2 hadm (by omega)
  have : Finite (spinGroup (quadMinus m (GaloisField p f) (minusCoeffs p f).1
    (minusCoeffs p f).2)) := ModelFacts.finite_spinGroup_of_ker _
      (coe_ker_spinMatrix_quadMinus (minusCoeffs_irr p f))
  have hker := ker_spinAction_le_center (quadMinus m (GaloisField p f) (minusCoeffs p f).1
    (minusCoeffs p f).2)
  exact
    { ker_le := hker
      center_le := fun z hz => spinAction_center_mem_scalars_minus hm4 (minusCoeffs_irr p f) hz
      perf := fun R hR => commutator_self_eq_of_le (hY.perfR R hR)
      inj := fun R hR r hr h1 => hY.central R hR r hr (hker h1)
      map_mem := (fundCorr_minus hp2 hq hadm).1
      surj := (fundCorr_minus hp2 hq hadm).2 }

theorem minusGlueFacts (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f) (hn : 5 ≤ n) :
    GlueFacts p f .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hQuot := centralQuot_minus hp2 hq hadm
  have hdim : Module.finrank (GaloisField p f)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p f) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hodd := odd_card_galoisField hp2 hq
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField p f)
    (minusCoeffs_irr p f)
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hK]
    omega
  have hTC : TwinWithinCentralizer (fundSet (quadMinus n (GaloisField p f) (minusCoeffs p f).1
      (minusCoeffs p f).2)) := by
    by_cases h6 : n = 6
    · subst h6
      exact minus_twinWithinCentralizer_six (ModelFacts.two_ne_zero_galoisField f hp2)
        (minusCoeffs_irr p f) h4 hodd hQ
    · exact fundSet_twinWithinCentralizer hodd hQ (by omega)
  have hker : ∃ ε ∈ (spinAction (quadMinus n (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)).ker, ∀ k ∈ (spinAction (quadMinus n (GaloisField p f)
        (minusCoeffs p f).1 (minusCoeffs p f).2)).ker, k = 1 ∨ k = ε := by
    have h := coe_ker_spinMatrix_quadMinus (n := n) (K := GaloisField p f)
      (b := (minusCoeffs p f).1) (c := (minusCoeffs p f).2) (minusCoeffs_irr p f)
    rw [ker_spinMatrix] at h
    exact exists_kernel_elem h
  obtain ⟨ht, hh, htc, ho, hk⟩ := facts_of_centralQuot hQuot hp2 hq hQ (by omega) hTC hker
  exact ⟨RouteD.nonempty_fund_minus hn4, ht, hh, htc, ho, hk⟩

theorem rowSingleMinusLarge : RowPiece p f ShapeSingleMinusLarge := by
  intro a t n hs
  obtain ⟨rfl, rfl, hn⟩ := hs
  exact shapePiece_of_glueFacts (by decide) fun hp2 hq hadm =>
    ⟨RouteD.yData_minus hadm.2.2 hp2 hadm (by omega), minusGlueFacts hp2 hq hadm hn⟩

end Minus

end CFSG.ClassicalInvolution.RouteD.Exotic
