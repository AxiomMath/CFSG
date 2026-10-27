module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.Open.GriessAllModelsStatement
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevProd
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSp
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.GroupTheory.WeirSylow.Symplectic
public import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
import CFSG.RankThree.PartOne.KF.ClsOmega
import CFSG.ClassicalGroups.Orthogonal.Models
import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossOmega
import CFSG.LargeExtraspecial.DWFldLinear
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.LargeExtraspecial.Types
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.RankThree.GroupTheory.ClassTwoThree
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.Sporadic.M23.M23Group
import CFSG.Timmesfeld.Outcome
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevProof

open CFSG.Open CFSG.SectionRank CFSG.GroupTheory.WeirSylow CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

instance finite_linearEquiv_pi {K : Type} [Field K] [Finite K] {ι : Type} [Finite ι] :
    Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
  Finite.of_injective (fun g : (ι → K) ≃ₗ[K] (ι → K) => (g : (ι → K) → (ι → K)))
    DFunLike.coe_injective

theorem mem_of_pow_eq_one_of_index_two {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (hN : N.index = 2) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {x : G}
    (hx : x ^ r = 1) : x ∈ N := by
  have h1 : (QuotientGroup.mk' N x) ^ r = 1 := by rw [← map_pow, hx, map_one]
  have h2 : (QuotientGroup.mk' N x) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := G ⧸ N) (x := QuotientGroup.mk' N x)
    rwa [← Subgroup.index_eq_card, hN] at this
  have h3 : orderOf (QuotientGroup.mk' N x) ∣ r := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (QuotientGroup.mk' N x) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime r 2 := (Nat.coprime_primes hr Nat.prime_two).2 hr2
  have h5 : orderOf (QuotientGroup.mk' N x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h4
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h5)

theorem pRank_top_eq_of_index_two {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) {G : Type*}
    [Group G] [Finite G] (N : Subgroup G) [N.Normal] (hN : N.index = 2) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥N) = CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have hp1 : 1 < r := hr.out.one_lt
  refine le_antisymm (pRank_top_le_of_injective hp1 N.subtype N.subtype_injective) ?_
  obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp1 (⊤ : Subgroup G)
  have hEN : E ≤ N := fun x hx => mem_of_pow_eq_one_of_index_two hN hr.out hr2 (hE.2 x hx)
  have key := card_le_pow_pRank_of_injective (p := r) (A := ↥E) (G := ↥N)
    (fun a b => hE.1.is_comm.comm a b) (fun a => Subtype.ext (by simpa using hE.2 a a.2))
    (Subgroup.inclusion hEN) (Subgroup.inclusion_injective hEN)
  rw [hcard] at key
  exact (Nat.pow_le_pow_iff_right hp1).1 key

theorem pRank_statedOmega_eq_orthogonal {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀)
    (hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * Nat.card (StatedOmega Q₀))
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedOmega Q₀)) =
      CFSG.Open.pRank r (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  classical
  have hMeq : StatedOmega Q₀ = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆.comap (toLinEquiv ι K).toMonoidHom :=
    statedOmega_eq_comap hQ₀
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set Ω₀ : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := ⁅O, O⁆ with hΩ₀
  have hΩO : Ω₀ ≤ O := by
    rw [hΩ₀, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem h₁ h₂) (O.inv_mem h₁)) (O.inv_mem h₂)
  have e2 : ↥(StatedOmega Q₀) ≃* ↥Ω₀ :=
    (MulEquiv.subgroupCongr hMeq).trans
      ((((toLinEquiv ι K).subgroupMap (Ω₀.comap (toLinEquiv ι K).toMonoidHom))).trans
        (MulEquiv.subgroupCongr
          (Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective Ω₀)))
  have hcardO : Nat.card O = 2 * Nat.card Ω₀ := by
    rw [← Nat.card_congr e2.toEquiv]
    exact hcard
  let N : Subgroup ↥O := Ω₀.subgroupOf O
  have hNnormal : N.Normal := by
    refine ⟨fun x hx y => ?_⟩
    have hxΩ : (x : (ι → K) ≃ₗ[K] (ι → K)) ∈ Ω₀ := hx
    have hxO : (x : (ι → K) ≃ₗ[K] (ι → K)) ∈ O := x.2
    have hcomm : ⁅(y : (ι → K) ≃ₗ[K] (ι → K)), (x : (ι → K) ≃ₗ[K] (ι → K))⁆ ∈ Ω₀ :=
      Subgroup.commutator_mem_commutator y.2 hxO
    show ((y * x * y⁻¹ : ↥O) : (ι → K) ≃ₗ[K] (ι → K)) ∈ Ω₀
    have : ((y * x * y⁻¹ : ↥O) : (ι → K) ≃ₗ[K] (ι → K)) =
        ⁅(y : (ι → K) ≃ₗ[K] (ι → K)), (x : (ι → K) ≃ₗ[K] (ι → K))⁆ *
          (x : (ι → K) ≃ₗ[K] (ι → K)) := by
      rw [commutatorElement_def]
      simp [mul_assoc]
    rw [this]
    exact Ω₀.mul_mem hcomm hxΩ
  have hNindex : N.index = 2 := by
    have h1 := Subgroup.card_mul_index N
    have h2 : Nat.card N = Nat.card Ω₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩO).toEquiv
    rw [h2, hcardO] at h1
    have hpos : 0 < Nat.card Ω₀ := Nat.card_pos
    nlinarith
  have e3 : ↥(StatedOmega Q₀) ≃* ↥N := e2.trans (Subgroup.subgroupOfEquivOfLe hΩO).symm
  rw [pRank_top_eq_of_mulEquiv hr.out.one_lt e3]
  exact pRank_top_eq_of_index_two hr2 N hNindex

theorem rk_plus_arith {e l : ℕ} (he : 0 < e) (hl : 1 ≤ l) :
    (if e ∣ 2 * l ∧ ¬ e ∣ l then (if Even e then 2 * (l - 1) else l - 1) / e
      else (if Even e then 2 * l else l) / e) =
    (if e ∣ 2 * l ∧ ¬ e ∣ l then 2 * l / e - 1 else l / (e / Nat.gcd e 2)) := by
  by_cases hc : e ∣ 2 * l ∧ ¬ e ∣ l
  · rw [if_pos hc, if_pos hc]
    obtain ⟨⟨k, hk⟩, hnel⟩ := hc
    have hev : Even e := by
      by_contra hodd
      exact hnel (Nat.Coprime.dvd_of_dvd_mul_left
        (Nat.coprime_two_right.2 (Nat.not_even_iff_odd.1 hodd)) ⟨k, hk⟩)
    have he2 : 2 ≤ e := by obtain ⟨j, hj⟩ := hev; omega
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    have h2 : 2 * l / e = k := by rw [hk]; exact Nat.mul_div_cancel_left k he
    have h1 : (k - 1) * e = 2 * l - e := by
      rw [Nat.sub_one_mul, Nat.mul_comm, ← hk]
    rw [if_pos hev, h2]
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [h1]; omega
    · have : (k - 1 + 1) * e = 2 * l := by
        rw [Nat.sub_add_cancel hk1, Nat.mul_comm, ← hk]
      rw [this]; omega
  · rw [if_neg hc, if_neg hc]
    exact sp_rank_arith e l

theorem rk_minus_arith {e l : ℕ} (he : 0 < e) (hl : 1 ≤ l) :
    (if e ∣ l then (if Even e then 2 * (l - 1) else l - 1) / e
      else (if Even e then 2 * l else l) / e) =
    l / (e / Nat.gcd e 2) - (if e ∣ l then 1 else 0) := by
  by_cases hd : e ∣ l
  · rw [if_pos hd, if_pos hd]
    obtain ⟨k, hk⟩ := hd
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; omega
      · exact h
    by_cases hev : Even e
    · obtain ⟨j, hj⟩ := hev
      have he2 : 2 ≤ e := by omega
      have hg : Nat.gcd e 2 = 2 := Nat.gcd_eq_right ⟨j, by omega⟩
      have hej : e / 2 = j := by omega
      have hjpos : 0 < j := by omega
      have h3 : l / j = 2 * k := by
        rw [hk, hj, show (j + j) * k = j * (2 * k) by ring]
        exact Nat.mul_div_cancel_left _ hjpos
      rw [if_pos ⟨j, hj⟩, hg, hej, h3]
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have h1 : (2 * k - 1) * e = 2 * l - e := by
          have : (2 * k - 1) * e = 2 * k * e - e := Nat.sub_one_mul _ _
          rw [this, hk]; ring_nf
        rw [h1]; omega
      · have h1 : (2 * k - 1 + 1) * e = 2 * l := by
          rw [Nat.sub_add_cancel (by omega), hk]; ring
        rw [h1]; omega
    · have hodd : Odd e := Nat.not_even_iff_odd.1 hev
      have hg : Nat.gcd e 2 = 1 := Nat.coprime_two_right.2 hodd
      have h3 : l / e = k := by rw [hk]; exact Nat.mul_div_cancel_left k he
      rw [if_neg hev, hg, Nat.div_one, h3]
      refine Nat.div_eq_of_lt_le ?_ ?_
      · have h1 : (k - 1) * e = l - e := by
          rw [Nat.sub_one_mul, Nat.mul_comm, ← hk]
        rw [h1]; omega
      · have h1 : (k - 1 + 1) * e = l := by
          rw [Nat.sub_add_cancel hk1, Nat.mul_comm, ← hk]
        rw [h1]; omega
  · rw [if_neg hd, if_neg hd, Nat.sub_zero]
    exact sp_rank_arith e l

theorem dvd_pow_add_one_iff_weirE {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) {K : Type} [Fintype K]
    (l : ℕ) :
    (p : ℤ) ∣ (Fintype.card K : ℤ) ^ l + 1 ↔ weirE p K ∣ 2 * l ∧ ¬ weirE p K ∣ l := by
  have hfac : (Fintype.card K : ℤ) ^ (2 * l) - 1 =
      ((Fintype.card K : ℤ) ^ l - 1) * ((Fintype.card K : ℤ) ^ l + 1) := by ring
  constructor
  · intro h
    have h2l : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ (2 * l) - 1 := by
      rw [hfac]; exact Dvd.dvd.mul_left h _
    refine ⟨(dvd_pow_sub_one_iff_weirE (p := p) (K := K) (2 * l)).1 h2l, fun hel => ?_⟩
    have h1 := (dvd_pow_sub_one_iff_weirE (p := p) (K := K) l).2 hel
    have h2 : (p : ℤ) ∣ 2 := by
      have := dvd_sub h h1
      have h22 : (Fintype.card K : ℤ) ^ l + 1 - ((Fintype.card K : ℤ) ^ l - 1) = 2 := by ring
      rwa [h22] at this
    have h3 : p ∣ 2 := by exact_mod_cast h2
    have h4 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h3
    rw [h4] at hp1
    exact absurd hp1 (by decide)
  · rintro ⟨h2l, hnel⟩
    have h : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ (2 * l) - 1 :=
      (dvd_pow_sub_one_iff_weirE (p := p) (K := K) (2 * l)).2 h2l
    rw [hfac] at h
    rcases (Nat.prime_iff_prime_int.1 hp.out).dvd_or_dvd h with h1 | h1
    · exact absurd ((dvd_pow_sub_one_iff_weirE (p := p) (K := K) l).1 h1) hnel
    · exact h1

theorem pRank_orthogonal_even {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) {K : Type} [Field K]
    [Fintype K] (hpK : ¬ p ∣ Fintype.card K) {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (hn : 1 ≤ n) (hdim : Fintype.card ι = 2 * n) (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {ε : ℤ}
    (hε : (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ IsMinusType Q)) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) =
      if (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n + ε then
        (if Even (weirE p K) then 2 * (n - 1) else n - 1) / weirE p K
      else (if Even (weirE p K) then 2 * n else n) / weirE p K := by
  have hdim' : Module.finrank K (ι → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, hdim]
  by_cases hc : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n + ε
  · rw [if_pos hc]
    refine pRank_eq_of_sylow_sigmaModel p (one_le_weirA hpK) (fun S => ?_)
    obtain ⟨-, h2, h3⟩ := sylow_orthogonal_even hp1 hpK hn hdim' Q hQ hε S
    have hnd : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ n - ε := h3.resolve_left (not_not.2 hc)
    obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp (n - 1) K)) := inferInstance
    obtain ⟨φ⟩ := h2 hnd P'
    obtain ⟨ψ⟩ := sylow_Sp hp1 K hpK (n - 1) P'
    exact ⟨φ.trans ψ⟩
  · rw [if_neg hc]
    refine pRank_eq_of_sylow_sigmaModel p (one_le_weirA hpK) (fun S => ?_)
    obtain ⟨h1, -, -⟩ := sylow_orthogonal_even hp1 hpK hn hdim' Q hQ hε S
    obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n K)) := inferInstance
    obtain ⟨φ⟩ := h1 hc P'
    obtain ⟨ψ⟩ := sylow_Sp hp1 K hpK n P'
    exact ⟨φ.trans ψ⟩

theorem genericOrders_POmegaPlus_even {l p f : ℕ} (hp : p = 2) (hf : 1 ≤ f) :
    CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus l p f = (1, 1) := by
  have hev : Even (p ^ f) := by rw [hp]; exact Nat.even_pow.2 ⟨even_two, by omega⟩
  unfold CFSG.Blueprint.Multiplier.genericOrders
  simp only [hev, if_true]

end RankChevProof

open RankChevProof CFSG.Open CFSG.Blueprint.Multiplier CFSG.LieType.Universal.Spin
  CFSG.GroupTheory.WeirSylow in
theorem pRank_chev_D (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.D l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkOmPlus l Q.card r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hl4 : 4 ≤ l :=
    (TauCeti.LieTypeIndex.inStandardRange_iff (.D l Q)).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaPlus l Q.p Q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even l Q hv hQ e
  have hLM : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .POmegaPlus l Q.p Q.exponent :=
    ⟨hm.1, Or.inl hm⟩
  have hdvd := ksm_card_center_dvd hG hq hLM
  have hexc : ∃ k, (exceptionalOrders .POmegaPlus l Q.p Q.exponent).1 *
      (exceptionalOrders .POmegaPlus l Q.p Q.exponent).2 = 2 ^ k := by
    unfold exceptionalOrders
    split <;> first | exact ⟨2, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨0, rfl⟩ | simp_all
  obtain ⟨k, hk⟩ := hexc
  rw [genericOrders_POmegaPlus_even hQ Q.exponent_pos, hk] at hdvd
  have hrZ : ¬ r ∣ Nat.card (Subgroup.center K) :=
    not_dvd_of_dvd_two_pow hr hr2 (k := k) (by simpa using hdvd)
  obtain ⟨-, K', instF, instFin, hcard, ⟨φ⟩⟩ := hm
  haveI : Fintype K' := Fintype.ofFinite K'
  have hKc : Fintype.card K' = 2 ^ Q.exponent := by
    rw [Fintype.card_eq_nat_card, hcard, hQ]
  haveI : CharP K' 2 := CFSG.LargeExtraspecial.DW.charP_two_of_card_eq (f := Q.exponent)
    (by rw [hcard, hQ])
  have hpK : ¬ r ∣ Fintype.card K' := by
    rw [hKc]
    exact not_dvd_of_dvd_two_pow hr hr2 (dvd_refl _)
  have hbot := CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
    (K := K') (n := l) (by omega)
  let ψ : ↥(StatedOmega (StatedQuadPlus l K')) ≃* StatedProj (StatedOmega (StatedQuadPlus l K')) :=
    CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have hcardΩ : Nat.card (StatedProj (StatedOmega (StatedQuadPlus (m + 1) K'))) =
      Nat.card ↥(StatedOmega (StatedQuadPlus (m + 1) K')) := (Nat.card_congr ψ.toEquiv).symm
  have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := K') m
  have hΩ := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (K := K')
    (n := m + 1) hl4
  have hpow : ∀ i : ℕ, ((Nat.card K' : ℤ) ^ 2) ^ i = (Nat.card K' : ℤ) ^ (2 * i) :=
    fun i => (pow_mul _ 2 i).symm
  simp only [hpow, Nat.add_sub_cancel] at hO hΩ
  have hcard2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) K')) =
      2 * Nat.card ↥(StatedOmega (StatedQuadPlus (m + 1) K')) := by
    rw [← hcardΩ]
    zify
    rw [hO, hΩ]
    ring
  have hrank := pRank_statedOmega_eq_orthogonal (K := K') (ι := Fin (m + 1) ⊕ Fin (m + 1))
    (Q := quadPlus (m + 1) K') (Q₀ := StatedQuadPlus (m + 1) K') (coe_quadPlus (m + 1) K')
    hcard2 hr2
  have hdim : Fintype.card (Fin (m + 1) ⊕ Fin (m + 1)) = 2 * (m + 1) := by
    simp only [Fintype.card_sum, Fintype.card_fin]; ring
  have hW := pRank_orthogonal_even (p := r) (hr.odd_of_ne_two hr2) hpK
    (ι := Fin (m + 1) ⊕ Fin (m + 1)) (n := m + 1) (by omega) hdim (quadPlus (m + 1) K')
    (nondegenerate_polarBilin_quadPlus (m + 1) K') (ε := 1)
    (Or.inl ⟨rfl, CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K' (m + 1)⟩)
  rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hrZ,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt (φ.trans ψ.symm), hrank, hW]
  have he0 : 0 < weirE r K' := weirE_pos hpK
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hweir : weirE r K' = eP Q.card r := by
    show orderOf ((Fintype.card K' : ℕ) : ZMod r) = orderOf ((Q.card : ℕ) : ZMod r)
    rw [hKc, hQc]
  have hS : eS Q.card r = eP Q.card r / Nat.gcd (eP Q.card r) 2 := by
    unfold eS eP
    rw [orderOf_pow' _ two_ne_zero]
  have hcond := dvd_pow_add_one_iff_weirE (p := r) (K := K') (hr.odd_of_ne_two hr2) (m + 1)
  simp only [hcond]
  rw [hweir]
  unfold rkOmPlus
  rw [hS]
  exact rk_plus_arith (by rw [← hweir]; exact he0) (by omega)

namespace RankChevProof

theorem genericOrders_POmegaMinus_even {l p f : ℕ} (hp : p = 2) (hf : 1 ≤ f) (hl : 1 ≤ l) :
    CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus l p f = (1, 1) := by
  have hev : Even ((p ^ f) ^ l) :=
    Nat.even_pow.2 ⟨by rw [hp]; exact Nat.even_pow.2 ⟨even_two, by omega⟩, by omega⟩
  have h2 : Nat.Coprime 2 ((p ^ f) ^ l + 1) := Nat.coprime_two_left.2 hev.add_one
  have h4 : Nat.gcd 4 ((p ^ f) ^ l + 1) = 1 := by simpa using Nat.Coprime.pow_left 2 h2
  show (Nat.gcd 4 ((p ^ f) ^ l + 1), 1) = (1, 1)
  rw [h4]

end RankChevProof

open RankChevProof CFSG.Open CFSG.Blueprint.Multiplier CFSG.LieType.Universal.Spin
  CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal in
theorem pRank_chev_twistedD (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedD l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkOmMinus l Q.card r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hl4 : 4 ≤ l :=
    (TauCeti.LieTypeIndex.inStandardRange_iff (.twistedD l Q)).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .POmegaMinus l Q.p
      Q.exponent :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even l Q hv hQ e
  have hLM : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .POmegaMinus l Q.p Q.exponent :=
    ⟨hm.1, Or.inl hm⟩
  have hdvd := ksm_card_center_dvd hG hq hLM
  have hexc : ∃ k, (exceptionalOrders .POmegaMinus l Q.p Q.exponent).1 *
      (exceptionalOrders .POmegaMinus l Q.p Q.exponent).2 = 2 ^ k := by
    unfold exceptionalOrders
    split <;> first | exact ⟨2, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨0, rfl⟩ | simp_all
  obtain ⟨k, hk⟩ := hexc
  rw [genericOrders_POmegaMinus_even hQ Q.exponent_pos (by omega), hk] at hdvd
  have hrZ : ¬ r ∣ Nat.card (Subgroup.center K) :=
    not_dvd_of_dvd_two_pow hr hr2 (k := k) (by simpa using hdvd)
  obtain ⟨-, K', instF, instFin, hcard, b, c, hirr, ⟨φ⟩⟩ := hm
  haveI : Fintype K' := Fintype.ofFinite K'
  have hKc : Fintype.card K' = 2 ^ Q.exponent := by
    rw [Fintype.card_eq_nat_card, hcard, hQ]
  haveI : CharP K' 2 := CFSG.LargeExtraspecial.DW.charP_two_of_card_eq (f := Q.exponent)
    (by rw [hcard, hQ])
  have hpK : ¬ r ∣ Fintype.card K' := by
    rw [hKc]
    exact not_dvd_of_dvd_two_pow hr hr2 (dvd_refl _)
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have P := minusPair K' b c (n := m + 1) (⟨0, by omega⟩ : Fin (m + 1 - 1))
  have hv0 : ∃ v, (quadMinus (m + 1) K' b c) v ≠ 0 :=
    ⟨P.e + P.f, by rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]; exact one_ne_zero⟩
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (coe_quadMinus (m + 1) K' b c) hv0
  let ψ : ↥(StatedOmega (StatedQuadMinus (m + 1) K' b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus (m + 1) K' b c)) :=
    CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot
  have hcardΩ : Nat.card (StatedProj (StatedOmega (StatedQuadMinus (m + 1) K' b c))) =
      Nat.card ↥(StatedOmega (StatedQuadMinus (m + 1) K' b c)) :=
    (Nat.card_congr ψ.toEquiv).symm
  have hO := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K') hirr m
  have hΩ := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (K := K')
    (n := m + 1) hl4 hirr
  have hpow : ∀ i : ℕ, ((Nat.card K' : ℤ) ^ 2) ^ i = (Nat.card K' : ℤ) ^ (2 * i) :=
    fun i => (pow_mul _ 2 i).symm
  simp only [hpow, Nat.add_sub_cancel] at hO hΩ
  have hcard2 : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) K' b c)) =
      2 * Nat.card ↥(StatedOmega (StatedQuadMinus (m + 1) K' b c)) := by
    rw [← hcardΩ]
    zify
    rw [hO, hΩ]
    ring
  have hrank := pRank_statedOmega_eq_orthogonal (K := K')
    (ι := Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2)
    (Q := quadMinus (m + 1) K' b c) (Q₀ := StatedQuadMinus (m + 1) K' b c)
    (coe_quadMinus (m + 1) K' b c) hcard2 hr2
  have hdim : Fintype.card (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) = 2 * (m + 1) := by
    simp only [Fintype.card_sum, Fintype.card_fin]; omega
  have hW := pRank_orthogonal_even (p := r) (hr.odd_of_ne_two hr2) hpK
    (ι := Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2) (n := m + 1) (by omega) hdim
    (quadMinus (m + 1) K' b c) (nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K' hirr)
    (ε := -1)
    (Or.inr ⟨rfl, CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.CrossOmega.isMinusType_quadMinus
      (by omega) hirr⟩)
  rw [← sub_eq_add_neg] at hW
  rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hrZ,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt (φ.trans ψ.symm), hrank, hW]
  have he0 : 0 < weirE r K' := weirE_pos hpK
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hweir : weirE r K' = eP Q.card r := by
    show orderOf ((Fintype.card K' : ℕ) : ZMod r) = orderOf ((Q.card : ℕ) : ZMod r)
    rw [hKc, hQc]
  have hS : eS Q.card r = eP Q.card r / Nat.gcd (eP Q.card r) 2 := by
    unfold eS eP
    rw [orderOf_pow' _ two_ne_zero]
  have hcond := dvd_pow_sub_one_iff_weirE (p := r) (K := K') (m + 1)
  simp only [hcond]
  rw [hweir]
  unfold rkOmMinus
  rw [hS]
  exact rk_minus_arith (by rw [← hweir]; exact he0) (by omega)

end CFSG.LocalAnalysis.RankThreeUC.S15
