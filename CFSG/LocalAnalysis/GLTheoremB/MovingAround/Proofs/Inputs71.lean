module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a
import all CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.AutOrthInner
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSixOdd
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentAlt
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs71

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open scoped commutatorElement

@[expose] def PPowInner (p : ℕ) (Y : Type*) [Group Y] : Prop :=
  ∀ (σ : MulAut Y) (k : ℕ), σ ^ (p ^ k) = 1 → ∃ y : Y, σ = MulAut.conj y

theorem PPowInner.of_mulEquiv {p : ℕ} {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : PPowInner p Z) : PPowInner p Y := fun σ k hσ =>
  CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.aut_odd_inner_of_mulEquiv e (p ^ k)
    (fun τ hτ => h τ k hτ) σ hσ

theorem pPowInner_of_subsingleton {p : ℕ} {Y : Type*} [Group Y] [Subsingleton Y] :
    PPowInner p Y :=
  fun _ _ _ => ⟨1, MulEquiv.ext fun _ => Subsingleton.elim _ _⟩

theorem le_innerAut_of_pPowInner {p : ℕ} {Y : Type*} [Group Y] (h : PPowInner p Y)
    {P : Subgroup (MulAut Y)} (hP : IsPGroup p P) : P ≤ innerAut Y := by
  intro σ hσ
  obtain ⟨k, hk⟩ := hP ⟨σ, hσ⟩
  have hσk : σ ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨y, rfl⟩ := h σ k hσk
  exact MonoidHom.mem_range.2 ⟨y, rfl⟩

theorem alt_aut_inner_of_odd (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) {m : ℕ} (hm : Odd m)
    (σ : MulAut ↥(alternatingGroup (Fin n))) (h : σ ^ m = 1) :
    ∃ y : ↥(alternatingGroup (Fin n)), σ = MulAut.conj y := by
  obtain ⟨τ, rfl⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    n hn hn6).2 σ
  have hτ : τ ^ m = 1 := by
    apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).1
    rw [map_pow, h, map_one]
  have hsign : Equiv.Perm.sign τ = 1 := by
    have h1 : (Equiv.Perm.sign τ) ^ m = 1 := by rw [← map_pow, hτ, map_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h2 | h2
    · exact h2
    · rw [h2, hm.neg_one_pow] at h1
      exact absurd h1 (by decide)
  refine ⟨⟨τ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩, ?_⟩
  ext x
  rfl

theorem pPowInner_alt (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) {p : ℕ} (hp : Odd p) :
    PPowInner p ↥(alternatingGroup (Fin n)) :=
  fun σ k hσ => alt_aut_inner_of_odd n hn hn6 (hp.pow (n := k)) σ hσ

section Gates

open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)

theorem inner_of_gates_pow {K : Type} [Field K] {d : ℕ} [Finite K] (hK : Nat.card K = 2)
    (Q : QuadraticForm K (Fin d → K)) (hG : OrthogonalGates Q 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (htop : p = 3 → projectivePointFamilyAut Q = ⊤)
    (α : MulAut (matrixProjectiveDerived Q)) {k : ℕ} (hα : α ^ (p ^ k) = 1) :
    α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨-, k₂, hk₂⟩, -, -, hEA, hpK, -, -⟩ := hG
  have hE : α ∈ matrixProjectiveImage Q := by
    rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with h3 | h3
    · rw [← hEA, htop h3]; exact Subgroup.mem_top _
    · have hA : IsPGroup p (Subgroup.zpowers α) := by
        intro x
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
        refine ⟨k, ?_⟩
        apply Subtype.ext
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
      have := hpK p hp h3 _ hA (Subgroup.mem_zpowers α)
      rw [← hEA]
      exact familyOrbitKernel_le Q this
  have : Subsingleton (K ≃+* K) :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.fieldAut_subsingleton hK
  have hD : α ∈ (linearConjugationHom Q).range := by
    have h1 : (⟨α, hE⟩ : matrixProjectiveImage Q) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]; exact Subsingleton.elim _ _
    rw [hψker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hcop2 : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  set H := CFSG.ComponentClassification.OuterAutomorphisms.inner (matrixProjectiveDerived Q)
    with hH
  set D := (linearConjugationHom Q).range with hDdef
  have : H.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set y : D := ⟨α, hD⟩ with hydef
  have hy : y ^ (p ^ k) = 1 := Subtype.ext (by simpa [hydef] using hα)
  have h1 : orderOf (y : D ⧸ H.subgroupOf D) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hy, QuotientGroup.mk_one])
  have h2 : orderOf (y : D ⧸ H.subgroupOf D) ∣ 2 ^ k₂ := by
    rw [← hk₂, Subgroup.relIndex, Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (y : D ⧸ H.subgroupOf D) = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.pow_right k₂ hcop2).coprime_dvd_left h1) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

open CFSG.RankThree.Classical.SteinbergBY
  (orthogonal_large_prime_semilinear_field_and_diagonal_gates)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)
open CFSG.LocalAnalysis.ComponentInitial

theorem pPowInner_omegaPlus (m p : ℕ) (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hexc : ¬ (p = 3 ∧ m = 4)) : PPowInner p ↥(StatedOmega (StatedQuadPlus m (ZMod 2))) := by
  intro σ k hσ
  set G := ↥(StatedOmega (StatedQuadPlus m (ZMod 2))) with hG
  let e : G ≃* StatedProj (StatedOmega (StatedQuadPlus m (ZMod 2))) :=
    (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedProjEquivZMod2 _).symm
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hM : StatedClassicalModel G .POmegaPlus m 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, hm⟩, ZMod 2, inferInstance, inferInstance, hK, ⟨e⟩⟩
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) m 2 1 hM (ZMod 2) hK e
  refine CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_conj_of_mulEquiv
    (coordinatePlusWitnessEquiv (ZMod 2) e) (p ^ k) ?_ σ hσ
  intro α hα
  refine inner_of_gates_pow (by simp) _ hgates hp hp2 ?_ α hα
  intro h3
  have h5 : 5 ≤ m := by
    rcases (show m = 4 ∨ 5 ≤ m by omega) with h4 | h5
    · exact absurd ⟨h3, h4⟩ hexc
    · exact h5
  exact (orthogonal_geometry_plus_point_family_orbit hM hK e).2.2.2.2.1 h5

theorem pPowInner_omegaMinus (m p : ℕ) (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) :
    PPowInner p ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) := by
  intro σ k hσ
  set G := ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) with hG
  let e : G ≃* StatedProj (StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)) :=
    (CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedProjEquivZMod2 _).symm
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  have hM : StatedClassicalModel G .POmegaMinus m 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, hm⟩, ZMod 2, inferInstance, inferInstance, hK, 1, 1, hirr, ⟨e⟩⟩
  have hn1 : 1 ≤ m := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) m 2 1 hM hn1 (ZMod 2) hK 1 1 hirr e
  refine CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_conj_of_mulEquiv
    (coordinateMinusWitnessEquiv (ZMod 2) hn1 1 1 e) (p ^ k) ?_ σ hσ
  intro α hα
  refine inner_of_gates_pow (by simp) _ hgates hp hp2 ?_ α hα
  intro _
  exact ((OrthogonalTail.orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus
    (.inr rfl) m 2 1 hM) hn1 (ZMod 2) hK 1 1 hirr).2

end Gates

section U42

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem pPowInner_u42 : PPowInner 5 ↥(StatedOmega (StatedQuadMinus 3 (ZMod 2) 1 1)) := by
  intro σ k hσ
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by simp
  have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
  obtain ⟨E, _, h, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      hK hirr
  obtain ⟨hsimple, -, hna⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (Or.inr rfl) hirr
  have : Finite E := h.finite
  have hE : Nat.card E = (2 ^ 1) ^ 2 := by rw [h.card_eq_sq]
  have hsimpleT : IsSimpleGroup (StatedSU 4 (2 ^ 1) E) := by
    have := hsimple
    exact eSU.symm.isSimpleGroup
  have hnaT : ¬ ∀ x y : StatedSU 4 (2 ^ 1) E, x * y = y * x := fun hc =>
    hna fun x y => eSU.injective (by rw [map_mul, map_mul, hc])
  have hcenter : Subgroup.center (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    have := hsimpleT
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedSU 4 (2 ^ 1) E)) with
      h0 | h1
    · exact h0
    · exact absurd (fun x y => (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y)) x) hnaT
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hscal : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ := by
    rw [← (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := 1) hE (by norm_num) hnq).2, hcenter]
  let ψ : unitaryPSU h 4 ≃* StatedSU 4 (2 ^ 1) E :=
    (unitaryPSUEquiv h (n := 4) (by norm_num)).trans
      ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot)
  have hout : Nat.card (Outer (unitaryPSU h 4)) = 2 := by
    have := (UnitaryHigher.unitary_full_diagonal_outer_order h (n := 4) (by norm_num)
      (by norm_num)).2.2.2.2.1
    rw [this]
    norm_num
  have hinner : ∀ τ : MulAut (unitaryPSU h 4), τ ^ (5 ^ k) = 1 →
      τ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (unitaryPSU h 4) := by
    intro τ hτ
    have h1 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU h 4)) ∣ 5 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one])
    have h2 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU h 4)) ∣ 2 := by
      have := orderOf_dvd_natCard (QuotientGroup.mk τ : Outer (unitaryPSU h 4))
      rwa [hout] at this
    have h3 : orderOf (QuotientGroup.mk τ : Outer (unitaryPSU h 4)) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num)) h1 h2
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact h3
  exact CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_conj_of_mulEquiv
    (eSU.trans ψ.symm) (5 ^ k) hinner σ hσ

end U42

open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration (typeSign
  dvd_typeSign_of_hasFixedPointFreeOrder statedOmega_quadMinus_two_mulEquiv_alt5
  statedOmega_quadPlus_three_mulEquiv_alt8)

theorem mul_add_two_ne_six {k p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : k * p + 2 ≠ 6 := by
  intro h
  have h4 : p ∣ 4 := ⟨k, by rw [mul_comm]; omega⟩
  have h2 : p ∣ 2 ^ 2 := by norm_num; exact h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))

theorem pPowInner_of_isPiTypeGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y]
    (hY : IsPiTypeGroup p Y) : PPowInner p Y := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases hY with ⟨k, ⟨e⟩⟩ | ⟨n, ε, hn, hO, hfp⟩ | ⟨h3, ⟨e⟩⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    ·
      have key : ∀ σ : Equiv.Perm (Fin (0 * p + 2)), Equiv.Perm.sign σ = 1 → σ = 1 := by
        rw [zero_mul, zero_add]
        decide
      haveI : Subsingleton ↥(alternatingGroup (Fin (0 * p + 2))) :=
        ⟨fun a b => Subtype.ext ((key _ (Equiv.Perm.mem_alternatingGroup.1 a.2)).trans
          (key _ (Equiv.Perm.mem_alternatingGroup.1 b.2)).symm)⟩
      haveI : Subsingleton Y := e.toEquiv.subsingleton
      exact pPowInner_of_subsingleton
    · have h5 : 5 ≤ k * p + 2 := by nlinarith
      exact PPowInner.of_mulEquiv e (pPowInner_alt _ h5 (mul_add_two_ne_six hp hp2) hodd)
  · have hdvd := dvd_typeSign_of_hasFixedPointFreeOrder hp hp2 hn hfp
    cases ε
    ·
      obtain ⟨e⟩ := hO
      rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
      · exact PPowInner.of_mulEquiv (e.trans statedOmega_quadMinus_two_mulEquiv_alt5)
          (pPowInner_alt 5 le_rfl (by decide) hodd)
      · have hp5 : p = 5 := by
          have h5 : typeSign false 2 = 5 := by decide
          rw [h5] at hdvd
          exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hdvd
        subst hp5
        exact PPowInner.of_mulEquiv e pPowInner_u42
      · exact PPowInner.of_mulEquiv e (pPowInner_omegaMinus (n + 1) p (by omega) hp hp2)
    ·
      obtain ⟨e⟩ := hO
      rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | rfl | h4
      · exact absurd hfp
          (CFSG.HardMathSupport.Timmesfeld.Proving.not_hasFixedPointFreeOrder_plus_one hp hp2)
      · exact PPowInner.of_mulEquiv (e.trans statedOmega_quadPlus_three_mulEquiv_alt8)
          (pPowInner_alt 8 (by norm_num) (by norm_num) hodd)
      ·
        have hp7 : p = 7 := by
          have h7 : typeSign true 3 = 7 := by decide
          rw [h7] at hdvd
          exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hdvd
        exact PPowInner.of_mulEquiv e
          (pPowInner_omegaPlus (3 + 1) p (by omega) hp hp2 (by omega))
      · exact PPowInner.of_mulEquiv e
          (pPowInner_omegaPlus (n + 1) p (by omega) hp hp2 (by omega))
  · subst h3
    exact PPowInner.of_mulEquiv e (pPowInner_alt 7 (by norm_num) (by norm_num) hodd)

theorem input7_1Inn_holds : Input7_1Inn := by
  intro p hp hp2 Y _ _ _ hY P hP
  exact le_innerAut_of_pPowInner (pPowInner_of_isPiTypeGroup hp hp2 hY) hP

theorem conj_injective_of_center_eq_bot {K : Type*} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro a b hab
  have hc : b⁻¹ * a ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := congrArg (fun φ : MulAut K => φ g) hab
    simp only [MulAut.conj_apply] at h
    calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
      _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h]
      _ = b⁻¹ * a * g := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

theorem card_mulAut_alt {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Nat.card (MulAut ↥(alternatingGroup (Fin n))) = Nat.factorial n := by
  rw [← Nat.card_eq_of_bijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6),
    Nat.card_perm, Nat.card_fin]

theorem input7_1Aut_holds : Sec13e.Input7_1Aut := by
  intro p hp hp3 K _ _ _ hZ hT E hE
  haveI : Fact p.Prime := ⟨hp⟩
  have hEp : IsPGroup p E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 x x.2)⟩
  obtain ⟨j, hj⟩ := hEp.exists_card_eq
  rw [hj]
  suffices hj1 : j ≤ 1 by
    calc p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hj1
      _ = p := pow_one p
  rcases hT with hA | ⟨hp3', ε, n, hn, hO, hfp, hrk⟩
  ·
    have hA' : Nonempty (K ≃* alternatingGroup (Fin (p + 2))) := hA
    obtain ⟨e⟩ := hA'
    by_contra hj2
    have h2 : p ^ 2 ∣ Nat.card E := hj ▸ pow_dvd_pow p (by omega)
    have hcard : Nat.card (MulAut K) = Nat.factorial (p + 2) := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      refine card_mulAut_alt (by omega) fun h6 => ?_
      have h4 : p = 4 := by omega
      rw [h4] at hp
      norm_num at hp
    have h3 : Nat.card E ∣ Nat.factorial (p + 2) := hcard ▸ Subgroup.card_subgroup_dvd_card E
    exact CFSG.AGLEmbedding.not_sq_dvd_factorial_of_lt hp (by omega) (by omega) (h2.trans h3)
  ·
    have hPi : IsPiTypeGroup p K := Or.inr (Or.inl ⟨n, ε, hn, hO, hfp⟩)
    have hle : E ≤ innerAut K := input7_1Inn_holds p hp (by omega) K hZ hPi E hEp
    have hinj := conj_injective_of_center_eq_bot hZ
    set E' : Subgroup K := E.comap (MulAut.conj : K →* MulAut K) with hE'def
    have hmap : E'.map (MulAut.conj : K →* MulAut K) = E := Subgroup.map_comap_eq_self hle
    have hcard : Nat.card E' = Nat.card E := by
      rw [← hmap, Subgroup.card_map_of_injective hinj]
    have hE' : IsElemAbelian p E' := by
      have := hE.1
      refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
      · have h := congrArg Subtype.val (mul_comm' (⟨MulAut.conj (a : K), a.2⟩ : E)
          ⟨MulAut.conj (b : K), b.2⟩)
        simpa using h
      · rw [map_pow, map_one]
        exact hE.2 _ hx
    have hk := CFSG.SectionRank.le_pRank hp.one_lt le_top hE' (hcard.trans hj)
    omega

@[expose] def IdxTwoPow (X : Type*) [Group X] : Prop :=
  ∃ j : ℕ, (commutator X).index = 2 ^ j

theorem IdxTwoPow.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IdxTwoPow Y) : IdxTwoPow X := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  rw [← hj, Subgroup.index_eq_card, Subgroup.index_eq_card]
  exact Nat.card_congr e.abelianizationCongr.toEquiv

theorem idxTwoPow_of_perfect {X : Type*} [Group X] (h : commutator X = ⊤) : IdxTwoPow X :=
  ⟨0, by rw [h, Subgroup.index_top, pow_zero]⟩

theorem idxTwoPow_of_subsingleton {X : Type*} [Group X] [Subsingleton X] : IdxTwoPow X :=
  idxTwoPow_of_perfect (eq_top_iff.2 fun x _ => by
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _)

theorem idxTwoPow_of_closure {X : Type*} [Group X] [Finite X] {S : Set X}
    (hS : Subgroup.closure S = ⊤) (h2 : ∀ s ∈ S, s ^ 2 = 1) : IdxTwoPow X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ x : X, (Abelianization.of x) ^ 2 = 1 := by
    intro x
    have hx : x ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem s hs => rw [← map_pow, h2 s hs, map_one]
    | one => rw [map_one, one_pow]
    | mul a b _ _ ha hb => rw [map_mul, mul_pow, ha, hb, one_mul]
    | inv a _ ha => rw [map_inv, inv_pow, ha, inv_one]
  have hP : IsPGroup 2 (Abelianization X) := by
    intro g
    refine QuotientGroup.induction_on g fun x => ?_
    exact ⟨1, by rw [pow_one]; exact key x⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hP
  exact ⟨j, hj⟩

theorem idxTwoPow_perm (m : ℕ) : IdxTwoPow (Equiv.Perm (Fin m)) := by
  refine idxTwoPow_of_closure (S := {σ | σ.IsSwap}) Equiv.Perm.closure_isSwap ?_
  rintro σ ⟨x, y, -, rfl⟩
  rw [pow_two, Equiv.swap_mul_self]

theorem subsingleton_alternatingGroup_of_le_two {m : ℕ} (hm : m ≤ 2) :
    Subsingleton ↥(alternatingGroup (Fin m)) := by
  have key : ∀ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ = 1 → σ = 1 := by
    interval_cases m <;> decide
  exact ⟨fun a b => Subtype.ext ((key _ (Equiv.Perm.mem_alternatingGroup.1 a.2)).trans
    (key _ (Equiv.Perm.mem_alternatingGroup.1 b.2)).symm)⟩

theorem commutator_statedSp_eq_top {n : ℕ} (hn : 3 ≤ n) :
    commutator ↥(StatedSp n (ZMod 2)) = ⊤ := by
  haveI : IsSimpleGroup ↥(StatedSp n (ZMod 2)) := OmegaFacts.isSimpleGroup_statedSp_zmod_two hn
  have h4 : 4 ∣ Nat.card ↥(StatedSp n (ZMod 2)) := by
    rw [OmegaFacts.card_statedSp_zmod_two]
    refine Dvd.dvd.mul_right ?_ _
    exact (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ pow_dvd_pow 2 (by nlinarith)
  have hnp : ¬ (Nat.card ↥(StatedSp n (ZMod 2))).Prime := fun hprime =>
    absurd ((Nat.dvd_prime hprime).1 h4) (by
      rintro (h | h)
      · omega
      · rw [← h] at hprime
        exact absurd hprime (by norm_num))
  exact OmegaFacts.commutator_eq_top_of_simple_of_center_bot
    (CatalogInputs.center_eq_bot_of_simple_not_prime hnp)

section OmegaPlusFour

open OmegaFacts
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell
  (card_orthGroup_quadPlus_two)

theorem iotaGL_mul_G41 : iotaGL * G41 = G41 * G41 * iotaGL := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [iotaGL_val, G41_val]
  decide +kernel

theorem iotaGL_mul_G42 : iotaGL * G42 = G42 * G42 * iotaGL := by
  apply Units.ext
  simp only [Units.val_mul]
  rw [iotaGL_val, G42_val]
  decide +kernel

theorem commutatorElement_eq_of_mul_eq {G : Type*} [Group G] {i g : G} (h : i * g = g * g * i) :
    ⁅i, g⁆ = g := by
  rw [commutatorElement_def, h]
  group

theorem card_statedOmega_plus_two_dvd :
    Nat.card ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) ∣ 72 := by
  have hle : StatedOmega (StatedQuadPlus 2 (ZMod 2)) ≤
      CFSG.LieType.BorelTits.orthGroup (StatedQuadPlus 2 (ZMod 2)) := by
    show ⁅CFSG.LieType.BorelTits.orthGroup (StatedQuadPlus 2 (ZMod 2)),
      CFSG.LieType.BorelTits.orthGroup (StatedQuadPlus 2 (ZMod 2))⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro g hg h hh
    simp only [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
      (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)
  have hcard : Nat.card ↥(CFSG.LieType.BorelTits.orthGroup (StatedQuadPlus 2 (ZMod 2))) = 72 := by
    rw [card_orthGroup_quadPlus_two, Nat.card_zmod]
    norm_num
  exact hcard ▸ Subgroup.card_dvd_of_le hle

theorem idxTwoPow_omegaPlus_two : IdxTwoPow ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) := by
  set W := ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) with hW
  let ι : W := ⟨iotaGL, iotaGL_mem⟩
  let g₁ : W := ⟨G41, G41_mem⟩
  let g₂ : W := ⟨G42, G42_mem⟩
  have h1 : ⁅ι, g₁⁆ = g₁ := commutatorElement_eq_of_mul_eq (Subtype.ext iotaGL_mul_G41)
  have h2 : ⁅ι, g₂⁆ = g₂ := commutatorElement_eq_of_mul_eq (Subtype.ext iotaGL_mul_G42)
  have hg₁ : g₁ ∈ commutator W := by
    rw [← h1, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top ι) (Subgroup.mem_top g₁)
  have hg₂ : g₂ ∈ commutator W := by
    rw [← h2, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top ι) (Subgroup.mem_top g₂)
  have hR : Rank2 (commutator W) := by
    refine ⟨g₁, hg₁, g₂, hg₂, Subtype.ext G41_cube, Subtype.ext G42_cube, Subtype.ext G4_comm,
      fun h => G41_ne_one (congrArg Subtype.val h), fun hmem => ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine G42_not_mem (Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩)
    have hk' := congrArg Subtype.val hk
    rw [SubgroupClass.coe_zpow] at hk'
    exact hk'
  have h9 : 9 ∣ Nat.card ↥(commutator W) := nine_dvd_card_of_rank2 (rank2_top_of_subgroup hR)
  have hmul := Subgroup.card_mul_index (commutator W)
  obtain ⟨c, hc⟩ := h9
  have hidx : (commutator W).index ∣ 2 ^ 3 := by
    have h72 : 9 * (c * (commutator W).index) ∣ 9 * 8 := by
      rw [← mul_assoc, ← hc, hmul]
      exact card_statedOmega_plus_two_dvd
    exact (Dvd.intro_left c rfl).trans (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h72)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hidx
  exact ⟨j, hj⟩

end OmegaPlusFour

theorem inputAbIdx2_holds : InputAbIdx2 := by
  intro X _ _ hX
  suffices h : IdxTwoPow X by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by rw [← commutator_def]; exact hj⟩
  rcases hX with ⟨m, hm, ⟨e⟩⟩ | ⟨m, ⟨e⟩⟩ | ⟨n, ⟨e⟩⟩ | ⟨ε, n, hn, hO⟩
  · rcases hm with hm | hm
    · haveI := subsingleton_alternatingGroup_of_le_two hm
      haveI : Subsingleton X := e.toEquiv.subsingleton
      exact idxTwoPow_of_subsingleton
    · exact IdxTwoPow.of_mulEquiv e
        (idxTwoPow_of_perfect (commutator_alternatingGroup_eq_top (by simpa using hm)))
  · exact IdxTwoPow.of_mulEquiv e (idxTwoPow_perm m)
  · rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | h3
    · haveI := OmegaFacts.subsingleton_statedSp_zero
      haveI : Subsingleton X := e.toEquiv.subsingleton
      exact idxTwoPow_of_subsingleton
    · obtain ⟨f⟩ :=
        CFSG.HardMathSupport.RichardWeiss.Proving.PLType.nonempty_statedSp_one_mulEquiv_perm_three
      exact IdxTwoPow.of_mulEquiv (e.trans f) (idxTwoPow_perm 3)
    · obtain ⟨f⟩ := OmegaFacts.nonempty_statedSp_two_mulEquiv_perm_six
      exact IdxTwoPow.of_mulEquiv (e.trans f) (idxTwoPow_perm 6)
    · exact IdxTwoPow.of_mulEquiv e (idxTwoPow_of_perfect (commutator_statedSp_eq_top h3))
  · rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | h3
    · cases ε
      · obtain ⟨e⟩ := hO
        exact IdxTwoPow.of_mulEquiv (e.trans statedOmega_quadMinus_two_mulEquiv_alt5)
          (idxTwoPow_of_perfect (commutator_alternatingGroup_eq_top (by simp)))
      · obtain ⟨e⟩ := hO
        exact IdxTwoPow.of_mulEquiv e idxTwoPow_omegaPlus_two
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      cases ε
      · obtain ⟨e⟩ := hO
        exact IdxTwoPow.of_mulEquiv e
          (idxTwoPow_of_perfect (OmegaFacts.commutator_statedOmega_minus_eq_top (by omega)))
      · obtain ⟨e⟩ := hO
        exact IdxTwoPow.of_mulEquiv e
          (idxTwoPow_of_perfect (OmegaFacts.commutator_statedOmega_plus_eq_top (by omega)))

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs71
