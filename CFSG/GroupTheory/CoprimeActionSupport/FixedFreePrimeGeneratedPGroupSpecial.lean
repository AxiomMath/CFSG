module

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Ext
meta import Lean.Elab.Tactic.NormCast
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section


namespace CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeGeneratedPGroupSpecial


open CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups


private lemma normalizes {G : Type*} [Group G] (D Q : Subgroup G) (hQD : ⁅D, Q⁆ = Q) :
    D ≤ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_right, hQD]


private lemma normalizes_char {G : Type*} [Group G] (D Q U : Subgroup G) (hQD : ⁅D, Q⁆ = Q)
    (hUQ : U ≤ Q) (hchar : (U.subgroupOf Q).Characteristic) :
    D ≤ Subgroup.normalizer (U : Set G) := by
  intro d hd
  have hdQ : ∀ x ∈ Q, d * x * d⁻¹ ∈ Q := by
    intro x hx
    have := normalizes D Q hQD hd
    exact (Subgroup.mem_normalizer_iff.mp this x).mp hx
  have hdQ' : ∀ x ∈ Q, d⁻¹ * x * d ∈ Q := by
    intro x hx
    have := normalizes D Q hQD (D.inv_mem hd)
    simpa using (Subgroup.mem_normalizer_iff.mp this x).mp hx
  let φ : Q ≃* Q :=
    { toFun := fun x => ⟨d * x * d⁻¹, hdQ x x.2⟩
      invFun := fun x => ⟨d⁻¹ * x * d, hdQ' x x.2⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc]
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  have hfix := hchar.fixed φ
  have key : ∀ x ∈ U, d * x * d⁻¹ ∈ U := by
    intro x hx
    have hmem : (⟨x, hUQ hx⟩ : Q) ∈ U.subgroupOf Q := hx
    rw [← hfix] at hmem
    exact hmem
  have hfix' := hchar.fixed φ.symm
  have key' : ∀ x ∈ U, d⁻¹ * x * d ∈ U := by
    intro x hx
    have hmem : (⟨x, hUQ hx⟩ : Q) ∈ U.subgroupOf Q := hx
    rw [← hfix'] at hmem
    exact hmem
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key x hx, fun hx => ?_⟩
  have := key' _ hx
  simpa [mul_assoc] using this


theorem special_and_center {F : Type*} [Field F] {G : Type} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hρ : Function.Injective ρ)
    {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (D : Subgroup G) (hD : Nat.card D = r)
    (hCV : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule F V))
    (E : Subgroup G) (hE1 : E ≠ ⊥) (hEq : IsPGroup q E)
    (hEF : (Nat.card E : F) ≠ 0) (hrF : (r : F) ≠ 0) (hDE : ⁅D, E⁆ = E) :
    IsSpecialPGroup E ∧ (Subgroup.center E).map E.subtype = E ⊓ Subgroup.centralizer (D : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hcop : Nat.Coprime q (Nat.card D) := by
    rw [hD]; exact (Nat.coprime_primes hq hr).mpr hqr
  have hSE : ⁅E, D⁆ = E := by rw [Subgroup.commutator_comm]; exact hDE
  rcases exists_characteristic_abelian_not_centralized_or_special_center_eq_centralizer q hq E D hEq hE1 hcop (normalizes D E hDE) hSE with ⟨U, hUE, hchar, hUc, hnot⟩ | h
  · exfalso
    apply hnot
    have hUdvd : Nat.card U ∣ Nat.card E := Subgroup.card_dvd_of_le hUE
    have hUF : (Nat.card U : F) ≠ 0 := by
      intro h0
      apply hEF
      obtain ⟨k, hk⟩ := hUdvd
      rw [hk]; push_cast; rw [h0, zero_mul]
    exact CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension.centralizes
      ρ hρ r D hD hCV U (normalizes_char D E U hDE hUE hchar) hUF hrF
  · exact h


theorem nonabelian {F : Type*} [Field F] {G : Type} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hρ : Function.Injective ρ)
    {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (D : Subgroup G) (hD : Nat.card D = r)
    (hCV : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule F V))
    (E : Subgroup G) (hE1 : E ≠ ⊥) (hEq : IsPGroup q E)
    (hEF : (Nat.card E : F) ≠ 0) (hrF : (r : F) ≠ 0) (hDE : ⁅D, E⁆ = E) :
    ¬ IsMulCommutative E := by
  intro hcomm
  haveI : Fact r.Prime := ⟨hr⟩
  apply hE1
  have hcent := CFSG.GroupTheory.CoprimeActionSupport.FixedFreeNormalizerScalarExtension.centralizes
    ρ hρ r D hD hCV E (normalizes D E hDE) hEF hrF
  rw [← hDE, eq_bot_iff, Subgroup.commutator_le]
  intro d hd x hx
  have := (Subgroup.mem_centralizer_iff.mp (hcent hd)) x hx
  rw [Subgroup.mem_bot, commutatorElement_def]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  simpa [mul_assoc] using this.symm


end CFSG.GroupTheory.CoprimeActionSupport.FixedFreePrimeGeneratedPGroupSpecial
