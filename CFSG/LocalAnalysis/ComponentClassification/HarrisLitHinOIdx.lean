module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinElem
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorOrthLift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal

section Pairs

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}

theorem polar_isometryEquiv (ι : Q.IsometryEquiv Q') (x y : V) :
    polar Q' (ι x) (ι y) = polar Q x y := by
  rw [polar, polar, ← map_add, ι.map_app, ι.map_app, ι.map_app]

@[expose] def hypPairMap (ι : Q.IsometryEquiv Q') (P : HypPair Q) : HypPair Q' where
  e := ι P.e
  f := ι P.f
  Q_e := by rw [ι.map_app]; exact P.Q_e
  Q_f := by rw [ι.map_app]; exact P.Q_f
  polar_ef := by rw [polar_isometryEquiv]; exact P.polar_ef

theorem hypPairMap_orth (ι : Q.IsometryEquiv Q') {P P' : HypPair Q} (h : P.Orth P') :
    (hypPairMap ι P).Orth (hypPairMap ι P') where
  ee := (polar_isometryEquiv ι _ _).trans h.ee
  ef := (polar_isometryEquiv ι _ _).trans h.ef
  fe := (polar_isometryEquiv ι _ _).trans h.fe
  ff := (polar_isometryEquiv ι _ _).trans h.ff

@[expose] def ThreePairs (Q : QuadraticForm K V) : Prop :=
  ∃ P₁ P₂ P₃ : HypPair Q, P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃

theorem ThreePairs.map (ι : Q.IsometryEquiv Q') (h : ThreePairs Q) : ThreePairs Q' := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := h
  exact ⟨_, _, _, hypPairMap_orth ι h₁₂, hypPairMap_orth ι h₁₃, hypPairMap_orth ι h₂₃⟩

end Pairs

section Coordinates

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin

variable (K : Type*) [Field K]

theorem threePairs_coordinateQuadOdd {n : ℕ} (hn : 3 ≤ n) : ThreePairs (coordinateQuadOdd n K) :=
  ThreePairs.map (coordinateOddIsometry n K)
    ⟨oddPair K ⟨0, by omega⟩, oddPair K ⟨1, by omega⟩, oddPair K ⟨2, by omega⟩,
      oddPair_orth (by simp [Fin.ext_iff]), oddPair_orth (by simp [Fin.ext_iff]),
      oddPair_orth (by simp [Fin.ext_iff])⟩

theorem threePairs_coordinateQuadPlus {n : ℕ} (hn : 3 ≤ n) :
    ThreePairs (coordinateQuadPlus n K) :=
  ThreePairs.map (coordinatePlusIsometry n K)
    ⟨plusPair K ⟨0, by omega⟩, plusPair K ⟨1, by omega⟩, plusPair K ⟨2, by omega⟩,
      plusPair_orth (by simp [Fin.ext_iff]), plusPair_orth (by simp [Fin.ext_iff]),
      plusPair_orth (by simp [Fin.ext_iff])⟩

theorem threePairs_coordinateQuadMinus {n : ℕ} (hn : 4 ≤ n) (b c : K) :
    ThreePairs (coordinateQuadMinus n K (by omega) b c) :=
  ThreePairs.map (coordinateMinusIsometry n K (by omega) b c)
    ⟨minusPair K b c ⟨0, by omega⟩, minusPair K b c ⟨1, by omega⟩,
      minusPair K b c ⟨2, by omega⟩, minusPair_orth (by simp [Fin.ext_iff]),
      minusPair_orth (by simp [Fin.ext_iff]), minusPair_orth (by simp [Fin.ext_iff])⟩

end Coordinates

section Index

variable {K V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem finite_linearEquiv : Finite (V ≃ₗ[K] V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    (fun g h hgh => LinearEquiv.ext (congrFun hgh))

theorem relIndex_omega_eq_four (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hP : ThreePairs Q) :
    (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆).relIndex
      (TauCeti.QuadraticMap.orthogonalGroup Q) = 4 := by
  have := finite_linearEquiv (K := K) (V := V)
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := hP
  have : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨hcard, -⟩ := ClassicalInvolution.orthogonalGroup_index_four hQ h₁₂ h₁₃ h₂₃
  rw [commutator_orthogonalGroup_eq_elementaryGroup_of_two_ne_zero h2 hQ h₁₂ h₁₃ h₂₃]
  have h := relIndex_mul_card (elementaryGroup Q) (TauCeti.QuadraticMap.orthogonalGroup Q)
  rw [inf_of_le_left (elementaryGroup_le_orthogonalGroup Q), hcard] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem card_le_four_mul_card_inf (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hP : ThreePairs Q) {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    Nat.card H ≤ 4 * Nat.card ↥(H ⊓ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  have := finite_linearEquiv (K := K) (V := V)
  set E := ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆
  have h4 := relIndex_omega_eq_four h2 hQ hP
  have hle := relIndex_le_of_le_right hH (by rw [h4]; norm_num : E.relIndex _ ≠ 0)
  rw [h4] at hle
  have h := relIndex_mul_card E H
  rw [inf_comm] at h
  calc Nat.card H = E.relIndex H * Nat.card ↥(H ⊓ E) := h.symm
    _ ≤ 4 * Nat.card ↥(H ⊓ E) := Nat.mul_le_mul_right _ hle

theorem card_le_two_mul_card_inf (h2 : (2 : K) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (hP : ThreePairs Q) {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hdet : ∀ h ∈ H, LinearEquiv.det h = 1) :
    Nat.card H ≤ 2 * Nat.card ↥(H ⊓ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) := by
  have := finite_linearEquiv (K := K) (V := V)
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hOdef
  set E := ⁅O, O⁆ with hEdef
  set S := O ⊓ (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).ker with hSdef
  have hES : E ≤ S := by
    refine le_inf (commutator_le_self O) ?_
    rw [hEdef, commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have h4 := relIndex_omega_eq_four h2 hQ hP
  have hmul := relIndex_mul_relIndex E S O hES inf_le_left
  rw [h4] at hmul
  obtain ⟨P₁, -, -, -, -, -⟩ := hP
  have hv : Q (P₁.e + P₁.f) = 1 := by
    rw [QuadraticMap.map_add Q, P₁.Q_e, P₁.Q_f, P₁.polar_ef]
    ring
  have : Invertible (Q (P₁.e + P₁.f)) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  have hrS : reflect Q (P₁.e + P₁.f) ∉ S := by
    intro h
    have h1 : LinearEquiv.det (reflect Q (P₁.e + P₁.f)) = 1 := h.2
    rw [reflect_eq_reflection, TauCeti.QuadraticMap.det_reflection] at h1
    have h1' : ((-1 : Kˣ) : K) = ((1 : Kˣ) : K) := by rw [h1]
    simp only [Units.val_neg, Units.val_one] at h1'
    exact h2 (by linear_combination -h1')
  have hSO1 : S.relIndex O ≠ 1 := fun h =>
    hrS ((relIndex_eq_one.mp h) (reflect_mem_orthogonalGroup Q _))
  have hES2 : E.relIndex S ≤ 2 := by
    rcases Nat.lt_or_ge (S.relIndex O) 2 with hlt | hge
    · interval_cases h : S.relIndex O
      · rw [mul_zero] at hmul
        omega
      · exact absurd rfl hSO1
    · nlinarith
  have hHS : H ≤ S := fun h hh => ⟨hH hh, MonoidHom.mem_ker.mpr (hdet h hh)⟩
  have hES0 : E.relIndex S ≠ 0 := fun h => by rw [h, zero_mul] at hmul; omega
  have hle := (relIndex_le_of_le_right hHS hES0).trans hES2
  have h := relIndex_mul_card E H
  rw [inf_comm] at h
  calc Nat.card H = E.relIndex H * Nat.card ↥(H ⊓ E) := h.symm
    _ ≤ 2 * Nat.card ↥(H ⊓ E) := Nat.mul_le_mul_right _ hle

end Index

section Dual

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def fixVec (v : V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g v = v}
  one_mem' := rfl
  mul_mem' {g h} hg hh := by
    change g (h v) = v
    rw [show h v = v from hh]
    exact hg
  inv_mem' {g} hg := by
    change g.symm v = v
    rw [LinearEquiv.symm_apply_eq]
    exact (show g v = v from hg).symm

theorem mem_fixVec {v : V} {g : V ≃ₗ[K] V} : g ∈ fixVec v ↔ g v = v :=
  Iff.rfl

theorem zpow_eq_one_or_eq {G : Type*} [Group G] {z : G} (hz : z * z = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  by_cases hz1 : z = 1
  · left
    rw [hz1, one_zpow]
  · have ho : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
    rw [← zpow_mod_orderOf, ho]
    rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
    · left
      rw [Nat.cast_ofNat, hk2, zpow_zero]
    · right
      rw [Nat.cast_ofNat, hk2, zpow_one]

theorem card_closure_dual {ι : Type*} [DecidableEq ι] [Finite (V ≃ₗ[K] V)] (h2 : (2 : K) ≠ 0)
    (x : ι → V ≃ₗ[K] V) (u : ι → V) (hcomm : ∀ i j, x i * x j = x j * x i)
    (hsq : ∀ i, x i * x i = 1) (hneg : ∀ i, x i (u i) = -u i)
    (hfix : ∀ i j, i ≠ j → x j (u i) = u i) (hu : ∀ i, u i ≠ 0) (s : Finset ι) :
    ElemTwo (closure (x '' ↑s)) ∧ 2 ^ s.card ≤ Nat.card (closure (x '' ↑s)) ∧
      ∀ i ∉ s, closure (x '' ↑s) ≤ fixVec (u i) := by
  have hneg0 : ∀ i, -u i ≠ u i := by
    intro i h
    apply hu i
    have h0 : (2 : K) • u i = 0 := by
      rw [two_smul]
      calc u i + u i = -u i + u i := by rw [h]
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp h0).resolve_left h2
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.coe_empty, Set.image_empty, Subgroup.closure_empty, Finset.card_empty,
      pow_zero]
    refine ⟨⟨fun a ha b hb => ?_, fun a ha => ?_⟩, ?_, fun i _ => bot_le⟩
    · rw [mem_bot] at ha hb
      rw [ha, hb]
    · rw [mem_bot] at ha
      rw [ha, one_mul]
    · rw [Subgroup.card_bot]
  | insert a s ha ih =>
    obtain ⟨hA, hcard, hfixA⟩ := ih
    set A := closure (x '' ↑s) with hAdef
    have heq : closure (x '' ↑(insert a s)) = A ⊔ zpowers (x a) := by
      rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, Subgroup.closure_union,
        zpowers_eq_closure, sup_comm]
    have hxa1 : x a ≠ 1 := by
      intro h
      have := hneg a
      rw [h] at this
      exact hneg0 a this.symm
    have hAc : A ≤ centralizer {x a} := by
      rw [hAdef, closure_le]
      rintro _ ⟨i, -, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (hcomm a i).symm
    have hAB : ∀ y ∈ A, ∀ z ∈ zpowers (x a), y * z = z * y := by
      intro y hy z hz
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
      have hc : Commute y (x a) := mem_centralizer_singleton_iff.mp (hAc hy)
      exact (hc.zpow_right n).eq
    have hinf : A ⊓ zpowers (x a) = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hzA, hzB⟩
      rw [mem_bot]
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hzB
      rcases zpow_eq_one_or_eq (hsq a) n with h | h
      · exact h
      · exfalso
        rw [h] at hzA
        have hf := hfixA a ha hzA
        rw [mem_fixVec, hneg] at hf
        exact hneg0 a hf
    obtain ⟨hE, hc⟩ := elemTwo_sup hA (elemTwo_zpowers (hsq a)) hAB hinf
    rw [card_zpowers_of_sq (hsq a) hxa1] at hc
    refine ⟨heq ▸ hE, ?_, fun i hi => ?_⟩
    · rw [heq, Finset.card_insert_of_notMem ha, pow_succ]
      exact (Nat.mul_le_mul_right 2 hcard).trans hc
    · rw [Finset.mem_insert, not_or] at hi
      rw [heq, sup_le_iff, zpowers_le]
      exact ⟨hfixA i hi.2, hfix i a hi.1⟩

end Dual

section Fix

open Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OddClassSelector
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal (commutant mem_commutant)
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare (orthogonalOmega)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ElemTwo.map {G H : Type*} [Group G] [Group H] {E : Subgroup G} (hE : ElemTwo E)
    (f : G →* H) : ElemTwo (E.map f) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hE.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hE.2 a ha, map_one]

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem exists_elemTwo_fix (Q : QuadraticForm K (Fin d → K)) (g : similarityPairs Q)
    {E : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    (hE : E ≤ orthogonalOmega Q ⊓ commutant (coordinateSemilinearMap g.val))
    (hE2 : ElemTwo E) (hEZ : ∀ x ∈ E, ∀ c : K, (∀ v, x v = c • v) → x = 1) :
    ∃ E' : Subgroup (matrixProjectiveDerived Q),
      E' ≤ fixedSubgroup (matrixProjectiveConjugationHom Q g) ∧ ElemTwo E' ∧
        Nat.card E ≤ Nat.card E' := by
  classical
  set J := derivedLinear Q with hJ
  set π := matrixProjectiveProjection Q with hπ
  set E₀ := E.comap J with hE₀
  have hJi : Function.Injective J := derivedLinear_injective Q
  have hER : E ≤ J.range := by
    rw [hJ, range_derivedLinear]
    exact hE.trans inf_le_left
  have hE₀2 : ElemTwo E₀ := by
    constructor
    · intro a ha b hb
      apply hJi
      rw [map_mul, map_mul]
      exact hE2.1 _ ha _ hb
    · intro a ha
      apply hJi
      rw [map_mul, map_one]
      exact hE2.2 _ ha
  refine ⟨E₀.map π, ?_, hE₀2.map π, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have hc : J a ∈ commutant (coordinateSemilinearMap g.val) := (hE ha).2
    have hfa := (derivedConj_eq_iff Q g a).mpr hc
    show matrixProjectiveConjugationHom Q g (π a) = π a
    rw [hπ, ← matrixProjective_comm, hfa]
  · have hcard : Nat.card E = Nat.card E₀ := by
      rw [← Subgroup.map_comap_eq_self hER, Subgroup.card_map_of_injective hJi]
    rw [hcard]
    refine Nat.card_le_card_of_injective (fun a => ⟨π a, mem_map_of_mem π a.2⟩) ?_
    intro a b hab
    have hab' : π (a : matrixDerived Q) = π b := congrArg Subtype.val hab
    have hmem := QuotientGroup.eq.mp hab'
    obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q _).mp hmem
    have hEmem : J ((a : matrixDerived Q)⁻¹ * b) ∈ E := by
      rw [map_mul, map_inv]
      exact mul_mem (inv_mem a.2) b.2
    have h1 := hEZ _ hEmem (c : K) (fun v => by
      rw [derivedLinear_apply, ← hc,
        LocalAnalysis.ComponentInitial.OddOrthogonal.matrixLinearEquiv_scalar])
    have h2 : (a : matrixDerived Q)⁻¹ * b = 1 := hJi (by rw [h1, map_one])
    exact Subtype.ext (inv_mul_eq_one.mp h2)

end Fix

end CFSG.ComponentClassification.HarrisLit.Hin
