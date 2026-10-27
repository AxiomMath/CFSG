module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexIntersection
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapTwoGroup

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

universe u

variable {G : Type u} [Group G]

theorem point_centralizer_le_unit_normalizer (H : Subgroup G) (z u : G) :
    Subgroup.centralizer ({u} : Set G) ⊓ H ≤
      Subgroup.normalizer (cosetUnitSet H z u) := by
  have hpres : ∀ x : G, x ∈ Subgroup.centralizer ({u} : Set G) ⊓ H →
      ∀ v ∈ cosetUnitSet H z u, x * v * x⁻¹ ∈ cosetUnitSet H z u := by
    intro x hx v hv
    rcases hv with hv | hv
    · left
      rw [Set.mem_singleton_iff] at hv ⊢
      rw [hv]
      simp
    · right
      have hfix : x * u * x⁻¹ = u := by
        have hc := Subgroup.mem_centralizer_singleton_iff.mp hx.1
        rw [hc, mul_assoc, mul_inv_cancel, mul_one]
      have hclass : x * v * x⁻¹ ∈ involutionPointClass z := by
        simpa only [rightConjugateElem, inv_inv] using
          pointClass_right_conjugate_mem hv.1.1 x⁻¹
      have hcomm : x * v * x⁻¹ ∈ Subgroup.centralizer ({u} : Set G) := by
        have hvc := (show Commute v u from
          Subgroup.mem_centralizer_singleton_iff.mp hv.1.2).map (MulAut.conj x).toMonoidHom
        change Commute (x * v * x⁻¹) (x * u * x⁻¹) at hvc
        rw [hfix] at hvc
        exact Subgroup.mem_centralizer_singleton_iff.mpr hvc
      exact ⟨⟨hclass, hcomm⟩, H.mul_mem (H.mul_mem hx.2 hv.2) (H.inv_mem hx.2)⟩
  intro x hx
  change ∀ v, v ∈ cosetUnitSet H z u ↔ x * v * x⁻¹ ∈ cosetUnitSet H z u
  intro v
  constructor
  · exact hpres x hx v
  · intro hv
    have hback := hpres x⁻¹ ((Subgroup.centralizer ({u} : Set G) ⊓ H).inv_mem hx) _ hv
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using hback

theorem point_centralizer_le_translated_normalizer (H : Subgroup G) (z u : G) :
    Subgroup.centralizer ({u} : Set G) ⊓ H ≤
      Subgroup.normalizer (translatedCosetUnitSet H z u) := by
  have hpres : ∀ x : G, x ∈ Subgroup.centralizer ({u} : Set G) ⊓ H →
      ∀ s ∈ translatedCosetUnitSet H z u,
        x * s * x⁻¹ ∈ translatedCosetUnitSet H z u := by
    rintro x hx s ⟨v, hv, rfl⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    have hv' : x * v * x⁻¹ ∈ cosetUnitSet H z u :=
      (show ∀ y, y ∈ cosetUnitSet H z u ↔ x * y * x⁻¹ ∈ cosetUnitSet H z u from
        point_centralizer_le_unit_normalizer H z u hx) v |>.mp hv
    refine ⟨x * v * x⁻¹, hv', ?_⟩
    change u * (x * v * x⁻¹) = x * (u * v) * x⁻¹
    calc
      _ = (u * x) * v * x⁻¹ := by group
      _ = (x * u) * v * x⁻¹ := by rw [← hc]
      _ = x * (u * v) * x⁻¹ := by group
  intro x hx
  change ∀ s, s ∈ translatedCosetUnitSet H z u ↔
    x * s * x⁻¹ ∈ translatedCosetUnitSet H z u
  intro s
  constructor
  · exact hpres x hx s
  · intro hs
    have hback := hpres x⁻¹ ((Subgroup.centralizer ({u} : Set G) ⊓ H).inv_mem hx) _ hs
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using hback

theorem supplied_pair_sylow_centralizes [Finite G] (D : Subgroup G)
    (hfour : ¬ TwoRankAtLeastTwo D) (u : G) (hu : IsInvolution u)
    (huD : u ∈ D) (Q : Sylow 2 D) (huQ : (⟨u, huD⟩ : D) ∈ (Q : Subgroup D)) :
    (Q : Subgroup D).map D.subtype ≤ Subgroup.centralizer ({u} : Set G) := by
  have hQfour : ¬ TwoRankAtLeastTwo (Q : Subgroup D) := by
    intro h
    exact hfour (twoRankAtLeastTwo_of_injective
      (Q : Subgroup D).subtype (Q : Subgroup D).subtype_injective h)
  let uQ : (Q : Subgroup D) := ⟨⟨u, huD⟩, huQ⟩
  have huQI : IsInvolution uQ := by
    constructor
    · intro h
      exact hu.ne_one (congrArg (fun x : (Q : Subgroup D) => ((x : D) : G)) h)
    · apply Subtype.ext
      apply Subtype.ext
      exact hu.sq_eq_one
  rintro x ⟨y, hy, rfl⟩
  let yQ : (Q : Subgroup D) := ⟨y, hy⟩
  have heq : rightConjugateElem uQ yQ = uQ :=
    involutions_eq_of_two_group_no_four Q.isPGroup' hQfour
      (isInvolution_rightConjugateElem huQI) huQI
  have heqG : (y : G)⁻¹ * u * (y : G) = u :=
    congrArg (fun x : (Q : Subgroup D) => ((x : D) : G)) heq
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  change (y : G) * u = u * (y : G)
  have h := congrArg (fun v : G => (y : G) * v) heqG
  simpa only [mul_assoc, mul_inv_cancel_left] using h.symm

theorem translated_normalizer_contains_pair_sylow [Finite G]
    (H D : Subgroup G) (hDH : D ≤ H) (hfour : ¬ TwoRankAtLeastTwo D)
    (z u : G) (hu : IsInvolution u) (huD : u ∈ D) :
    ∃ Q : Sylow 2 D,
      (Q : Subgroup D).map D.subtype ≤
        Subgroup.normalizer (translatedCosetUnitSet H z u) ⊓ D := by
  have huDI : IsInvolution (⟨u, huD⟩ : D) := by
    constructor
    · intro h
      exact hu.ne_one (congrArg Subtype.val h)
    · apply Subtype.ext
      exact hu.sq_eq_one
  have hp : IsPGroup 2 (Subgroup.zpowers (⟨u, huD⟩ : D)) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime huDI.sq_eq_one huDI.ne_one, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have huQ := hQ (Subgroup.mem_zpowers (⟨u, huD⟩ : D))
  have hQC := supplied_pair_sylow_centralizes D hfour u hu huD Q huQ
  refine ⟨Q, ?_⟩
  intro x hx
  have hxD : x ∈ D := Subgroup.map_subtype_le (Q : Subgroup D) hx
  exact ⟨point_centralizer_le_translated_normalizer H z u ⟨hQC hx, hDH hxD⟩, hxD⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
