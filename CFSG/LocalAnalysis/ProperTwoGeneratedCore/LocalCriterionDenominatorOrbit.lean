module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Complement

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.BenderSuzuki.PFchapter1section1 CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def involutionOrbit (E : Subgroup G) (t : G) : Set G :=
  {s | ∃ e ∈ E, rightConjugateElem t e = s}

variable [Finite G]

theorem normalized_subgroup_inversion_of_trivial_centralizer
    (W : Subgroup G) (t : G) (ht : orderOf t = 2)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hfixed : W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) :
    Odd (Nat.card W) ∧ IsMulCommutative W ∧
      ∀ w ∈ W, rightConjugateElem w t = w⁻¹ := by
  let tn : Subgroup.normalizer (W : Set G) := ⟨t, htW⟩
  let phi : MulAut W := W.normalizerMonoidHom tn
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have htt : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [ht, pow_two] at hpow
    exact hpow
  have hinv : Function.Involutive phi := by
    intro w
    apply Subtype.ext
    change t * (t * (w : G) * t⁻¹) * t⁻¹ = w
    rw [htinv]
    calc
      t * (t * (w : G) * t) * t = (t * t) * (w : G) * (t * t) := by group
      _ = w := by rw [htt, one_mul, mul_one]
  have hfree : MonoidHom.FixedPointFree phi := by
    intro w hw
    apply Subtype.ext
    have hc : (w : G) ∈ Subgroup.centralizer ({t} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have heq : t * (w : G) * t⁻¹ = w := congrArg Subtype.val hw
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    have hbot : (w : G) ∈ (⊥ : Subgroup G) := hfixed ▸ ⟨w.property, hc⟩
    exact hbot
  refine ⟨hfree.odd_card_of_involutive hinv, ?_, ?_⟩
  · exact ⟨⟨fun a b => (hfree.commute_all_of_involutive hinv a b).eq⟩⟩
  · intro w hw
    have heq := congrFun (hfree.coe_eq_inv_of_involutive hinv) (⟨w, hw⟩ : W)
    have hcoe : t * w * t⁻¹ = w⁻¹ := congrArg Subtype.val heq
    simpa only [rightConjugateElem, htinv] using hcoe

omit [Finite G] in
theorem inverted_odd_subgroup_involution_orbit
    (W : Subgroup G) (t : G) (ht : orderOf t = 2)
    (hodd : Odd (Nat.card W))
    (hinv : ∀ w ∈ W, rightConjugateElem w t = w⁻¹) :
    involutionOrbit W t = (W : Set G) * ({t} : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have htt : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [ht, pow_two] at hpow
    exact hpow
  have hformula (w : W) : rightConjugateElem t (w : G) = (w : G)⁻¹ ^ 2 * t := by
    have hw : t * (w : G) * t = (w : G)⁻¹ := by
      simpa only [rightConjugateElem, htinv] using hinv w w.property
    calc
      rightConjugateElem t (w : G) = (w : G)⁻¹ * t * w := rfl
      _ = (w : G)⁻¹ * (t * w * t) * t := by
        simp only [mul_assoc, htt, mul_one]
      _ = (w : G)⁻¹ ^ 2 * t := by rw [hw, pow_two]
  ext s
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact Set.mem_mul.mpr ⟨(w⁻¹) ^ 2, W.pow_mem (W.inv_mem hw) 2,
      t, Set.mem_singleton t, (hformula ⟨w, hw⟩).symm⟩
  · rintro ⟨q, hq, r, hr, rfl⟩
    have hrt : r = t := hr
    subst r
    obtain ⟨w, hw⟩ := (powCoprime hodd.coprime_two_right).surjective (⟨q, hq⟩ : W)
    refine ⟨(w : G)⁻¹, W.inv_mem w.property, ?_⟩
    rw [hformula ⟨(w : G)⁻¹, W.inv_mem w.property⟩, inv_inv]
    have hsq : (w : G) ^ 2 = q := by
      simpa only [powCoprime_apply, Subgroup.coe_pow] using congrArg Subtype.val hw
    rw [hsq]

theorem odd_involution_orbit_product_index
    (E W : Subgroup G) (hWE : W ≤ E) (t : G) (ht : orderOf t = 2)
    (htW : t ∈ Subgroup.normalizer (W : Set G))
    (hfixed : W ⊓ Subgroup.centralizer ({t} : Set G) = ⊥)
    (horbit : ∀ e ∈ E, rightConjugateElem t e * t ∈ W) :
    Odd (Nat.card W) ∧ IsMulCommutative W ∧
    (∀ w ∈ W, rightConjugateElem w t = w⁻¹) ∧
    involutionOrbit E t = involutionOrbit W t ∧
    (∀ e ∈ E, ∃ c ∈ E ⊓ Subgroup.centralizer ({t} : Set G),
      ∃ w ∈ W, e = c * w) ∧
    (E : Set G) = ((E ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) *
      (W : Set G) ∧
    (E ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ W = ⊥ ∧
    (Subgroup.centralizer ({t} : Set G)).relIndex E = Nat.card W := by
  obtain ⟨hodd, hcomm, hinv⟩ :=
    normalized_subgroup_inversion_of_trivial_centralizer W t ht htW hfixed
  have htt : t * t = 1 := by
    have hpow := pow_orderOf_eq_one t
    rw [ht, pow_two] at hpow
    exact hpow
  have hOrbit : involutionOrbit E t = involutionOrbit W t := by
    apply Set.Subset.antisymm
    · rintro s ⟨e, he, rfl⟩
      rw [inverted_odd_subgroup_involution_orbit W t ht hodd hinv]
      exact Set.mem_mul.mpr ⟨rightConjugateElem t e * t, horbit e he,
        t, Set.mem_singleton t, by rw [mul_assoc, htt, mul_one]⟩
    · rintro s ⟨w, hw, hs⟩
      exact ⟨w, hWE hw, hs⟩
  have hfactor : ∀ e ∈ E, ∃ c ∈ E ⊓ Subgroup.centralizer ({t} : Set G),
      ∃ w ∈ W, e = c * w := by
    intro e he
    have heorb : rightConjugateElem t e ∈ involutionOrbit W t := by
      rw [← hOrbit]
      exact ⟨e, he, rfl⟩
    obtain ⟨w, hw, hew⟩ := heorb
    have hc : e * w⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have heq : (e * w⁻¹)⁻¹ * t * (e * w⁻¹) = t := by
        change w⁻¹ * t * w = e⁻¹ * t * e at hew
        calc
          (e * w⁻¹)⁻¹ * t * (e * w⁻¹) = w * (e⁻¹ * t * e) * w⁻¹ := by group
          _ = w * (w⁻¹ * t * w) * w⁻¹ := by rw [← hew]
          _ = t := by group
      have htc : t * (e * w⁻¹) = (e * w⁻¹) * t := by
        have h := congrArg (fun x : G => (e * w⁻¹) * x) heq
        simpa only [mul_assoc, mul_inv_cancel_left] using h
      exact htc.symm
    exact ⟨e * w⁻¹, ⟨E.mul_mem he (E.inv_mem (hWE hw)), hc⟩,
      w, hw, by group⟩
  have hprod : (E : Set G) =
      ((E ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) * (W : Set G) := by
    ext e
    constructor
    · intro he
      obtain ⟨c, hc, w, hw, heq⟩ := hfactor e he
      exact Set.mem_mul.mpr ⟨c, hc, w, hw, heq.symm⟩
    · rintro ⟨c, hc, w, hw, rfl⟩
      exact E.mul_mem hc.1 (hWE hw)
  have hinter : (E ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ W = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    exact hfixed ▸ ⟨hx.2, hx.1.2⟩
  have hindex : (Subgroup.centralizer ({t} : Set G)).relIndex E = Nat.card W := by
    let C := (Subgroup.centralizer ({t} : Set G)).subgroupOf E
    let B := W.subgroupOf E
    have hdis : Disjoint C B := by
      rw [disjoint_iff_inf_le]
      intro e he
      apply Subtype.ext
      have hbot : (e : G) ∈ (⊥ : Subgroup G) := hfixed ▸ ⟨he.2, he.1⟩
      exact hbot
    have hmul : (C : Set E) * (B : Set E) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro e
      obtain ⟨c, hc, w, hw, hcw⟩ := hfactor e e.property
      exact Set.mem_mul.mpr ⟨⟨c, hc.1⟩, hc.2, ⟨w, hWE hw⟩, hw, Subtype.ext hcw.symm⟩
    have hcompl : C.IsComplement' B :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis hmul
    change C.index = Nat.card W
    rw [hcompl.symm.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWE).toEquiv
  exact ⟨hodd, hcomm, hinv, hOrbit, hfactor, hprod, hinter, hindex⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
