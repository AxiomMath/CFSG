module

public import CFSG.LieType.Ree.StandardParabolicData
public import CFSG.LieType.Ree.ReducedWordBorelExtraction

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem fixedOrbitElement_injective :
    Function.Injective t.fixedOrbitElement := by
  have h01 : F4.fixedOrbitElement ⟨0, by decide⟩ ≠ F4.fixedOrbitElement ⟨1, by decide⟩ := by
    intro h
    have h8 := orderOf_F4_fixedOrbitElement_mul
    rw [h, fixedOrbitElement_mul_self, orderOf_one] at h8
    exact absurd h8 (by decide)
  intro i j h
  cases t
  · have hi : (i : ℕ) < 1 := i.2
    have hj : (j : ℕ) < 1 := j.2
    exact Fin.ext (by omega)
  · obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    change i < 2 at hi
    change j < 2 at hj
    interval_cases i <;> interval_cases j
    · rfl
    · exact absurd h h01
    · exact absurd h.symm h01
    · rfl

theorem canonicalRep_list_prod_mem_reeParabolic
    {J : Set (Fin t.fixedOrbitCount)} :
    ∀ ω : List (Fin t.fixedOrbitCount), (∀ j ∈ ω, j ∈ J) →
      canonicalRep (coxeterSystem t.tag) K (ω.map t.fixedOrbitElement).prod ∈
        t.reeParabolic K a J
  | [], _ => by
    rw [List.map_nil, List.prod_nil, canonicalRep_one]
    exact one_mem _
  | i :: ω, hω => by
    obtain ⟨h, hh, e⟩ := exists_canonicalRep_inv_mul_eq (K := K) (a := a)
      (fixedOrbitElement_mem i)
      (mul_mem (fixedOrbitElement_mem i) (list_prod_map_fixedOrbitElement_mem ω))
    rw [inv_mul_cancel_left] at e
    rw [List.map_cons, List.prod_cons, eq_mul_of_inv_mul_eq e]
    exact mul_mem (t.canonicalRep_mem_reeParabolic K a (hω i List.mem_cons_self))
      (mul_mem (canonicalRep_list_prod_mem_reeParabolic ω fun j hj =>
          hω j (List.mem_cons_of_mem _ hj))
        (t.reeFixedBorel_le_reeParabolic K a J (reeFixedTorus_le_reeFixedBorel hh)))

theorem reeParabolic_le_reeGamma_inf
    {J : Set (Fin t.fixedOrbitCount)}
    {i : Fin t.fixedOrbitCount} (hJ : J ⊆ {i}) :
    t.reeParabolic K a J ≤ t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet i) := by
  refine sup_le (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup i)
    ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, rfl⟩
  obtain rfl : j = i := hJ hj
  exact canonicalRep_fixedOrbitElement_mem_reeGamma_inf j

theorem canonicalRep_mem_reeParabolic_iff
    {J : Set (Fin t.fixedOrbitCount)}
    {j : Fin t.fixedOrbitCount} :
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeParabolic K a J ↔
      j ∈ J := by
  refine ⟨fun h => ?_, t.canonicalRep_mem_reeParabolic K a⟩
  by_contra hj
  have hnD : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
      t.reeFixedBruhatCell K a (t.fixedOrbitElement j) :=
    mem_reeFixedBruhatCell.2 ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩
  rcases J.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · rw [reeParabolic_empty] at h
    exact Set.disjoint_left.1 (disjoint_reeFixedBorel_reeFixedBruhatCell j) h hnD
  · have hij : i ≠ j := fun e => hj (e ▸ hi)
    have hJ : J ⊆ {i} := fun k hk => by
      have hr : t.fixedOrbitCount ≤ 2 := by cases t <;> decide
      have hkj : (k : ℕ) ≠ j := fun e => hj (Fin.ext e ▸ hk)
      have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
      have := k.2
      have := i.2
      have := j.2
      exact Fin.ext (by omega)
    have h' := reeParabolic_le_reeGamma_inf (K := K) (a := a) hJ h
    rw [← SetLike.mem_coe, coe_reeGamma_inf_parabolicSubgroup] at h'
    rcases h' with hB | hD
    · exact Set.disjoint_left.1 (disjoint_reeFixedBorel_reeFixedBruhatCell j) hB hnD
    · exact Set.disjoint_left.1
        (disjoint_reeFixedBruhatCell fun e => hij (fixedOrbitElement_injective e)) hD hnD

theorem ree_Borel_overgroup_classification
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (A : Subgroup (ModGL t.tag K)) (hBA : t.reeFixedBorel K a ≤ A)
    (hAΓ : A ≤ t.reeGamma K a) :
    A = t.reeParabolic K a
        {j | canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A} ∧
      ∃! J : Set (Fin t.fixedOrbitCount), A = t.reeParabolic K a J := by
  have hA : A = t.reeParabolic K a
      {j | canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A} := by
    refine le_antisymm (fun g hg => ?_) (sup_le hBA ((Subgroup.closure_le _).2 ?_))
    · have hgΓ : g ∈ (t.reeGamma K a : Set (ModGL t.tag K)) := hAΓ hg
      rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hgΓ
      obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hgΓ
      obtain ⟨b, hb, b', hb', rfl⟩ := mem_reeFixedBruhatCell.1 hgw
      have hnA : canonicalRep (coxeterSystem t.tag) K w ∈ A := by
        have e : canonicalRep (coxeterSystem t.tag) K w =
            b⁻¹ * (b * canonicalRep (coxeterSystem t.tag) K w * b') * b'⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem (hBA hb)) hg) (inv_mem (hBA hb'))
      have hwA : (t.reeFixedBorel K a).map
          (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w)).toMonoidHom ≤ A := by
        rintro _ ⟨x, hx, rfl⟩
        exact mul_mem (mul_mem hnA (hBA hx)) (inv_mem hnA)
      obtain ⟨k, hk⟩ := exists_fixedRelElt_eq hw
      have hred : (t.fixedRelWord k).length = t.fixedRelLength w := by
        rw [← hk, fixedRelLength_fixedRelElt]
      have hnP := canonicalRep_list_prod_mem_reeParabolic (K := K) (a := a)
        (J := {j | canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ A})
        (t.fixedRelWord k) (ree_reduced_word_Borel_extraction t a K A hBA hwA _ hk hred)
      change canonicalRep (coxeterSystem t.tag) K (t.fixedRelElt k) ∈ _ at hnP
      rw [hk] at hnP
      exact mul_mem (mul_mem (t.reeFixedBorel_le_reeParabolic K a _ hb) hnP)
        (t.reeFixedBorel_le_reeParabolic K a _ hb')
    · rintro _ ⟨j, hj, rfl⟩
      exact hj
  refine ⟨hA, _, hA, fun J hJ => ?_⟩
  ext j
  rw [Set.mem_ofPred_eq, hJ, canonicalRep_mem_reeParabolic_iff]

end ReeTag

end CFSG.LieType.Ree
