module

public import CFSG.Dihedral.OriginalOddCore

public noncomputable section

namespace CFSG.DihedralBlueprint

variable {G H : Type} [Group G] [Group H]

theorem subgroup_map_equiv_inverse (e : G ≃* H) (P : Subgroup G) :
    (P.map e.toMonoidHom).map e.symm.toMonoidHom = P := by
  rw [← Subgroup.comap_equiv_eq_map_symm']
  exact Subgroup.comap_map_eq_self_of_injective e.injective P

theorem isSylowIn_map_equiv (e : G ≃* H) (p : ℕ) (P R : Subgroup G)
    (hP : IsSylowIn p P R) :
    IsSylowIn p (P.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  refine ⟨Subgroup.map_mono hP.1, hP.2.1.map e.toMonoidHom, ?_⟩
  intro Q hQR hQp hPQ
  have hback : Q.map e.symm.toMonoidHom ≤ R := by
    have h := Subgroup.map_mono (f := e.symm.toMonoidHom) hQR
    rwa [subgroup_map_equiv_inverse e R] at h
  have hPback : P ≤ Q.map e.symm.toMonoidHom := by
    have h := Subgroup.map_mono (f := e.symm.toMonoidHom) hPQ
    rwa [subgroup_map_equiv_inverse e P] at h
  have heq := hP.2.2 _ hback (hQp.map e.symm.toMonoidHom) hPback
  have h := congrArg (Subgroup.map e.toMonoidHom) heq
  have hinverse : (Q.map e.symm.toMonoidHom).map e.toMonoidHom = Q := by
    simpa only [MulEquiv.symm_symm] using subgroup_map_equiv_inverse e.symm Q
  rwa [hinverse] at h

theorem isSylowIn_map_equiv_iff (e : G ≃* H) (p : ℕ) (P R : Subgroup G) :
    IsSylowIn p (P.map e.toMonoidHom) (R.map e.toMonoidHom) ↔ IsSylowIn p P R := by
  constructor
  · intro h
    have hback := isSylowIn_map_equiv e.symm p _ _ h
    simpa only [subgroup_map_equiv_inverse] using hback
  · exact isSylowIn_map_equiv e p P R

theorem normalizedBy_map_equiv (e : G ≃* H) (P R : Subgroup G)
    (h : NormalizedBy P R) :
    NormalizedBy (P.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  change R.map e.toMonoidHom ≤ Subgroup.normalizer (P.map e.toMonoidHom : Set H)
  rw [← Subgroup.map_normalizer_eq_of_bijective P e.bijective]
  exact Subgroup.map_mono h

theorem normal_subgroupOf_map_equiv (e : G ≃* H) (P R : Subgroup G)
    (hPR : P ≤ R) (h : (P.subgroupOf R).Normal) :
    ((P.map e.toMonoidHom).subgroupOf (R.map e.toMonoidHom)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hPR)).mpr
  exact normalizedBy_map_equiv e P R
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hPR).mp h)

theorem hasNormalTwoComplement_map_equiv (e : G ≃* H) (R : Subgroup G)
    (h : HasNormalTwoComplement R) : HasNormalTwoComplement (R.map e.toMonoidHom) := by
  obtain ⟨P, hPR, hnormal, hodd, a, hindex⟩ := h
  refine ⟨P.map e.toMonoidHom, Subgroup.map_mono hPR,
    normal_subgroupOf_map_equiv e P R hPR hnormal, ?_, a, ?_⟩
  · rwa [Subgroup.card_map_of_injective e.injective]
  · change (P.map e.toMonoidHom).relIndex (R.map e.toMonoidHom) = 2 ^ a
    rw [Subgroup.relIndex_map_map_of_injective P R e.injective]
    exact hindex

theorem hasNormalTwoComplement_map_equiv_iff (e : G ≃* H) (R : Subgroup G) :
    HasNormalTwoComplement (R.map e.toMonoidHom) ↔ HasNormalTwoComplement R := by
  constructor
  · intro h
    have hback := hasNormalTwoComplement_map_equiv e.symm _ h
    simpa only [subgroup_map_equiv_inverse] using hback
  · exact hasNormalTwoComplement_map_equiv e R

variable [Finite G] [Finite H]

omit [Finite H] in
theorem oddCoreOf_map_le_equiv (e : G ≃* H) (R : Subgroup G) :
    (oddCoreOf R).map e.toMonoidHom ≤ oddCoreOf (R.map e.toMonoidHom) := by
  apply normal_odd_le_oddCoreOf _ _ (Subgroup.map_mono (oddCoreOf_le R))
  · exact normal_subgroupOf_map_equiv e _ _ (oddCoreOf_le R) (oddCoreOf_normal R)
  · rw [Subgroup.card_map_of_injective e.injective]
    exact oddCoreOf_odd R

theorem oddCoreOf_map_equiv (e : G ≃* H) (R : Subgroup G) :
    oddCoreOf (R.map e.toMonoidHom) = (oddCoreOf R).map e.toMonoidHom := by
  apply le_antisymm
  · have hback := oddCoreOf_map_le_equiv e.symm (R.map e.toMonoidHom)
    have h := Subgroup.map_mono (f := e.toMonoidHom) hback
    have hinverse :
        ((oddCoreOf (R.map e.toMonoidHom)).map e.symm.toMonoidHom).map e.toMonoidHom =
          oddCoreOf (R.map e.toMonoidHom) := by
      simpa only [MulEquiv.symm_symm] using
        subgroup_map_equiv_inverse e.symm (oddCoreOf (R.map e.toMonoidHom))
    rw [hinverse, subgroup_map_equiv_inverse e R] at h
    exact h
  · exact oddCoreOf_map_le_equiv e R

@[expose] def primeClassPredicate (j : Fin 4) (p : ℕ) (P : Subgroup G) : Prop :=
  let N := Subgroup.normalizer (P : Set G)
  let K := oddCoreOf N
  match j.val with
  | 0 => IsSylowIn p P K ∧ HasNormalTwoComplement N
  | 1 => IsSylowIn p P K ∧ ¬ HasNormalTwoComplement N
  | 2 => IsCyclic P ∧ ¬ IsSylowIn p P K
  | _ => ¬ IsCyclic P ∧ ¬ IsSylowIn p P K

theorem primeClassPredicate_map_equiv_iff (e : G ≃* H) (j : Fin 4)
    (p : ℕ) (P : Subgroup G) :
    primeClassPredicate j p (P.map e.toMonoidHom) ↔ primeClassPredicate j p P := by
  have hN := Subgroup.map_normalizer_eq_of_bijective P (f := e.toMonoidHom) e.bijective
  have hK := oddCoreOf_map_equiv e (Subgroup.normalizer (P : Set G))
  have hcyc : IsCyclic P ↔ IsCyclic (P.map e.toMonoidHom) := (e.subgroupMap P).isCyclic
  have hsyl : IsSylowIn p (P.map e.toMonoidHom)
      (oddCoreOf (Subgroup.normalizer (P.map e.toMonoidHom : Set H))) ↔
      IsSylowIn p P (oddCoreOf (Subgroup.normalizer (P : Set G))) := by
    rw [← hN, hK, isSylowIn_map_equiv_iff]
  have hcomp : HasNormalTwoComplement (Subgroup.normalizer (P.map e.toMonoidHom : Set H)) ↔
      HasNormalTwoComplement (Subgroup.normalizer (P : Set G)) := by
    rw [← hN, hasNormalTwoComplement_map_equiv_iff]
  fin_cases j <;> simp only [primeClassPredicate, hsyl, hcomp, ← hcyc]

end CFSG.DihedralBlueprint
