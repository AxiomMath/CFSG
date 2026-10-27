module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingLocal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

open scoped Classical

theorem between_alternating_normal {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : Subgroup (Equiv.Perm Ω)) (hK : alternatingGroup Ω ≤ K) : K.Normal :=
  Subgroup.Normal.of_commutator_le (Equiv.Perm Ω)
    (alternatingGroup.commutator_perm_le.trans hK)

theorem normalizerSubtype_comap {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (P : Subgroup K) :
    (Subgroup.normalizer (P.map K.subtype : Set (Equiv.Perm Ω))).comap K.subtype =
      Subgroup.normalizer (P : Set K) := by
  rw [Subgroup.comap_normalizer_eq_of_le_range (Subgroup.map_le_range K.subtype P),
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

@[expose] def normalizerSubtypeHom {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (P : Subgroup K) :
    Subgroup.normalizer (P : Set K) →*
      Subgroup.normalizer (P.map K.subtype : Set (Equiv.Perm Ω)) where
  toFun g := ⟨g.val.val, Subgroup.le_normalizer_map K.subtype
    (Subgroup.mem_map_of_mem K.subtype g.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem normalizerSubtypeHom_injective {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (P : Subgroup K) : Function.Injective (normalizerSubtypeHom K P) := by
  intro g h heq
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : Subgroup.normalizer (P.map K.subtype : Set (Equiv.Perm Ω)) =>
    x.val) heq

theorem normalizerSubtypeHom_range {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (P : Subgroup K) :
    (normalizerSubtypeHom K P).range = K.subgroupOf
      (Subgroup.normalizer (P.map K.subtype : Set (Equiv.Perm Ω))) := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    exact h.val.property
  · intro hg
    let k : K := ⟨g.val, hg⟩
    have hk : k ∈ Subgroup.normalizer (P : Set K) := by
      rw [← normalizerSubtype_comap K P]
      exact g.property
    exact ⟨⟨k, hk⟩, Subtype.ext rfl⟩

@[expose] def normalizerSubtypeEquiv {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (P : Subgroup K) :
    Subgroup.normalizer (P : Set K) ≃*
      K.subgroupOf (Subgroup.normalizer (P.map K.subtype : Set (Equiv.Perm Ω))) where
  toFun g := ⟨normalizerSubtypeHom K P g, g.val.property⟩
  invFun g := ⟨⟨g.val.val, g.property⟩, by
    rw [← normalizerSubtype_comap K P]
    exact g.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem normalizerSubtypeEquiv_coe {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (P : Subgroup K) (g : Subgroup.normalizer (P : Set K)) :
    (normalizerSubtypeEquiv K P g).val = normalizerSubtypeHom K P g := rfl

theorem fixedPoints_subtype_map {Ω : Type*} (K : Subgroup (Equiv.Perm Ω))
    (P : Subgroup K) :
    MulAction.fixedPoints (P.map K.subtype) Ω = MulAction.fixedPoints P Ω := by
  ext x
  rw [MulAction.mem_fixedPoints, MulAction.mem_fixedPoints]
  constructor
  · intro h g
    exact h ⟨g.val.val, Subgroup.mem_map_of_mem K.subtype g.property⟩
  · intro h g
    obtain ⟨k, hk, hkg⟩ := g.property
    change g.val x = x
    rw [← hkg]
    exact h ⟨k, hk⟩

theorem between_normalizer_pComponent_map {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : Subgroup (Equiv.Perm Ω)) (hK : alternatingGroup Ω ≤ K)
    (p : ℕ) [Fact p.Prime] (P : Subgroup K)
    (L : Subgroup (Subgroup.normalizer (P : Set K))) (hL : CFSG.IsPComponent p L) :
    CFSG.IsPComponent p (L.map (normalizerSubtypeHom K P)) := by
  let : K.Normal := between_alternating_normal K hK
  let H := Subgroup.normalizer (P.map K.subtype : Set (Equiv.Perm Ω))
  let R := K.subgroupOf H
  let : R.Normal := inferInstance
  let e := normalizerSubtypeEquiv K P
  have h := pComponent_of_normal_subgroup p R (L.map e.toMonoidHom)
    (pComponent_map_equiv p e L hL)
  rwa [Subgroup.map_map] at h

theorem between_normalizer_pComponent {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : Subgroup (Equiv.Perm Ω)) (hK : alternatingGroup Ω ≤ K)
    (p : ℕ) [Fact p.Prime] (P : Subgroup K) (hP : IsPGroup p P)
    (L : Subgroup (Subgroup.normalizer (P : Set K))) (hL : CFSG.IsPComponent p L) :
    5 ≤ Nat.card (MulAction.fixedPoints P Ω) ∧
      L.map (K.subtype.comp (Subgroup.normalizer (P : Set K)).subtype) =
        (alternatingGroup (MulAction.fixedPoints P Ω)).map Equiv.Perm.ofSubtype ∧
      CFSG.IsQuasisimple L := by
  let Q := P.map K.subtype
  let H := Subgroup.normalizer (Q : Set (Equiv.Perm Ω))
  let f := normalizerSubtypeHom K P
  obtain ⟨hdegree, heq, hquasi⟩ := symmetric_normalizer_pComponent p Q (hP.map K.subtype)
    (L.map f) (between_normalizer_pComponent_map K hK p P L hL)
  have hambient := congrArg (Subgroup.map H.subtype) heq
  rw [Subgroup.map_map, Subgroup.map_map] at hambient
  change L.map (K.subtype.comp (Subgroup.normalizer (P : Set K)).subtype) =
    (alternatingGroup (MulAction.fixedPoints Q Ω)).map Equiv.Perm.ofSubtype at hambient
  rw [fixedPoints_subtype_map K P] at hdegree hambient
  refine ⟨hdegree, hambient, quasisimple_iff_native.mpr ?_⟩
  exact Components.quasisimple_of_equiv
    (L.equivMapOfInjective f (normalizerSubtypeHom_injective K P))
    (quasisimple_iff_native.mp hquasi)

theorem between_normalizer_badSubgroup_eq_bot {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : Subgroup (Equiv.Perm Ω)) (hK : alternatingGroup Ω ≤ K)
    (P : Subgroup K) (hP : IsPGroup 2 P) :
    TwoComponents.badSubgroup (Subgroup.normalizer (P : Set K)) = ⊥ := by
  apply le_bot_iff.mp
  apply sSup_le
  intro L hL
  exact (hL.2 (quasisimple_iff_native.mp
    (between_normalizer_pComponent K hK 2 P hP L
      ((pComponent_two_iff L).mpr hL.1)).2.2)).elim

end CFSG.ComponentClassification.CatalogueBAlternating
