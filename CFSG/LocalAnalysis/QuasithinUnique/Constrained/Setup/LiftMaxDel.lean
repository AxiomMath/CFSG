module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxTransport

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Equiv CFSG.ABGLocalTools

section DeletedStabilizer

variable {G : Type*} [Group G]

theorem isSylowOf_map {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ} [Fact p.Prime]
    {P K : Subgroup X} (h : IsSylowOf p P K) (f : X →* Y) :
    IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem deleted_stabilizer_facts [Finite G] (h5 : Fintype.card Ω = 5) {B L U Q R : Subgroup G}
    (ψ : ↥B ≃* Perm Ω) (hLB : L ≤ B) (hUL : U ≤ L) (hUQ : U ≤ Q)
    (hψL : (L.subgroupOf B).map ψ.toMonoidHom = alternatingGroup Ω)
    (hU : IsSylowOf 2 U L) (hQn : Q ≤ Subgroup.normalizer (U : Set G))
    (hR : R = Subgroup.normalizer (U : Set G) ⊓ B) :
    ∃ ω : Ω, (∀ q ∈ Q.subgroupOf B, ψ q ω = ω) ∧
      (∀ ω' : Ω, (∀ q ∈ Q.subgroupOf B, ψ q ω' = ω') → ω' = ω) ∧
      (R.subgroupOf B).map ψ.toMonoidHom = MulAction.stabilizer (Perm Ω) ω ∧
      ((R ⊓ L).subgroupOf B).map ψ.toMonoidHom =
        alternatingGroup Ω ⊓ MulAction.stabilizer (Perm Ω) ω ∧
      R.relIndex B = 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUB : U ≤ B := hUL.trans hLB
  have hU' : IsSylowOf 2 (U.subgroupOf B) (L.subgroupOf B) := by
    refine (isSylowOf_map_subtype_iff (p := 2) B (A := U.subgroupOf B) (B := L.subgroupOf B)).1 ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hUB, Subgroup.map_subgroupOf_eq_of_le hLB]
    exact hU
  have hψU : IsSylowOf 2 ((U.subgroupOf B).map ψ.toMonoidHom) (alternatingGroup Ω) := by
    have := isSylowOf_map hU' ψ.toMonoidHom
    rwa [hψL] at this
  have hcard : Nat.card ((U.subgroupOf B).map ψ.toMonoidHom) = 4 := card_sylow_alt_five h5 hψU
  have hsign : ∀ σ ∈ (U.subgroupOf B).map ψ.toMonoidHom, Perm.sign σ = 1 := fun σ hσ =>
    Perm.mem_alternatingGroup.1 (hψU.le hσ)
  obtain ⟨ω, hωfix, huniq, hnorm⟩ := alt5_order_four h5 hsign hcard
  have hmapN : (Subgroup.normalizer ((U.subgroupOf B : Subgroup ↥B) : Set ↥B)).map
      ψ.toMonoidHom = Subgroup.normalizer
        (((U.subgroupOf B).map ψ.toMonoidHom : Subgroup (Perm Ω)) : Set (Perm Ω)) :=
    Subgroup.map_normalizer_eq_of_bijective _ ψ.bijective
  have hRN : R.subgroupOf B = Subgroup.normalizer ((U.subgroupOf B : Subgroup ↥B) : Set ↥B) := by
    rw [normalizer_subgroupOf_eq hUB, hR]
    ext x
    simp [Subgroup.mem_subgroupOf]
  have hstab : (R.subgroupOf B).map ψ.toMonoidHom = MulAction.stabilizer (Perm Ω) ω := by
    rw [hRN, hmapN]
    ext g
    rw [hnorm g, MulAction.mem_stabilizer_iff]
    rfl
  refine ⟨ω, ?_, ?_, hstab, ?_, ?_⟩
  · intro q hq
    have hqN : q ∈ Subgroup.normalizer ((U.subgroupOf B : Subgroup ↥B) : Set ↥B) :=
      (mem_normalizer_subgroupOf_iff hUB q).2 (hQn (show (q : G) ∈ Q from hq))
    have : ψ.toMonoidHom q ∈ Subgroup.normalizer
        (((U.subgroupOf B).map ψ.toMonoidHom : Subgroup (Perm Ω)) : Set (Perm Ω)) := by
      rw [← hmapN]
      exact ⟨q, hqN, rfl⟩
    exact (hnorm _).1 this
  · intro ω' hω'
    apply huniq
    rintro σ ⟨u, hu, rfl⟩
    exact hω' u (show (u : G) ∈ Q from hUQ hu)
  · rw [inf_subgroupOf', Subgroup.map_inf _ _ _ ψ.injective, hstab, hψL, inf_comm]
  · show (R.subgroupOf B).index = 5
    rw [← Subgroup.index_map_equiv (R.subgroupOf B) ψ]
    show ((R.subgroupOf B).map ψ.toMonoidHom).index = 5
    rw [hstab, MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, h5]

end DeletedStabilizer

end CFSG.QuasithinUnique.Setup.Lift
