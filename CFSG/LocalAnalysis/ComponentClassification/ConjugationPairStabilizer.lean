module

public import CFSG.LocalAnalysis.ComponentClassification.CommutingComponentFamily

public section

open scoped Pointwise

namespace CFSG.ComponentClassification.ConjugationPairStabilizer

@[expose, instance_reducible] noncomputable def action {G : Type*} [Group G] : MulAction G (Subgroup G) where
  smul actor subgroup := subgroup.map (MulAut.conj actor).toMonoidHom
  one_smul subgroup := by
    change subgroup.map (MulAut.conj 1).toMonoidHom = subgroup
    have heq : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext member
      simp
    rw [heq, Subgroup.map_id]
  mul_smul first second subgroup := by
    change subgroup.map (MulAut.conj (first * second)).toMonoidHom =
      (subgroup.map (MulAut.conj second).toMonoidHom).map (MulAut.conj first).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext member
    change first * second * member * (first * second)⁻¹ = first * (second * member * second⁻¹) * first⁻¹
    group

@[expose] noncomputable def stabilizer {G : Type*} [Group G] (acting first second : Subgroup G) : Subgroup acting :=
  let := action (G := G)
  MulAction.stabilizer acting ({first, second} : Set (Subgroup G))

@[expose] noncomputable def orbit {G : Type*} [Group G] (acting first second : Subgroup G) : Set (Set (Subgroup G)) :=
  let := action (G := G)
  MulAction.orbit acting ({first, second} : Set (Subgroup G))

theorem odd_index {G : Type*} [Group G] (acting first second : Subgroup G)
    (hodd : Odd (Nat.card ↥(orbit acting first second))) : Odd (stabilizer acting first second).index := by
  let := action (G := G)
  change Odd (Nat.card (acting ⧸ MulAction.stabilizer acting ({first, second} : Set (Subgroup G))))
  rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer acting ({first, second} : Set (Subgroup G)))]
  exact hodd

theorem mem_iff {G : Type*} [Group G] (acting first second : Subgroup G) (actor : acting) :
    actor ∈ stabilizer acting first second ↔
      ({first.map (MulAut.conj actor.val).toMonoidHom, second.map (MulAut.conj actor.val).toMonoidHom} : Set (Subgroup G)) =
        {first, second} := by
  let := action (G := G)
  change actor ∈ MulAction.stabilizer acting ({first, second} : Set (Subgroup G)) ↔ _
  rw [MulAction.mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton]
  rfl

theorem pair_normalizes_product {G : Type*} [Group G] (acting first second : Subgroup G) :
    (stabilizer acting first second).map acting.subtype ≤ Subgroup.normalizer ((first ⊔ second : Subgroup G) : Set G) := by
  rintro actor ⟨lift, hlift, rfl⟩
  apply (CommutingComponentFamily.normalizer_iff_conjugate_eq _ lift.val).mpr
  have hpairs := (mem_iff acting first second lift).mp hlift
  have hsup := congrArg (fun subgroups : Set (Subgroup G) => sSup subgroups) hpairs
  simp only [sSup_pair] at hsup
  rwa [Subgroup.map_sup]

theorem normalized {G : Type*} [Group G] (acting first second actors : Subgroup G)
    (hnormalizes : actors ≤ Subgroup.normalizer (acting : Set G))
    (hfirst : actors ≤ Subgroup.normalizer (first : Set G))
    (hsecond : actors ≤ Subgroup.normalizer (second : Set G)) :
    actors ≤ Subgroup.normalizer (((stabilizer acting first second).map acting.subtype : Subgroup G) : Set G) := by
  apply Subgroup.le_set_normalizer_iff.mpr
  intro actor hactor member hmember
  obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
  have hconjugateActing : actor * lift.val * actor⁻¹ ∈ acting :=
    (Subgroup.mem_normalizer_iff.mp (hnormalizes hactor) lift.val).mp lift.property
  apply Subgroup.mem_map.mpr
  refine ⟨⟨actor * lift.val * actor⁻¹, hconjugateActing⟩, ?_, rfl⟩
  apply (mem_iff acting first second _).mpr
  have hpairs := (mem_iff acting first second lift).mp hlift
  have hfirstEq := (CommutingComponentFamily.normalizer_iff_conjugate_eq first actor).mp (hfirst hactor)
  have hsecondEq := (CommutingComponentFamily.normalizer_iff_conjugate_eq second actor).mp (hsecond hactor)
  have hfirstInv := (CommutingComponentFamily.normalizer_iff_conjugate_eq first actor⁻¹).mp
    ((Subgroup.normalizer _).inv_mem (hfirst hactor))
  have hsecondInv := (CommutingComponentFamily.normalizer_iff_conjugate_eq second actor⁻¹).mp
    ((Subgroup.normalizer _).inv_mem (hsecond hactor))
  have hmapped := congrArg (fun subgroups : Set (Subgroup G) =>
    (fun subgroup : Subgroup G => subgroup.map (MulAut.conj actor).toMonoidHom) '' subgroups) hpairs
  rw [Set.image_pair, Set.image_pair, hfirstEq, hsecondEq] at hmapped
  have hhom : (MulAut.conj (actor * lift.val * actor⁻¹)).toMonoidHom =
      ((MulAut.conj actor).toMonoidHom.comp (MulAut.conj lift.val).toMonoidHom).comp
        (MulAut.conj actor⁻¹).toMonoidHom := by
    ext element
    change (actor * lift.val * actor⁻¹) * element * (actor * lift.val * actor⁻¹)⁻¹ =
      actor * (lift.val * (actor⁻¹ * element * actor⁻¹⁻¹) * lift.val⁻¹) * actor⁻¹
    group
  rw [hhom, ← Subgroup.map_map, ← Subgroup.map_map, hfirstInv,
    ← Subgroup.map_map, ← Subgroup.map_map, hsecondInv]
  exact hmapped

end CFSG.ComponentClassification.ConjugationPairStabilizer
