module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStar

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

@[expose] def pairFlipRootMap [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightPairFlipFiber H z beta → conjugacyWithin H z := fun s =>
  ⟨((s : G) * t)⁻¹ * z * ((s : G) * t),
    ⟨⟨(s : G) * t, by
      have hsprod : (s : G) * t ∈ rightPairFlipProducts H z beta t :=
        ⟨s, s.property, rfl⟩
      have hpair := ((involution_point_uniform_pair_flips h beta hbeta).2.2 t ht).1 hsprod
      have hp := hpair.1
      rw [rightCosetStabilizer_base H] at hp
      exact hp⟩, rfl⟩⟩

theorem pairFlipRootMap_bijective [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    Function.Bijective (pairFlipRootMap h hbeta ht) := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, (involution_point_uniform_pair_flips h beta hbeta).1⟩
  intro x
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨k, hk, _⟩ := ((involution_point_uniform_pair_flips h beta hbeta).2.2 t ht).2 a
  obtain ⟨s, hs, hsk⟩ := k.property
  change s * t = (k : G) at hsk
  refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
  change (s * t)⁻¹ * z * (s * t) = x
  rw [hsk]
  have hkC : (k : G) * (a : G)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    (mem_rightCoset_iff (s := (Subgroup.centralizer ({z} : Set G) : Set G)) (a : G)).mp hk
  exact (right_conjugates_eq_iff.mpr hkC).trans ha

def pairFlipRootEquiv [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    rightPairFlipFiber H z beta ≃ conjugacyWithin H z :=
  Equiv.ofBijective (pairFlipRootMap h hbeta ht) (pairFlipRootMap_bijective h hbeta ht)

theorem pair_flip_root_formula_equivariant (s z t a : G)
    (haz : Commute a z) (hat : Commute a t) :
    ((a⁻¹ * s * a) * t)⁻¹ * z * ((a⁻¹ * s * a) * t) =
      a⁻¹ * ((s * t)⁻¹ * z * (s * t)) * a := by
  have hprod : (a⁻¹ * s * a) * t = a⁻¹ * (s * t) * a := by
    calc
      _ = a⁻¹ * s * (a * t) := by group
      _ = a⁻¹ * s * (t * a) := by rw [hat.eq]
      _ = _ := by group
  rw [hprod]
  calc
    _ = a⁻¹ * ((s * t)⁻¹ * (a * z * a⁻¹) * (s * t)) * a := by group
    _ = _ := by rw [haz.mul_inv_cancel]

theorem pairFlipRootEquiv_mem_centralizer_iff [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (A : Subgroup G) (hAB : A ≤ pairPointStabilizer H beta)
    (hzA : z ∈ Subgroup.centralizer (A : Set G))
    (htA : t ∈ Subgroup.centralizer (A : Set G))
    (s : rightPairFlipFiber H z beta) :
    (pairFlipRootEquiv h hbeta ht s : G) ∈ Subgroup.centralizer (A : Set G) ↔
      (s : G) ∈ Subgroup.centralizer (A : Set G) := by
  let e := pairFlipRootEquiv h hbeta ht
  constructor
  · intro hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    let sa : rightPairFlipFiber H z beta :=
      ⟨a⁻¹ * (s : G) * a, pair_group_conjugate_flip_mem h.distinguished_order hbeta ht
        s.property ((pairPointStabilizer_le_pairFlipGroup H beta t) (hAB ha))⟩
    have haz : Commute a z := Subgroup.mem_centralizer_iff.mp hzA a ha
    have hat : Commute a t := Subgroup.mem_centralizer_iff.mp htA a ha
    have hax : Commute a (e s : G) := Subgroup.mem_centralizer_iff.mp hx a ha
    have heq : e sa = e s := by
      apply Subtype.ext
      change ((a⁻¹ * (s : G) * a) * t)⁻¹ * z * ((a⁻¹ * (s : G) * a) * t) = (e s : G)
      rw [pair_flip_root_formula_equivariant (s : G) z t a haz hat]
      exact hax.inv_mul_cancel
    have hsa : a⁻¹ * (s : G) * a = s := congrArg Subtype.val (e.injective heq)
    have hh := congrArg (fun x : G => a * x) hsa
    simpa only [mul_assoc, mul_inv_cancel_left] using hh.symm
  · intro hs
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    have has : Commute a (s : G) := Subgroup.mem_centralizer_iff.mp hs a ha
    have haz : Commute a z := Subgroup.mem_centralizer_iff.mp hzA a ha
    have hat : Commute a t := Subgroup.mem_centralizer_iff.mp htA a ha
    have hf : a⁻¹ * (e s : G) * a = e s := by
      change a⁻¹ * (((s : G) * t)⁻¹ * z * ((s : G) * t)) * a =
        ((s : G) * t)⁻¹ * z * ((s : G) * t)
      rw [← pair_flip_root_formula_equivariant (s : G) z t a haz hat, has.inv_mul_cancel]
    have hh := congrArg (fun x : G => a * x) hf
    simpa only [mul_assoc, mul_inv_cancel_left] using hh.symm

theorem original_fixed_flip_card_eq_root_card [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (A : Subgroup G) (hAB : A ≤ pairPointStabilizer H beta)
    (hzA : z ∈ Subgroup.centralizer (A : Set G))
    (htA : t ∈ Subgroup.centralizer (A : Set G)) :
    Nat.card {s : G // s ∈ rightPairFlipFiber H z beta ∧ s ∈ Subgroup.centralizer (A : Set G)} =
      Nat.card {x : G // x ∈ conjugacyWithin H z ∧ x ∈ Subgroup.centralizer (A : Set G)} := by
  let e := pairFlipRootEquiv h hbeta ht
  let p (s : rightPairFlipFiber H z beta) :=
    pairFlipRootEquiv_mem_centralizer_iff h hbeta ht A hAB hzA htA s
  let f : {s : G // s ∈ rightPairFlipFiber H z beta ∧ s ∈ Subgroup.centralizer (A : Set G)} ≃
      {x : G // x ∈ conjugacyWithin H z ∧ x ∈ Subgroup.centralizer (A : Set G)} :=
    { toFun := fun s => ⟨e ⟨s, s.property.1⟩,
        (e ⟨s, s.property.1⟩).property, (p ⟨s, s.property.1⟩).mpr s.property.2⟩
      invFun := fun x => ⟨e.symm ⟨x, x.property.1⟩,
        (e.symm ⟨x, x.property.1⟩).property, by
          apply (p (e.symm ⟨x, x.property.1⟩)).mp
          change (e (e.symm ⟨x, x.property.1⟩) : G) ∈ Subgroup.centralizer (A : Set G)
          rw [e.apply_symm_apply]
          exact x.property.2⟩
      left_inv := by
        intro s
        apply Subtype.ext
        change (e.symm (e ⟨s, s.property.1⟩) : G) = s
        rw [e.symm_apply_apply]
      right_inv := by
        intro x
        apply Subtype.ext
        change (e (e.symm ⟨x, x.property.1⟩) : G) = x
        rw [e.apply_symm_apply] }
  exact Nat.card_congr f

end CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
