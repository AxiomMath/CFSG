module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometry
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem entire_point_involution_root_normalized
    (P U : Subgroup G)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ P ∧ IsInvolution x}) :
    P ≤ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro p hp x hx
  change x ∈ (U : Set G) at hx
  change p * x * p⁻¹ ∈ (U : Set G)
  rw [hU] at hx ⊢
  rcases hx with hx | hx
  · have hxone := Set.mem_singleton_iff.mp hx
    subst x
    exact Or.inl (by simp)
  · refine Or.inr ⟨P.mul_mem (P.mul_mem hp hx.1) (P.inv_mem hp), ?_⟩
    have h := isInvolution_rightConjugateElem (g := p⁻¹) hx.2
    simpa only [rightConjugateElem, inv_inv] using h

theorem entire_point_root_conjugacy_class [Finite G]
    (L P U : Subgroup G) (hPL : P ≤ L)
    (hP : IsStronglyEmbedded (P.subgroupOf L))
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ P ∧ IsInvolution x})
    (z : G) (hzP : z ∈ P) (hz : IsInvolution z) :
    conjugacyWithin P z = (U : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨p, hpx⟩
    have hxP : x ∈ P := hpx ▸ P.mul_mem (P.mul_mem (P.inv_mem p.property) hzP) p.property
    have hx : IsInvolution x := hpx ▸ isInvolution_rightConjugateElem hz
    refine ⟨?_, hx.ne_one⟩
    rw [hU]
    exact Or.inr ⟨hxP, hx⟩
  · rintro ⟨hxU, hxone⟩
    rw [hU] at hxU
    rcases hxU with hx | hx
    · exact (hxone hx).elim
    · have hzL : z ∈ L := hPL hzP
      have hxL : x ∈ L := hPL hx.1
      obtain ⟨p, hp, hpx⟩ := hP.involutions_conjugate_in
        (a := (⟨z, hzL⟩ : L)) (b := (⟨x, hxL⟩ : L))
        hzP (IsInvolution.subtype hz hzL) hx.1 (IsInvolution.subtype hx.2 hxL)
      exact ⟨⟨p, hp⟩, congrArg Subtype.val hpx⟩

theorem entire_hull_involution_conjugacy_class [Finite G]
    (L P : Subgroup G) (hP : IsStronglyEmbedded (P.subgroupOf L))
    (z : G) (hzL : z ∈ L) (hz : IsInvolution z) :
    conjugacyWithin L z = {x : G | x ∈ L ∧ IsInvolution x} := by
  ext x
  constructor
  · rintro ⟨l, hlx⟩
    exact ⟨hlx ▸ L.mul_mem (L.mul_mem (L.inv_mem l.property) hzL) l.property,
      hlx ▸ isInvolution_rightConjugateElem hz⟩
  · rintro ⟨hxL, hx⟩
    obtain ⟨l, hlx⟩ := hP.involutions_conjugate
      (IsInvolution.subtype hz hzL) (IsInvolution.subtype hx hxL)
    exact ⟨l, congrArg Subtype.val hlx⟩

theorem entire_normalizer_root_conjugacy_class
    (L P U : Subgroup G) (hPL : P ≤ L)
    (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (z : G) (hzU : z ∈ U) (hz : z ≠ 1)
    (hPclass : conjugacyWithin P z = (U : Set G) \ {1}) :
    conjugacyWithin (L ⊓ Subgroup.normalizer (U : Set G)) z = (U : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨n, hnx⟩
    have hxU : x ∈ U := hnx ▸
      (Subgroup.mem_normalizer_iff''.mp n.property.2 z).mp hzU
    refine ⟨hxU, ?_⟩
    intro hxone
    apply hz
    have h := congrArg (fun y : G => (n : G) * y * (n : G)⁻¹) (hnx.trans hxone)
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
      one_mul, mul_one] using h
  · intro hx
    obtain ⟨p, hpx⟩ := Set.ext_iff.mp hPclass x |>.mpr hx
    exact ⟨⟨p, hPL p.property, hPU p.property⟩, hpx⟩

theorem central_involution_conjugacy_class
    (A : Subgroup G) (u : G) (huZ : u ∈ Subgroup.center G) :
    conjugacyWithin A u = {u} := by
  ext x
  constructor
  · rintro ⟨a, hax⟩
    rw [Subgroup.mem_center_iff.mp huZ (a : G)⁻¹, mul_assoc,
      inv_mul_cancel, mul_one] at hax
    exact hax.symm
  · intro hx
    have hxu := Set.mem_singleton_iff.mp hx
    exact ⟨1, by simpa only [Subgroup.coe_one, inv_one, one_mul, mul_one] using hxu.symm⟩

theorem central_translate_conjugacy_class
    (A : Subgroup G) (u z : G) (huZ : u ∈ Subgroup.center G) :
    conjugacyWithin A (u * z) =
      (fun x : G => u * x) '' conjugacyWithin A z := by
  have htranslate (a : A) : (a : G)⁻¹ * (u * z) * a =
      u * ((a : G)⁻¹ * z * a) := by
    rw [← mul_assoc, Subgroup.mem_center_iff.mp huZ (a : G)⁻¹]
    simp only [mul_assoc]
  ext x
  constructor
  · rintro ⟨a, hax⟩
    exact ⟨(a : G)⁻¹ * z * a, ⟨a, rfl⟩, (htranslate a).symm.trans hax⟩
  · rintro ⟨y, ⟨a, hay⟩, hyx⟩
    exact ⟨a, (htranslate a).trans (by rw [hay]; exact hyx)⟩

theorem conjugation_orbit_eq_conjugacyWithin (A : Subgroup G) (x : G) :
    let _ : MulAction A G := MulAction.compHom G
      (ConjAct.toConjAct.toMonoidHom.comp A.subtype)
    MulAction.orbit A x = conjugacyWithin A x := by
  let _ : MulAction A G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp A.subtype)
  ext y
  constructor
  · rintro ⟨a, hay⟩
    refine ⟨a⁻¹, ?_⟩
    change (a : G) * x * (a : G)⁻¹ = y at hay
    simpa only [Subgroup.coe_inv, inv_inv] using hay
  · rintro ⟨a, hay⟩
    refine ⟨a⁻¹, ?_⟩
    change (a : G)⁻¹ * x * (a : G)⁻¹⁻¹ = y
    simpa only [inv_inv] using hay

theorem entire_class_intersections
    (L U T : Subgroup G) (u z : G)
    (hu : u ^ 2 = 1) (huZ : u ∈ Subgroup.center G)
    (hUT : U ≤ T) (huT : u ∈ T)
    (hroot : (U : Set G) \ {1} = {x : G | x ∈ T ∧ x ∈ L ∧ IsInvolution x})
    (hLclass : conjugacyWithin L z = {x : G | x ∈ L ∧ IsInvolution x}) :
    conjugacyWithin L u ∩ (T : Set G) = {u} ∧
      conjugacyWithin L z ∩ (T : Set G) = (U : Set G) \ {1} ∧
      conjugacyWithin L (u * z) ∩ (T : Set G) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [central_involution_conjugacy_class L u huZ]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (Set.mem_singleton_iff.mp hx).symm ▸ huT⟩⟩
  · rw [hLclass, hroot]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  · rw [central_translate_conjugacy_class L u z huZ, hLclass]
    ext x
    constructor
    · rintro ⟨⟨l, hl, rfl⟩, hxT⟩
      have hlT : l ∈ T := by
        have h := T.mul_mem huT hxT
        simpa only [← mul_assoc, ← pow_two, hu, one_mul] using h
      exact ⟨l, hroot.symm ▸ ⟨hlT, hl⟩, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      have hlrootmem : l ∈ {x : G | x ∈ T ∧ x ∈ L ∧ IsInvolution x} := hroot ▸ hl
      have hlroot : l ∈ T ∧ l ∈ L ∧ IsInvolution l := hlrootmem
      exact ⟨⟨l, hlroot.2, rfl⟩, T.mul_mem huT (hUT hl.1)⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
