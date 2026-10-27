module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullThreeOrbits

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u v

variable {G : Type u} [Group G]

theorem centralizer_singleton_conjugacy_class
    (A : Subgroup G) (u : G) (huK : u ∈ Subgroup.centralizer (A : Set G)) :
    conjugacyWithin A u = {u} := by
  ext x
  constructor
  · rintro ⟨a, hax⟩
    rw [Subgroup.mem_centralizer_iff.mp huK (a : G)⁻¹ (A.inv_mem a.property),
      mul_assoc, inv_mul_cancel, mul_one] at hax
    exact hax.symm
  · intro hx
    have hxu := Set.mem_singleton_iff.mp hx
    exact ⟨1, by simpa only [Subgroup.coe_one, inv_one, one_mul, mul_one] using hxu.symm⟩

theorem centralizer_translate_conjugacy_class
    (A : Subgroup G) (u z : G) (huK : u ∈ Subgroup.centralizer (A : Set G)) :
    conjugacyWithin A (u * z) =
      (fun x : G => u * x) '' conjugacyWithin A z := by
  have htranslate (a : A) : (a : G)⁻¹ * (u * z) * a =
      u * ((a : G)⁻¹ * z * a) := by
    rw [← mul_assoc,
      Subgroup.mem_centralizer_iff.mp huK (a : G)⁻¹ (A.inv_mem a.property)]
    simp only [mul_assoc]
  ext x
  constructor
  · rintro ⟨a, hax⟩
    exact ⟨(a : G)⁻¹ * z * a, ⟨a, rfl⟩, (htranslate a).symm.trans hax⟩
  · rintro ⟨y, ⟨a, hay⟩, hyx⟩
    exact ⟨a, (htranslate a).trans (by rw [hay]; exact hyx)⟩

theorem entire_three_orbit_carrier
    {A : Type u} [Group A] {X : Type v} [MulAction A X]
    (S : Set X) (a b c : X)
    (hS : S = MulAction.orbit A a ∪ MulAction.orbit A b ∪ MulAction.orbit A c)
    (hdab : Disjoint (MulAction.orbit A a) (MulAction.orbit A b))
    (hdac : Disjoint (MulAction.orbit A a) (MulAction.orbit A c))
    (hdbc : Disjoint (MulAction.orbit A b) (MulAction.orbit A c)) :
    ∃ p : SubMulAction A X, (p : Set X) = S ∧
      ∃ a' b' c' : p,
        (a' : X) = a ∧ (b' : X) = b ∧ (c' : X) = c ∧
        Subtype.val '' MulAction.orbit A a' = MulAction.orbit A a ∧
        Subtype.val '' MulAction.orbit A b' = MulAction.orbit A b ∧
        Subtype.val '' MulAction.orbit A c' = MulAction.orbit A c ∧
        (∀ x : p, x ∈ MulAction.orbit A a' ∨
          x ∈ MulAction.orbit A b' ∨ x ∈ MulAction.orbit A c') ∧
        Set.range (fun q : MulAction.orbitRel.Quotient A p =>
          Subtype.val '' q.orbit) =
            {MulAction.orbit A a, MulAction.orbit A b, MulAction.orbit A c} ∧
        Nat.card (MulAction.orbitRel.Quotient A p) = 3 := by
  let p : SubMulAction A X := {
    carrier := S
    smul_mem' := by
      intro g x hx
      rw [hS] at hx ⊢
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (MulAction.mem_orbit_of_mem_orbit g hx))
      · exact Or.inl (Or.inr (MulAction.mem_orbit_of_mem_orbit g hx))
      · exact Or.inr (MulAction.mem_orbit_of_mem_orbit g hx) }
  have ha : a ∈ S := hS.symm ▸ Or.inl (Or.inl (MulAction.mem_orbit_self a))
  have hb : b ∈ S := hS.symm ▸ Or.inl (Or.inr (MulAction.mem_orbit_self b))
  have hc : c ∈ S := hS.symm ▸ Or.inr (MulAction.mem_orbit_self c)
  let a' : p := ⟨a, ha⟩
  let b' : p := ⟨b, hb⟩
  let c' : p := ⟨c, hc⟩
  have hIa : Subtype.val '' MulAction.orbit A a' = MulAction.orbit A a :=
    SubMulAction.val_image_orbit a'
  have hIb : Subtype.val '' MulAction.orbit A b' = MulAction.orbit A b :=
    SubMulAction.val_image_orbit b'
  have hIc : Subtype.val '' MulAction.orbit A c' = MulAction.orbit A c :=
    SubMulAction.val_image_orbit c'
  have hcover : ∀ x : p, x ∈ MulAction.orbit A a' ∨
      x ∈ MulAction.orbit A b' ∨ x ∈ MulAction.orbit A c' := by
    intro x
    have hx : (x : X) ∈ S := x.property
    rw [hS] at hx
    rcases hx with (hx | hx) | hx
    · exact Or.inl (SubMulAction.mem_orbit_subMul_iff.mpr hx)
    · exact Or.inr (Or.inl (SubMulAction.mem_orbit_subMul_iff.mpr hx))
    · exact Or.inr (Or.inr (SubMulAction.mem_orbit_subMul_iff.mpr hx))
  have hab : MulAction.orbit A a' ≠ MulAction.orbit A b' := by
    intro h
    have heq := congrArg (fun t : Set p => Subtype.val '' t) h
    rw [hIa, hIb] at heq
    exact Set.disjoint_left.mp hdab (heq ▸ MulAction.mem_orbit_self b) (MulAction.mem_orbit_self b)
  have hac : MulAction.orbit A a' ≠ MulAction.orbit A c' := by
    intro h
    have heq := congrArg (fun t : Set p => Subtype.val '' t) h
    rw [hIa, hIc] at heq
    exact Set.disjoint_left.mp hdac (heq ▸ MulAction.mem_orbit_self c) (MulAction.mem_orbit_self c)
  have hbc : MulAction.orbit A b' ≠ MulAction.orbit A c' := by
    intro h
    have heq := congrArg (fun t : Set p => Subtype.val '' t) h
    rw [hIb, hIc] at heq
    exact Set.disjoint_left.mp hdbc (heq ▸ MulAction.mem_orbit_self c) (MulAction.mem_orbit_self c)
  obtain ⟨hrange, hcount⟩ := entire_three_orbit_quotient a' b' c' hcover hab hac hbc
  refine ⟨p, rfl, a', b', c', rfl, rfl, rfl, hIa, hIb, hIc, hcover, ?_, hcount⟩
  have hrangeimage := congrArg (fun t : Set (Set p) =>
    (fun r : Set p => Subtype.val '' r) '' t) hrange
  simpa only [← Set.range_comp, Function.comp_def, Set.image_insert_eq,
    Set.image_singleton, hIa, hIb, hIc] using hrangeimage

theorem relative_entire_local_three_conjugation_orbits [Finite G]
    (L P U T : Subgroup G) (hPL : P ≤ L)
    (hP : IsStronglyEmbedded (P.subgroupOf L))
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ P ∧ IsInvolution x})
    (u z : G) (huK : u ∈ Subgroup.centralizer (L : Set G)) (huL : u ∉ L)
    (hzP : z ∈ P) (hz : IsInvolution z)
    (hInv : {x : G | x ∈ T ∧ IsInvolution x} =
      ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
        ((fun x : G => u * x) '' ((U : Set G) \ {1}))) :
    let N := L ⊓ Subgroup.normalizer (U : Set G)
    let _ : MulAction N G := MulAction.compHom G
      (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
    ∃ p : SubMulAction N G,
      (p : Set G) = {x : G | x ∈ T ∧ IsInvolution x} ∧
      ∃ a b c : p,
        (a : G) = u ∧ (b : G) = z ∧ (c : G) = u * z ∧
        Subtype.val '' MulAction.orbit N a = {u} ∧
        Subtype.val '' MulAction.orbit N b = (U : Set G) \ {1} ∧
        Subtype.val '' MulAction.orbit N c =
          (fun x : G => u * x) '' ((U : Set G) \ {1}) ∧
        (∀ x : p, x ∈ MulAction.orbit N a ∨
          x ∈ MulAction.orbit N b ∨ x ∈ MulAction.orbit N c) ∧
        Disjoint ({u} : Set G) ((U : Set G) \ {1}) ∧
        Disjoint ({u} : Set G)
          ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
        Disjoint ((U : Set G) \ {1})
          ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
        Set.range (fun q : MulAction.orbitRel.Quotient N p =>
          Subtype.val '' q.orbit) =
            {({u} : Set G), (U : Set G) \ {1},
              (fun x : G => u * x) '' ((U : Set G) \ {1})} ∧
        Nat.card (MulAction.orbitRel.Quotient N p) = 3 := by
  let N := L ⊓ Subgroup.normalizer (U : Set G)
  let _ : MulAction N G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  have huNK : u ∈ Subgroup.centralizer (N : Set G) :=
    Subgroup.centralizer_le (show (N : Set G) ⊆ L from inf_le_left) huK
  have hzU : z ∈ U := by
    rw [show z ∈ U ↔ z ∈ ({1} : Set G) ∪
      {x : G | x ∈ P ∧ IsInvolution x} from Set.ext_iff.mp hU z]
    exact Or.inr ⟨hzP, hz⟩
  have hPU := entire_point_involution_root_normalized P U hU
  have hPclass := entire_point_root_conjugacy_class L P U hPL hP hU z hzP hz
  have hNclass := entire_normalizer_root_conjugacy_class L P U hPL hPU z hzU hz.ne_one hPclass
  have hOu : MulAction.orbit N u = ({u} : Set G) :=
    (conjugation_orbit_eq_conjugacyWithin N u).trans
      (centralizer_singleton_conjugacy_class N u huNK)
  have hOz : MulAction.orbit N z = (U : Set G) \ {1} :=
    (conjugation_orbit_eq_conjugacyWithin N z).trans hNclass
  have hOuz : MulAction.orbit N (u * z) =
      (fun x : G => u * x) '' ((U : Set G) \ {1}) := by
    rw [conjugation_orbit_eq_conjugacyWithin,
      centralizer_translate_conjugacy_class N u z huNK, hNclass]
  have hrootL : (U : Set G) \ {1} ⊆ {x : G | x ∈ L ∧ IsInvolution x} := by
    rintro x ⟨hxU, hxone⟩
    rw [hU] at hxU
    rcases hxU with hx | hx
    · exact (hxone hx).elim
    · exact ⟨hPL hx.1, hx.2⟩
  obtain ⟨hdu, hdut, hdrt⟩ := hull_involution_three_sets_disjoint L u huL
  have hd1 := hdu.mono_right hrootL
  have hd2 := hdut.mono_right (Set.image_mono hrootL)
  have hd3 := hdrt.mono hrootL (Set.image_mono hrootL)
  have hcover : {x : G | x ∈ T ∧ IsInvolution x} =
      MulAction.orbit N u ∪ MulAction.orbit N z ∪ MulAction.orbit N (u * z) := by
    rw [hOu, hOz, hOuz, hInv]
  obtain ⟨p, hp, a, b, c, ha, hb, hc, hIa, hIb, hIc, hwhole, hrange, hcount⟩ :=
    entire_three_orbit_carrier _ u z (u * z) hcover
      (by rw [hOu, hOz]; exact hd1)
      (by rw [hOu, hOuz]; exact hd2)
      (by rw [hOz, hOuz]; exact hd3)
  rw [hOu] at hIa
  rw [hOz] at hIb
  rw [hOuz] at hIc
  rw [hOu, hOz, hOuz] at hrange
  exact ⟨p, hp, a, b, c, ha, hb, hc, hIa, hIb, hIc, hwhole, hd1, hd2, hd3, hrange, hcount⟩

theorem relative_entire_class_intersections
    (L U T : Subgroup G) (u z : G)
    (hu : u ^ 2 = 1) (huK : u ∈ Subgroup.centralizer (L : Set G))
    (hUT : U ≤ T) (huT : u ∈ T)
    (hroot : (U : Set G) \ {1} = {x : G | x ∈ T ∧ x ∈ L ∧ IsInvolution x})
    (hLclass : conjugacyWithin L z = {x : G | x ∈ L ∧ IsInvolution x}) :
    conjugacyWithin L u ∩ (T : Set G) = {u} ∧
      conjugacyWithin L z ∩ (T : Set G) = (U : Set G) \ {1} ∧
      conjugacyWithin L (u * z) ∩ (T : Set G) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [centralizer_singleton_conjugacy_class L u huK]
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (Set.mem_singleton_iff.mp hx).symm ▸ huT⟩⟩
  · rw [hLclass, hroot]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  · rw [centralizer_translate_conjugacy_class L u z huK, hLclass]
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
