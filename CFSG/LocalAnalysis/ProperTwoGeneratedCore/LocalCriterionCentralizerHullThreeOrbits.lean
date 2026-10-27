module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOrbits
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullPartition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u v

theorem entire_three_orbit_quotient
    {A : Type u} [Group A] {X : Type v} [MulAction A X]
    (a b c : X)
    (hcover : ∀ x : X, x ∈ MulAction.orbit A a ∨
      x ∈ MulAction.orbit A b ∨ x ∈ MulAction.orbit A c)
    (hab : MulAction.orbit A a ≠ MulAction.orbit A b)
    (hac : MulAction.orbit A a ≠ MulAction.orbit A c)
    (hbc : MulAction.orbit A b ≠ MulAction.orbit A c) :
    Set.range (MulAction.orbitRel.Quotient.orbit :
      MulAction.orbitRel.Quotient A X → Set X) =
        {MulAction.orbit A a, MulAction.orbit A b, MulAction.orbit A c} ∧
      Nat.card (MulAction.orbitRel.Quotient A X) = 3 := by
  have hrange : Set.range (MulAction.orbitRel.Quotient.orbit :
      MulAction.orbitRel.Quotient A X → Set X) =
        {MulAction.orbit A a, MulAction.orbit A b, MulAction.orbit A c} := by
    ext s
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn'
      rename_i x
      rw [MulAction.orbitRel.Quotient.orbit_mk]
      rcases hcover x with hx | hx | hx
      · exact Or.inl (MulAction.orbit_eq_iff.mpr hx)
      · exact Or.inr (Or.inl (MulAction.orbit_eq_iff.mpr hx))
      · exact Or.inr (Or.inr (MulAction.orbit_eq_iff.mpr hx))
    · rintro (hs | hs | hs)
      · exact ⟨Quotient.mk'' a, by simpa only [MulAction.orbitRel.Quotient.orbit_mk] using hs.symm⟩
      · exact ⟨Quotient.mk'' b, by simpa only [MulAction.orbitRel.Quotient.orbit_mk] using hs.symm⟩
      · exact ⟨Quotient.mk'' c, by simpa only [MulAction.orbitRel.Quotient.orbit_mk] using hs.symm⟩
  refine ⟨hrange, ?_⟩
  rw [← Set.ncard_range_of_injective MulAction.orbitRel.Quotient.orbit_injective, hrange]
  have hnot : MulAction.orbit A a ∉
      ({MulAction.orbit A b, MulAction.orbit A c} : Set (Set X)) := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using And.intro hab hac
  rw [Set.ncard_insert_of_notMem hnot, Set.ncard_pair hbc]

theorem entire_local_three_conjugation_orbits {G : Type u} [Group G] [Finite G]
    (L P U T : Subgroup G) (hPL : P ≤ L)
    (hP : IsStronglyEmbedded (P.subgroupOf L))
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ P ∧ IsInvolution x})
    (u z : G) (huZ : u ∈ Subgroup.center G) (huL : u ∉ L)
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
  have hzU : z ∈ U := by
    rw [show z ∈ U ↔ z ∈ ({1} : Set G) ∪
      {x : G | x ∈ P ∧ IsInvolution x} from Set.ext_iff.mp hU z]
    exact Or.inr ⟨hzP, hz⟩
  have hzroot : z ∈ (U : Set G) \ {1} := ⟨hzU, hz.ne_one⟩
  have hPU := entire_point_involution_root_normalized P U hU
  have hPclass := entire_point_root_conjugacy_class L P U hPL hP hU z hzP hz
  have hNclass := entire_normalizer_root_conjugacy_class L P U hPL hPU z hzU hz.ne_one hPclass
  have hOu : MulAction.orbit N u = ({u} : Set G) :=
    (conjugation_orbit_eq_conjugacyWithin N u).trans
      (central_involution_conjugacy_class N u huZ)
  have hOz : MulAction.orbit N z = (U : Set G) \ {1} :=
    (conjugation_orbit_eq_conjugacyWithin N z).trans hNclass
  have hOuz : MulAction.orbit N (u * z) =
      (fun x : G => u * x) '' ((U : Set G) \ {1}) := by
    rw [conjugation_orbit_eq_conjugacyWithin,
      central_translate_conjugacy_class N u z huZ, hNclass]
  have hcoverG : {x : G | x ∈ T ∧ IsInvolution x} =
      MulAction.orbit N u ∪ MulAction.orbit N z ∪ MulAction.orbit N (u * z) := by
    rw [hOu, hOz, hOuz, hInv]
  let p : SubMulAction N G := {
    carrier := {x : G | x ∈ T ∧ IsInvolution x}
    smul_mem' := by
      intro n x hx
      rw [hcoverG] at hx ⊢
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (MulAction.mem_orbit_of_mem_orbit n hx))
      · exact Or.inl (Or.inr (MulAction.mem_orbit_of_mem_orbit n hx))
      · exact Or.inr (MulAction.mem_orbit_of_mem_orbit n hx) }
  have huInv : u ∈ {x : G | x ∈ T ∧ IsInvolution x} := by
    rw [hInv]
    exact Or.inl (Or.inl rfl)
  have hzInv : z ∈ {x : G | x ∈ T ∧ IsInvolution x} := by
    rw [hInv]
    exact Or.inl (Or.inr hzroot)
  have huzInv : u * z ∈ {x : G | x ∈ T ∧ IsInvolution x} := by
    rw [hInv]
    exact Or.inr ⟨z, hzroot, rfl⟩
  let a : p := ⟨u, huInv⟩
  let b : p := ⟨z, hzInv⟩
  let c : p := ⟨u * z, huzInv⟩
  have hIa : Subtype.val '' MulAction.orbit N a = ({u} : Set G) :=
    (SubMulAction.val_image_orbit a).trans hOu
  have hIb : Subtype.val '' MulAction.orbit N b = (U : Set G) \ {1} :=
    (SubMulAction.val_image_orbit b).trans hOz
  have hIc : Subtype.val '' MulAction.orbit N c =
      (fun x : G => u * x) '' ((U : Set G) \ {1}) :=
    (SubMulAction.val_image_orbit c).trans hOuz
  have hcover : ∀ x : p, x ∈ MulAction.orbit N a ∨
      x ∈ MulAction.orbit N b ∨ x ∈ MulAction.orbit N c := by
    intro x
    have hx : (x : G) ∈ {y : G | y ∈ T ∧ IsInvolution y} := x.property
    rw [hcoverG] at hx
    rcases hx with (hx | hx) | hx
    · exact Or.inl (SubMulAction.mem_orbit_subMul_iff.mpr hx)
    · exact Or.inr (Or.inl (SubMulAction.mem_orbit_subMul_iff.mpr hx))
    · exact Or.inr (Or.inr (SubMulAction.mem_orbit_subMul_iff.mpr hx))
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
  have hab : MulAction.orbit N a ≠ MulAction.orbit N b := by
    intro h
    have heq := congrArg (fun s : Set p => Subtype.val '' s) h
    rw [hIa, hIb] at heq
    exact Set.disjoint_left.mp hd1 (heq ▸ hzroot) hzroot
  have hac : MulAction.orbit N a ≠ MulAction.orbit N c := by
    intro h
    have heq := congrArg (fun s : Set p => Subtype.val '' s) h
    rw [hIa, hIc] at heq
    have hmem : u * z ∈ (fun x : G => u * x) '' ((U : Set G) \ {1}) := ⟨z, hzroot, rfl⟩
    exact Set.disjoint_left.mp hd2 (heq ▸ hmem) hmem
  have hbc : MulAction.orbit N b ≠ MulAction.orbit N c := by
    intro h
    have heq := congrArg (fun s : Set p => Subtype.val '' s) h
    rw [hIb, hIc] at heq
    have hmem : u * z ∈ (fun x : G => u * x) '' ((U : Set G) \ {1}) := ⟨z, hzroot, rfl⟩
    exact Set.disjoint_left.mp hd3 (heq ▸ hmem) hmem
  obtain ⟨hrange, hcount⟩ := entire_three_orbit_quotient a b c hcover hab hac hbc
  refine ⟨p, rfl, a, b, c, rfl, rfl, rfl, hIa, hIb, hIc, hcover,
    hd1, hd2, hd3, ?_, hcount⟩
  have hrangeimage := congrArg (fun s : Set (Set p) =>
    (fun t : Set p => Subtype.val '' t) '' s) hrange
  simpa only [← Set.range_comp, Function.comp_def, Set.image_insert_eq,
    Set.image_singleton, hIa, hIb, hIc] using hrangeimage

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
