module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeBasic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def binarySymThreeSingularShift : Set (↥(binarySymMatrices 3) × ZMod 2) :=
  {p | p.2 = 1 ∧ (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 0}

@[expose] def binarySymThreeAltShift : Set (↥(binarySymMatrices 3) × ZMod 2) :=
  {p | (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3 ∧ p.2 = 1}

namespace BinarySymThreeSingular

@[expose] def symDet (B : 𝕍) : ZMod 2 :=
  binarySymDetThree (B : M₃)

theorem det_eq_symDet (B : 𝕍) : (B : M₃).det = symDet B :=
  det_eq_binarySymDetThree B.2

theorem add_self_eq_zero' (B : 𝕍) : B + B = 0 :=
  Subtype.ext (binary_add_self _)

theorem mem_singularShift_iff (B : 𝕍) (ε : ZMod 2) :
    (B, ε) ∈ binarySymThreeSingularShift ↔ ε = 1 ∧ symDet B = 0 := by
  rw [← det_eq_symDet]
  rfl

theorem eq_of_eq_zero_iff : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b := by
  decide

theorem exists_singular_add : ∀ B : 𝕍, ∃ S : 𝕍, symDet S = 0 ∧ symDet (B + S) = 0 := by
  decide

theorem symDet_eq_zero_of_mem_alt :
    ∀ U : 𝕍, (U : M₃) ∈ binaryAltMatrices 3 → symDet U = 0 := by
  decide

theorem exists_alt_symDet_add_ne_zero : ∀ D : 𝕍, (D : M₃) ∉ binaryAltMatrices 3 →
    ∃ U : 𝕍, (U : M₃) ∈ binaryAltMatrices 3 ∧ symDet (D + U) ≠ 0 := by
  decide

@[expose] def cubeSum (h : 𝕍 → ZMod 2) (B U₁ U₂ U₃ : 𝕍) : ZMod 2 :=
  h B + h (B + U₁) + h (B + U₂) + h (B + U₃) + h (B + U₁ + U₂) + h (B + U₁ + U₃) +
    h (B + U₂ + U₃) + h (B + U₁ + U₂ + U₃)

theorem cubeSum_affine {h : 𝕍 → ZMod 2} {L : 𝕍 →+ 𝕍} {D : 𝕍} (hh : ∀ B, h (L B + D) = h B)
    (B U₁ U₂ U₃ : 𝕍) : cubeSum h (L B + D) (L U₁) (L U₂) (L U₃) = cubeSum h B U₁ U₂ U₃ := by
  have key : ∀ X Z : 𝕍, Z = L X + D → h Z = h X := fun X Z hZ => hZ ▸ hh X
  have t1 := key (B + U₁) (L B + D + L U₁) (by rw [map_add]; abel)
  have t2 := key (B + U₂) (L B + D + L U₂) (by rw [map_add]; abel)
  have t3 := key (B + U₃) (L B + D + L U₃) (by rw [map_add]; abel)
  have t12 := key (B + U₁ + U₂) (L B + D + L U₁ + L U₂) (by rw [map_add, map_add]; abel)
  have t13 := key (B + U₁ + U₃) (L B + D + L U₁ + L U₃) (by rw [map_add, map_add]; abel)
  have t23 := key (B + U₂ + U₃) (L B + D + L U₂ + L U₃) (by rw [map_add, map_add]; abel)
  have t123 := key (B + U₁ + U₂ + U₃) (L B + D + L U₁ + L U₂ + L U₃)
    (by rw [map_add, map_add, map_add]; abel)
  unfold cubeSum
  rw [hh, t1, t2, t3, t12, t13, t23, t123]

@[expose] def altDiff (U : 𝕍) : 𝕍 →+ ZMod 2 where
  toFun X := (X : M₃) 0 0 * (U : M₃) 1 2 + (X : M₃) 1 1 * (U : M₃) 0 2 +
    (X : M₃) 2 2 * (U : M₃) 0 1
  map_zero' := by simp
  map_add' X Y := by
    simp only [AddSubgroup.coe_add, Matrix.add_apply]
    ring

theorem symDet_add_of_mem_alt (X U : 𝕍) (hU : (U : M₃) ∈ binaryAltMatrices 3) :
    symDet (X + U) = symDet X + altDiff U X := by
  have h0 : (U : M₃) 0 0 = 0 := (mem_binaryAltMatrices.1 hU).2 0
  have h1 : (U : M₃) 1 1 = 0 := (mem_binaryAltMatrices.1 hU).2 1
  have h2 : (U : M₃) 2 2 = 0 := (mem_binaryAltMatrices.1 hU).2 2
  simp only [symDet, binarySymDetThree, altDiff, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddSubgroup.coe_add, Matrix.add_apply, h0, h1, h2, add_zero]
  ring

theorem cubeSum_symDet_of_mem_alt (B U V₁ V₂ : 𝕍) (hU : (U : M₃) ∈ binaryAltMatrices 3) :
    cubeSum symDet B U V₁ V₂ = 0 := by
  have h1 := symDet_add_of_mem_alt B U hU
  have h2 := symDet_add_of_mem_alt (B + V₁) U hU
  have h3 := symDet_add_of_mem_alt (B + V₂) U hU
  have h4 := symDet_add_of_mem_alt (B + V₁ + V₂) U hU
  rw [map_add] at h2 h3
  rw [map_add, map_add] at h4
  have e1 : B + U + V₁ = B + V₁ + U := add_right_comm _ _ _
  have e2 : B + U + V₂ = B + V₂ + U := add_right_comm _ _ _
  have e3 : B + U + V₁ + V₂ = B + V₁ + V₂ + U := by abel
  unfold cubeSum
  rw [e3, e1, e2, h1, h2, h3, h4]
  generalize symDet B = a, symDet (B + V₁) = b, symDet (B + V₂) = c, symDet (B + V₁ + V₂) = d,
    altDiff U B = l, altDiff U V₁ = l₁, altDiff U V₂ = l₂
  revert a b c d l l₁ l₂
  decide

theorem exists_cubeSum_ne_zero :
    ∀ U : 𝕍, (U : M₃) ∉ binaryAltMatrices 3 → ∃ V₁ V₂ : 𝕍, cubeSum symDet 0 U V₁ V₂ ≠ 0 := by
  decide +kernel

section Automorphism

variable {e : (𝕍 × ZMod 2) ≃+ (𝕍 × ZMod 2)}

theorem snd_apply (he : ∀ x, e x ∈ binarySymThreeSingularShift ↔ x ∈ binarySymThreeSingularShift)
    (x : 𝕍 × ZMod 2) : (e x).2 = x.2 := by
  have hsnd : ∀ B : 𝕍, symDet B = 0 → (e (B, 1)).2 = 1 := fun B hB =>
    (((mem_singularShift_iff _ _).1 ((he (B, 1)).2 ((mem_singularShift_iff B 1).2 ⟨rfl, hB⟩))).1 :)
  have h0 : ∀ B : 𝕍, (e (B, 0)).2 = 0 := by
    intro B
    obtain ⟨S, hS, hBS⟩ := exists_singular_add B
    have hsum : ((S, 1) : 𝕍 × ZMod 2) + (B + S, 1) = (B, 0) := by
      refine Prod.ext ?_ (show (1 : ZMod 2) + 1 = 0 from rfl)
      change S + (B + S) = B
      rw [add_left_comm, add_self_eq_zero', add_zero]
    rw [← hsum, map_add, Prod.snd_add, hsnd S hS, hsnd (B + S) hBS]
    decide
  obtain ⟨B, ε⟩ := x
  have hε : ε = 0 ∨ ε = 1 := by
    revert ε
    decide
  rcases hε with rfl | rfl
  · exact h0 B
  · have hB : ((B, 1) : 𝕍 × ZMod 2) = (B, 0) + (0, 1) :=
      Prod.ext (add_zero B).symm (zero_add 1).symm
    change (e (B, 1)).2 = 1
    rw [hB, map_add, Prod.snd_add, h0, hsnd 0 (symDet_eq_zero_of_mem_alt 0 (zero_mem _))]
    exact zero_add 1

@[expose] def linPart (e : (𝕍 × ZMod 2) ≃+ (𝕍 × ZMod 2)) : 𝕍 →+ 𝕍 :=
  (AddMonoidHom.fst 𝕍 (ZMod 2)).comp (e.toAddMonoidHom.comp (AddMonoidHom.inl 𝕍 (ZMod 2)))

variable (he : ∀ x, e x ∈ binarySymThreeSingularShift ↔ x ∈ binarySymThreeSingularShift)
include he

theorem apply_zero (B : 𝕍) : e (B, 0) = (linPart e B, 0) :=
  Prod.ext rfl (snd_apply he _)

theorem apply_one (B : 𝕍) : e (B, 1) = (linPart e B + (e (0, 1)).1, 1) := by
  have hB : ((B, 1) : 𝕍 × ZMod 2) = (B, 0) + (0, 1) :=
    Prod.ext (add_zero B).symm (zero_add 1).symm
  rw [hB, map_add, apply_zero he]
  exact Prod.ext rfl (by rw [Prod.snd_add, snd_apply he]; exact zero_add 1)

theorem symDet_linPart_add (B : 𝕍) : symDet (linPart e B + (e (0, 1)).1) = symDet B := by
  refine eq_of_eq_zero_iff _ _ ?_
  have h := he (B, 1)
  rw [apply_one he, mem_singularShift_iff, mem_singularShift_iff] at h
  simpa using h

theorem exists_linPart_add_eq (B' : 𝕍) : ∃ B, linPart e B + (e (0, 1)).1 = B' := by
  refine ⟨(e.symm (B', 1)).1, ?_⟩
  have h1 : (e.symm (B', 1)).2 = 1 := by
    rw [← snd_apply he, AddEquiv.apply_symm_apply]
  have h := e.apply_symm_apply (B', 1)
  rw [← Prod.mk.eta (p := e.symm (B', 1)), h1, apply_one he] at h
  exact congrArg Prod.fst h

theorem exists_linPart_eq (B' : 𝕍) : ∃ B, linPart e B = B' := by
  refine ⟨(e.symm (B', 0)).1, ?_⟩
  have h0 : (e.symm (B', 0)).2 = 0 := by
    rw [← snd_apply he, AddEquiv.apply_symm_apply]
  have h := e.apply_symm_apply (B', 0)
  rw [← Prod.mk.eta (p := e.symm (B', 0)), h0, apply_zero he] at h
  exact congrArg Prod.fst h

theorem linPart_mem_alt {U : 𝕍} (hU : (U : M₃) ∈ binaryAltMatrices 3) :
    (linPart e U : M₃) ∈ binaryAltMatrices 3 := by
  by_contra hLU
  obtain ⟨V₁', V₂', hne⟩ := exists_cubeSum_ne_zero _ hLU
  obtain ⟨B₀, hB₀⟩ := exists_linPart_add_eq he 0
  obtain ⟨V₁, rfl⟩ := exists_linPart_eq he V₁'
  obtain ⟨V₂, rfl⟩ := exists_linPart_eq he V₂'
  rw [← hB₀, cubeSum_affine (symDet_linPart_add he)] at hne
  exact hne (cubeSum_symDet_of_mem_alt B₀ U V₁ V₂ hU)

omit he in
theorem symm_preserves (he : ∀ x, e x ∈ binarySymThreeSingularShift ↔
    x ∈ binarySymThreeSingularShift) (x : 𝕍 × ZMod 2) :
    e.symm x ∈ binarySymThreeSingularShift ↔ x ∈ binarySymThreeSingularShift := by
  rw [← he, AddEquiv.apply_symm_apply]

theorem exists_mem_alt_linPart_eq {U : 𝕍} (hU : (U : M₃) ∈ binaryAltMatrices 3) :
    ∃ U' : 𝕍, (U' : M₃) ∈ binaryAltMatrices 3 ∧ linPart e U' = U := by
  have he' := symm_preserves he
  refine ⟨linPart e.symm U, linPart_mem_alt he' hU, ?_⟩
  have h := e.apply_symm_apply (U, 0)
  rw [apply_zero he', apply_zero he] at h
  exact congrArg Prod.fst h

theorem translation_mem_alt : ((e (0, 1)).1 : M₃) ∈ binaryAltMatrices 3 := by
  by_contra hD
  obtain ⟨U, hU, hne⟩ := exists_alt_symDet_add_ne_zero _ hD
  obtain ⟨U', hU', hLU'⟩ := exists_mem_alt_linPart_eq he hU
  apply hne
  rw [← hLU', add_comm, symDet_linPart_add he]
  exact symDet_eq_zero_of_mem_alt U' hU'

theorem image_altShift : ⇑e '' binarySymThreeAltShift = binarySymThreeAltShift := by
  have hD := translation_mem_alt he
  ext ⟨U, ε⟩
  constructor
  · rintro ⟨⟨B, ε'⟩, ⟨hB, hε'⟩, hx⟩
    change ε' = 1 at hε'
    subst hε'
    rw [apply_one he] at hx
    rw [← hx]
    refine ⟨?_, rfl⟩
    change ((linPart e B + (e (0, 1)).1 : 𝕍) : M₃) ∈ binaryAltMatrices 3
    rw [AddSubgroup.coe_add]
    exact add_mem (linPart_mem_alt he hB) hD
  · rintro ⟨hU, hε⟩
    change ε = 1 at hε
    subst hε
    have hUD : ((U + (e (0, 1)).1 : 𝕍) : M₃) ∈ binaryAltMatrices 3 := by
      rw [AddSubgroup.coe_add]
      exact add_mem hU hD
    obtain ⟨U', hU', hLU'⟩ := exists_mem_alt_linPart_eq he hUD
    refine ⟨(U', 1), ⟨hU', rfl⟩, ?_⟩
    rw [apply_one he, hLU', add_assoc, add_self_eq_zero', add_zero]

end Automorphism

theorem ncard_singularShift : binarySymThreeSingularShift.ncard = 36 := by
  have h : binarySymThreeSingularShift =
      ↑(Finset.univ.filter fun p : 𝕍 × ZMod 2 => p.2 = 1 ∧ symDet p.1 = 0) := by
    ext ⟨B, ε⟩
    rw [mem_singularShift_iff, Finset.coe_filter]
    simp
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem ncard_altShift : binarySymThreeAltShift.ncard = 8 := by
  have h : binarySymThreeAltShift =
      ↑(Finset.univ.filter fun p : 𝕍 × ZMod 2 => (p.1 : M₃) ∈ binaryAltMatrices 3 ∧ p.2 = 1) := by
    ext p
    simp [binarySymThreeAltShift]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

end BinarySymThreeSingular

open BinarySymThreeSingular in
theorem binary_symmetric_three_singular_set_affine_orbit_obstruction :
    binarySymThreeSingularShift.ncard = 36 ∧ binarySymThreeAltShift.ncard = 8 ∧
      (∀ g : (↥(binarySymMatrices 3) × ZMod 2) ≃+ (↥(binarySymMatrices 3) × ZMod 2),
        ⇑g '' binarySymThreeSingularShift = binarySymThreeSingularShift →
          ⇑g '' binarySymThreeAltShift = binarySymThreeAltShift) ∧
      ∀ (G : Type*) [Group G] [DistribMulAction G (↥(binarySymMatrices 3) × ZMod 2)],
        (∀ g : G, (fun x => g • x) '' binarySymThreeSingularShift =
          binarySymThreeSingularShift) →
          ¬ ∀ p ∈ binarySymThreeSingularShift, ∀ q ∈ binarySymThreeSingularShift,
            ∃ g : G, g • p = q := by
  have hstab : ∀ g : (↥(binarySymMatrices 3) × ZMod 2) ≃+ (↥(binarySymMatrices 3) × ZMod 2),
      ⇑g '' binarySymThreeSingularShift = binarySymThreeSingularShift →
        ⇑g '' binarySymThreeAltShift = binarySymThreeAltShift := fun g hg =>
    image_altShift (apply_mem_iff_of_image_eq g.toEquiv hg)
  refine ⟨ncard_singularShift, ncard_altShift, hstab, fun G _ _ hG htrans => ?_⟩
  let E₁₁ : ↥(binarySymMatrices 3) := ⟨!![1, 0, 0; 0, 0, 0; 0, 0, 0], by decide⟩
  have hp : ((0, 1) : ↥(binarySymMatrices 3) × ZMod 2) ∈ binarySymThreeSingularShift :=
    (mem_singularShift_iff _ _).2 ⟨rfl, by decide⟩
  have hq : ((E₁₁, 1) : ↥(binarySymMatrices 3) × ZMod 2) ∈ binarySymThreeSingularShift :=
    (mem_singularShift_iff _ _).2 ⟨rfl, by decide⟩
  obtain ⟨g, hg⟩ := htrans _ hp _ hq
  let e := DistribMulAction.toAddEquiv (↥(binarySymMatrices 3) × ZMod 2) g
  have he : ⇑e = fun x => g • x := funext fun x => DistribMulAction.toAddEquiv_apply _ g x
  have hmem : e ((0, 1) : ↥(binarySymMatrices 3) × ZMod 2) ∈ binarySymThreeAltShift := by
    rw [← hstab e (by rw [he]; exact hG g)]
    exact Set.mem_image_of_mem _ ⟨zero_mem _, rfl⟩
  rw [DistribMulAction.toAddEquiv_apply, hg] at hmem
  exact absurd hmem.1 (by decide)

end CFSG.LocalAnalysis.ComponentInitial
