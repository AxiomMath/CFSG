module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullEverySylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem every_relative_point_sylow_is_sylow [Finite G]
    (M H : Subgroup G) (hHM : H ≤ M)
    (hindex : Odd (H.subgroupOf M).index) (T : Sylow 2 H) :
    ∃ S : Sylow 2 M,
      (S : Subgroup M).map M.subtype = (T : Subgroup H).map H.subtype := by
  let e := (Subgroup.subgroupOfEquivOfLe hHM).symm
  let T' : Sylow 2 (H.subgroupOf M) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨sylowTwoOfOddIndex (H.subgroupOf M) hindex T', ?_⟩
  rw [sylowTwoOfOddIndex_subgroup]
  change ((T : Subgroup H).map e.toMonoidHom |>.map (H.subgroupOf M).subtype).map
    M.subtype = (T : Subgroup H).map H.subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem relative_central_involution_mem_every_point_sylow
    (M H : Subgroup G) (hHM : H ≤ M) (u : G) (huH : u ∈ H)
    (huK : u ∈ Subgroup.centralizer (M : Set G)) (hu : u ^ 2 = 1)
    (T : Sylow 2 H) : u ∈ (T : Subgroup H).map H.subtype := by
  have huHZ : (⟨u, huH⟩ : H) ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp huK h (hHM h.property)
  exact ⟨⟨u, huH⟩,
    central_square_one_mem_every_sylow _ huHZ (Subtype.ext hu) T, rfl⟩

theorem relative_entire_involution_set_image
    (M T : Subgroup G) (hTM : T ≤ M) :
    M.subtype '' {x : M | x ∈ T.subgroupOf M ∧ IsInvolution x} =
      {x : G | x ∈ T ∧ IsInvolution x} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy.1, fun h => hy.2.ne_one (Subtype.ext h),
      congrArg Subtype.val hy.2.sq_eq_one⟩
  · rintro ⟨hxT, hx⟩
    exact ⟨⟨x, hTM hxT⟩,
      ⟨hxT, fun h => hx.ne_one (congrArg Subtype.val h), Subtype.ext hx.sq_eq_one⟩, rfl⟩

theorem relative_entire_root_nonidentity_image
    (M U : Subgroup G) (hUM : U ≤ M) :
    M.subtype '' (((U.subgroupOf M : Subgroup M) : Set M) \ {1}) =
      (U : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy.1, fun h => hy.2 (Subtype.ext h)⟩
  · rintro ⟨hxU, hxone⟩
    exact ⟨⟨x, hUM hxU⟩, ⟨hxU, fun h => hxone (congrArg Subtype.val h)⟩, rfl⟩

theorem relative_omega_one_image_map
    (M T : Subgroup G) (hTM : T ≤ M) :
    ((CFSG.omega₁ (G := T.subgroupOf M) (p := 2)).map (T.subgroupOf M).subtype).map
        M.subtype = (CFSG.omega₁ (G := T) (p := 2)).map T.subtype := by
  rw [omega_one_map_eq_entire_involution_closure,
    MonoidHom.map_closure, relative_entire_involution_set_image M T hTM,
    omega_one_map_eq_entire_involution_closure]

theorem literal_omega_one_eq_subgroupOf_product
    (U T : Subgroup G) (u : G)
    (hOmega : (CFSG.omega₁ (G := T) (p := 2)).map T.subtype = Subgroup.zpowers u ⊔ U) :
    CFSG.omega₁ (G := T) (p := 2) = (Subgroup.zpowers u ⊔ U).subgroupOf T := by
  have h := congrArg (fun A : Subgroup G => A.comap T.subtype) hOmega
  rw [Subgroup.comap_map_eq_self_of_injective T.subtype_injective] at h
  exact h

theorem every_relative_point_sylow_exact_product [Finite G]
    (M L H U : Subgroup G) (hLM : L ≤ M) (hHM : H ≤ M)
    (u : G) (hu : IsInvolution u) (huH : u ∈ H)
    (huK : u ∈ Subgroup.centralizer (M : Set G)) (huL : u ∉ L)
    (hUL : U ≤ L) (hUH : U ≤ H) [IsElementaryAbelian 2 U]
    [(U.subgroupOf H).Normal] (hindex : Odd (H.subgroupOf M).index)
    (hU : (U : Set G) = {1} ∪ {x : G | x ∈ L ∧ x ∈ H ∧ IsInvolution x})
    (hpartition : ∀ x : G, x ∈ M → IsInvolution x →
      x = u ∨ x ∈ L ∨ ∃ l : G, l ∈ L ∧ IsInvolution l ∧ x = u * l) :
    ∀ T : Sylow 2 H,
      let T' := (T : Subgroup H).map H.subtype
      (∃ S : Sylow 2 M, (S : Subgroup M).map M.subtype = T') ∧
      {x : G | x ∈ T' ∧ IsInvolution x} =
        ({u} : Set G) ∪ ((U : Set G) \ {1}) ∪
          ((fun x : G => u * x) '' ((U : Set G) \ {1})) ∧
      (CFSG.omega₁ (G := T') (p := 2)).map T'.subtype = Subgroup.zpowers u ⊔ U ∧
      CFSG.omega₁ (G := T') (p := 2) = (Subgroup.zpowers u ⊔ U).subgroupOf T' ∧
      Disjoint (Subgroup.zpowers u) U ∧
      (∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k) ∧
      IsElementaryAbelian 2 ↥(Subgroup.zpowers u ⊔ U : Subgroup G) ∧
      (∃ e : Subgroup.zpowers u × U ≃*
        ↥((CFSG.omega₁ (G := T') (p := 2)).map T'.subtype),
        ∀ (a : Subgroup.zpowers u) (b : U), (e (a, b) : G) = (a : G) * b) := by
  intro T
  let T' := (T : Subgroup H).map H.subtype
  have hUT : U ≤ T' := normal_root_mem_every_point_sylow H U hUH T
  have huT : u ∈ T' := relative_central_involution_mem_every_point_sylow
    M H hHM u huH huK hu.sq_eq_one T
  have hTH : T' ≤ H := Subgroup.map_subtype_le _
  have hTM : T' ≤ M := hTH.trans hHM
  have hUM : U ≤ M := hUH.trans hHM
  let LM := L.subgroupOf M
  let HM := H.subgroupOf M
  let UM := U.subgroupOf M
  let TM := T'.subgroupOf M
  let uM : M := ⟨u, hHM huH⟩
  have huMI : IsInvolution uM :=
    ⟨fun h => hu.ne_one (congrArg Subtype.val h), Subtype.ext hu.sq_eq_one⟩
  have huMZ : uM ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp huK m m.property
  have huML : uM ∉ LM := huL
  have hULM : UM ≤ LM := fun _ hx => hUL hx
  have hUTM : UM ≤ TM := fun _ hx => hUT hx
  have hTHM : TM ≤ HM := fun _ hx => hTH hx
  have huTM : uM ∈ TM := huT
  have hUMset : (UM : Set M) = {1} ∪ {x : M | x ∈ LM ∧ x ∈ HM ∧ IsInvolution x} := by
    ext x
    constructor
    · intro hx
      have hxset : (x : G) ∈ (U : Set G) := hx
      rw [hU] at hxset
      rcases hxset with hxone | hx
      · exact Or.inl (Subtype.ext hxone)
      · exact Or.inr ⟨hx.1, hx.2.1,
          fun h => hx.2.2.ne_one (congrArg Subtype.val h), Subtype.ext hx.2.2.sq_eq_one⟩
    · rintro (hxone | hx)
      · have h : x = 1 := hxone
        exact h ▸ UM.one_mem
      · change (x : G) ∈ (U : Set G)
        rw [hU]
        exact Or.inr ⟨hx.1, hx.2.1, fun h => hx.2.2.ne_one (Subtype.ext h),
          congrArg Subtype.val hx.2.2.sq_eq_one⟩
  have hpartitionM : ∀ x : M, IsInvolution x →
      x = uM ∨ x ∈ LM ∨ ∃ l : M, l ∈ LM ∧ IsInvolution l ∧ x = uM * l := by
    intro x hx
    have hxG : IsInvolution (x : G) :=
      ⟨fun h => hx.ne_one (Subtype.ext h), congrArg Subtype.val hx.sq_eq_one⟩
    rcases hpartition x x.property hxG with hxu | hxL | ⟨l, hlL, hl, hxl⟩
    · exact Or.inl (Subtype.ext hxu)
    · exact Or.inr (Or.inl hxL)
    · exact Or.inr (Or.inr ⟨⟨l, hLM hlL⟩, hlL,
        ⟨fun h => hl.ne_one (congrArg Subtype.val h), Subtype.ext hl.sq_eq_one⟩, Subtype.ext hxl⟩)
  have hInvM := local_entire_involution_set LM HM UM TM uM huMI huMZ huML
    hULM hUTM hTHM huTM hUMset hpartitionM
  have hrootImage : M.subtype '' ((UM : Set M) \ {1}) = (U : Set G) \ {1} :=
    relative_entire_root_nonidentity_image M U hUM
  have htranslateImage : M.subtype ''
      ((fun x : M => uM * x) '' ((UM : Set M) \ {1})) =
        (fun x : G => u * x) '' ((U : Set G) \ {1}) := by
    rw [← hrootImage, Set.image_image, Set.image_image]
    rfl
  have hInv := congrArg (fun s : Set M => M.subtype '' s) hInvM
  rw [relative_entire_involution_set_image M T' hTM, Set.image_union,
    Set.image_union, Set.image_singleton, hrootImage, htranslateImage] at hInv
  have huUM : uM ∉ UM := fun h => huL (hUL h)
  let : IsElementaryAbelian 2 UM := IsElementaryAbelian.subgroupOf hUM
  obtain ⟨hOmegaM, hdisjM, hcommM, helemM⟩ :=
    local_omega_one_internal_product UM TM uM huMI huMZ huUM hUTM huTM hInvM
  have hOmega := congrArg (fun A : Subgroup M => A.map M.subtype) hOmegaM
  rw [relative_omega_one_image_map M T' hTM, Subgroup.map_sup,
    MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hUM] at hOmega
  have hdisj := Subgroup.disjoint_map M.subtype_injective hdisjM
  rw [MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hUM] at hdisj
  have hcomm : ∀ e ∈ Subgroup.zpowers u, ∀ k ∈ U, Commute e k := by
    intro e he k hk
    have hemap : e ∈ (Subgroup.zpowers uM).map M.subtype := by
      rw [MonoidHom.map_zpowers]
      exact he
    obtain ⟨eM, heM, rfl⟩ := hemap
    have h := hcommM eM heM ⟨k, hUM hk⟩ hk
    rw [commute_iff_eq]
    exact congrArg Subtype.val h.eq
  let := helemM
  have helem : IsElementaryAbelian 2 ↥(Subgroup.zpowers u ⊔ U : Subgroup G) := by
    have h : IsElementaryAbelian 2 ↥((Subgroup.zpowers uM ⊔ UM).map M.subtype) :=
      IsElementaryAbelian.map_subtype (p := 2) (K := M) (H := Subgroup.zpowers uM ⊔ UM)
    rw [Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hUM] at h
    exact h
  exact ⟨every_relative_point_sylow_is_sylow M H hHM hindex T, hInv,
    hOmega, literal_omega_one_eq_subgroupOf_product U T' u hOmega, hdisj, hcomm, helem,
    local_omega_one_product_equivalence U T' u hOmega hdisj hcomm⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
