module

public import CFSG.RankThree.PerfectCover.HopfFormula

public noncomputable section

namespace CFSG.LieType.Multipliers

open Subgroup CFSG.RankThree.PerfectCover CFSG.Open
open scoped commutatorElement

universe u v

section Defs

variable {X : Type v} [Group X] {ι : Type u}

structure IsPresentation (g : ι → X) (R : Set (FreeGroup ι)) : Prop where
  lift_surjective : Function.Surjective (FreeGroup.lift g)
  ker_lift : (FreeGroup.lift g).ker = normalClosure R

@[expose] def coverRelators (R : Set (FreeGroup ι)) (w : ι → FreeGroup ι) : Set (FreeGroup ι) :=
  {x | ∃ i : ι, ∃ r ∈ R, ⁅FreeGroup.of i, r⁆ = x} ∪ Set.range fun i => (FreeGroup.of i)⁻¹ * w i

abbrev PresentedCover (R : Set (FreeGroup ι)) (w : ι → FreeGroup ι) : Type u :=
  PresentedGroup (coverRelators R w)

theorem commutator_mem_coverRelators {R : Set (FreeGroup ι)} (w : ι → FreeGroup ι) (i : ι)
    {r : FreeGroup ι} (hr : r ∈ R) : ⁅FreeGroup.of i, r⁆ ∈ coverRelators R w :=
  Or.inl ⟨i, r, hr, rfl⟩

theorem inv_of_mul_mem_coverRelators (R : Set (FreeGroup ι)) (w : ι → FreeGroup ι) (i : ι) :
    (FreeGroup.of i)⁻¹ * w i ∈ coverRelators R w :=
  Or.inr ⟨i, rfl⟩

theorem lift_coverRelators_eq_one_iff {E : Type*} [Group E] {e : ι → E}
    {R : Set (FreeGroup ι)} {w : ι → FreeGroup ι} :
    (∀ r ∈ coverRelators R w, FreeGroup.lift e r = 1) ↔
      (∀ i, ∀ r ∈ R, ⁅e i, FreeGroup.lift e r⁆ = 1) ∧ ∀ i, FreeGroup.lift e (w i) = e i := by
  constructor
  · intro h
    refine ⟨fun i r hr => ?_, fun i => ?_⟩
    · simpa using h _ (commutator_mem_coverRelators w i hr)
    · have := h _ (inv_of_mul_mem_coverRelators R w i)
      rw [map_mul, map_inv, FreeGroup.lift_apply_of, inv_mul_eq_one] at this
      exact this.symm
  · rintro ⟨h₁, h₂⟩ x (⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩)
    · simpa using h₁ i r hr
    · rw [map_mul, map_inv, FreeGroup.lift_apply_of, h₂, inv_mul_cancel]

end Defs

namespace IsPresentation

variable {X : Type v} [Group X] {ι : Type u} {g : ι → X} {R : Set (FreeGroup ι)}

theorem lift_eq_one (hP : IsPresentation g R) {r : FreeGroup ι} (hr : r ∈ R) :
    FreeGroup.lift g r = 1 := by
  rw [← MonoidHom.mem_ker, hP.ker_lift]
  exact subset_normalClosure hr

theorem of_bijective (h : ∀ r ∈ R, FreeGroup.lift g r = 1)
    (hb : Function.Bijective (PresentedGroup.toGroup h)) : IsPresentation g R := by
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨y, rfl⟩ := hb.2 x
    obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective R y
    exact ⟨f, rfl⟩
  · refine le_antisymm (fun f hf => ?_) (PresentedGroup.closure_rels_subset_ker h)
    rw [← PresentedGroup.mk_eq_one_iff]
    exact hb.1 (by rw [map_one]; exact hf)

theorem presentedGroup (R : Set (FreeGroup ι)) :
    IsPresentation (PresentedGroup.of : ι → PresentedGroup R) R := by
  have hl : FreeGroup.lift (PresentedGroup.of : ι → PresentedGroup R) = PresentedGroup.mk R :=
    FreeGroup.ext_hom _ _ fun _ => FreeGroup.lift_apply_of
  have h : ∀ r ∈ R, FreeGroup.lift (PresentedGroup.of : ι → PresentedGroup R) r = 1 := fun r hr =>
    hl ▸ PresentedGroup.one_of_mem hr
  have hid : PresentedGroup.toGroup h = MonoidHom.id _ :=
    PresentedGroup.ext fun i => PresentedGroup.toGroup.of h
  exact of_bijective h (by rw [hid]; exact Function.bijective_id)

theorem of_card_le [Finite (PresentedGroup R)] (h : ∀ r ∈ R, FreeGroup.lift g r = 1)
    (hgen : closure (Set.range g) = ⊤) (hcard : Nat.card (PresentedGroup R) ≤ Nat.card X) :
    IsPresentation g R := by
  have hs : Function.Surjective (PresentedGroup.toGroup h) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of h⟩
  exact of_bijective h (hs.bijective_of_nat_card_le hcard)

end IsPresentation

section Hom

private theorem map_mem_commutator {G H : Type*} [Group G] [Group H] (f : G →* H) {x : G}
    (hx : x ∈ commutator G) : f x ∈ commutator H := by
  have h := mem_map_of_mem f hx
  rw [map_commutator_eq] at h
  rw [_root_.commutator_def]
  exact commutator_mono le_top le_top h

private theorem eq_of_mem_commutator {G E S : Type*} [Group G] [Group E] [Group S] (q : E →* S)
    (hker : q.ker ≤ center E) (φ φ' : G →* E) (h : q.comp φ = q.comp φ') {x : G}
    (hx : x ∈ commutator G) : φ x = φ' x := by
  have hc : ∀ y, (φ y)⁻¹ * φ' y ∈ center E := fun y => hker <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, h, MonoidHom.comp_apply,
      inv_mul_cancel]
  have hle : commutator G ≤ MonoidHom.eqLocus φ φ' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change φ ⁅a, b⁆ = φ' ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have ha : φ' a = φ a * ((φ a)⁻¹ * φ' a) := by group
    have hb : φ' b = φ b * ((φ b)⁻¹ * φ' b) := by group
    rw [ha, hb, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hc a) (hc b)]
  exact hle hx

private theorem hom_ext_of_perfect {G E S : Type*} [Group G] [Group E] [Group S]
    [Group.IsPerfect G] (q : E →* S) (hker : q.ker ≤ center E) {φ φ' : G →* E}
    (h : q.comp φ = q.comp φ') : φ = φ' :=
  MonoidHom.ext fun _ => eq_of_mem_commutator q hker φ φ' h (by simp)

end Hom

section Cover

variable {X : Type} [Group X] {ι : Type u} {g : ι → X} {R : Set (FreeGroup ι)}
  {w : ι → FreeGroup ι}

theorem isPerfect_of_isPresentation (hP : IsPresentation g R)
    (hw : ∀ i, w i ∈ commutator (FreeGroup ι)) (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    Group.IsPerfect X := by
  rw [Group.isPerfect_def, eq_top_iff]
  rintro x -
  obtain ⟨f, rfl⟩ := hP.lift_surjective x
  have hgen : ∀ i, g i ∈ commutator X := fun i => by
    rw [← hwg i]
    exact map_mem_commutator _ (hw i)
  induction f using FreeGroup.induction_on with
  | one => simp
  | of i => simpa using hgen i
  | inv_of i => simpa using hgen i
  | mul _ _ h₁ h₂ => rw [map_mul]; exact mul_mem h₁ h₂

theorem lift_coverRelators_eq_one (hP : IsPresentation g R)
    (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    ∀ r ∈ coverRelators R w, FreeGroup.lift g r = 1 :=
  lift_coverRelators_eq_one_iff.mpr
    ⟨fun _ _ hr => by rw [hP.lift_eq_one hr, commutatorElement_one_right], hwg⟩

@[expose] def coverMap (hP : IsPresentation g R) (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    PresentedCover R w →* X :=
  PresentedGroup.toGroup (lift_coverRelators_eq_one hP hwg)

@[simp]
theorem coverMap_of (hP : IsPresentation g R) (hwg : ∀ i, FreeGroup.lift g (w i) = g i) (i : ι) :
    coverMap hP hwg (PresentedGroup.of i) = g i :=
  PresentedGroup.toGroup.of _

@[simp]
theorem coverMap_mk (hP : IsPresentation g R) (hwg : ∀ i, FreeGroup.lift g (w i) = g i)
    (f : FreeGroup ι) : coverMap hP hwg (PresentedGroup.mk _ f) = FreeGroup.lift g f :=
  rfl

theorem coverMap_surjective (hP : IsPresentation g R) (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    Function.Surjective (coverMap hP hwg) := fun x => by
  obtain ⟨f, rfl⟩ := hP.lift_surjective x
  exact ⟨PresentedGroup.mk _ f, rfl⟩

theorem mk_mem_center (w : ι → FreeGroup ι) {r : FreeGroup ι} (hr : r ∈ R) :
    PresentedGroup.mk (coverRelators R w) r ∈ center (PresentedCover R w) := by
  rw [← centralizer_univ, ← coe_top, ← PresentedGroup.closure_range_of, centralizer_closure,
    mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h := PresentedGroup.one_of_mem (commutator_mem_coverRelators w i hr)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem coverMap_ker_le_center (hP : IsPresentation g R)
    (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    (coverMap hP hwg).ker ≤ center (PresentedCover R w) := by
  intro x hx
  obtain ⟨f, rfl⟩ := PresentedGroup.mk_surjective _ x
  have hf : f ∈ normalClosure R := by
    rw [← hP.ker_lift]
    exact hx
  have hmap : (normalClosure R).map (PresentedGroup.mk (coverRelators R w)) ≤
      center (PresentedCover R w) := by
    rw [map_normalClosure _ _ (PresentedGroup.mk_surjective _)]
    exact normalClosure_le_normal (by rintro _ ⟨r, hr, rfl⟩; exact mk_mem_center w hr)
  exact hmap (mem_map_of_mem _ hf)

theorem presentedCover_isPerfect (hw : ∀ i, w i ∈ commutator (FreeGroup ι)) :
    Group.IsPerfect (PresentedCover R w) := by
  rw [Group.isPerfect_def, eq_top_iff, ← PresentedGroup.closure_range_of, closure_le]
  rintro _ ⟨i, rfl⟩
  have h : PresentedGroup.of i = PresentedGroup.mk (coverRelators R w) (w i) :=
    PresentedGroup.mk_eq_mk_of_inv_mul_mem (inv_of_mul_mem_coverRelators R w i)
  rw [h]
  exact map_mem_commutator _ (hw i)

theorem isPerfectCentralExtension_coverMap (hP : IsPresentation g R)
    (hw : ∀ i, w i ∈ commutator (FreeGroup ι)) (hwg : ∀ i, FreeGroup.lift g (w i) = g i) :
    IsPerfectCentralExtension X (coverMap hP hwg) :=
  ⟨⟨coverMap_surjective hP hwg, coverMap_ker_le_center hP hwg⟩,
    (presentedCover_isPerfect hw).commutator_eq_top⟩

variable (hP : IsPresentation g R) (hw : ∀ i, w i ∈ commutator (FreeGroup ι))
  (hwg : ∀ i, FreeGroup.lift g (w i) = g i)

private def hopfGen : ι → HopfCover X :=
  haveI := isPerfect_of_isPresentation hP hw hwg
  fun i => FreeGroup.lift (fun j => Function.surjInv hopfCoverMap_surjective (g j)) (w i)

private theorem hopfCoverMap_comp_lift_hopfGen :
    (hopfCoverMap X).comp (FreeGroup.lift (hopfGen hP hw hwg)) = FreeGroup.lift g := by
  have := isPerfect_of_isPresentation hP hw hwg
  refine FreeGroup.ext_hom _ _ fun i => ?_
  rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, hopfGen,
    ← MonoidHom.comp_apply, ← hwg i]
  congr 1
  refine FreeGroup.ext_hom _ _ fun j => ?_
  simp [Function.surjInv_eq hopfCoverMap_surjective]

private theorem lift_hopfGen_coverRelators :
    ∀ r ∈ coverRelators R w, FreeGroup.lift (hopfGen hP hw hwg) r = 1 := by
  have := isPerfect_of_isPresentation hP hw hwg
  have hq := hopfCoverMap_comp_lift_hopfGen hP hw hwg
  refine lift_coverRelators_eq_one_iff.mpr ⟨fun i r hr => ?_, fun i => ?_⟩
  · have hc : FreeGroup.lift (hopfGen hP hw hwg) r ∈ center (HopfCover X) := by
      refine hopfMultiplier_le_center ?_
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hq]
      exact hP.lift_eq_one hr
    exact (commutatorElement_eq_one_iff_mul_comm).mpr (mem_center_iff.mp hc _)
  · set l : ι → HopfCover X := fun j => Function.surjInv hopfCoverMap_surjective (g j)
    have hl : (hopfCoverMap X).comp (FreeGroup.lift (hopfGen hP hw hwg)) =
        (hopfCoverMap X).comp (FreeGroup.lift l) := by
      rw [hq]
      refine FreeGroup.ext_hom _ _ fun j => ?_
      simp [l, Function.surjInv_eq hopfCoverMap_surjective]
    exact eq_of_mem_commutator _ hopfMultiplier_le_center _ _ hl (hw i)

private def toHopfCover : PresentedCover R w →* HopfCover X :=
  PresentedGroup.toGroup (lift_hopfGen_coverRelators hP hw hwg)

private theorem hopfCoverMap_comp_toHopfCover :
    (hopfCoverMap X).comp (toHopfCover hP hw hwg) = coverMap hP hwg := by
  refine PresentedGroup.ext fun i => ?_
  rw [MonoidHom.comp_apply, toHopfCover, PresentedGroup.toGroup.of, coverMap_of,
    ← FreeGroup.lift_apply_of (f := hopfGen hP hw hwg), ← MonoidHom.comp_apply,
    hopfCoverMap_comp_lift_hopfGen, FreeGroup.lift_apply_of]

def presentedCoverEquiv : PresentedCover R w ≃* HopfCover X :=
  haveI := isPerfect_of_isPresentation hP hw hwg
  haveI := presentedCover_isPerfect (R := R) hw
  haveI := hopfCover_isPerfect (S := X)
  have hπ := isPerfectCentralExtension_coverMap hP hw hwg
  MonoidHom.toMulEquiv (toHopfCover hP hw hwg) (hopfLift _ hπ.1.1 hπ.1.2)
    (hom_ext_of_perfect _ hπ.1.2 <| by
      rw [MonoidHom.comp_id, ← MonoidHom.comp_assoc, comp_hopfLift,
        hopfCoverMap_comp_toHopfCover])
    (hom_ext_of_perfect _ hopfMultiplier_le_center <| by
      rw [MonoidHom.comp_id, ← MonoidHom.comp_assoc, hopfCoverMap_comp_toHopfCover,
        comp_hopfLift])

theorem hopfCoverMap_presentedCoverEquiv (x : PresentedCover R w) :
    hopfCoverMap X (presentedCoverEquiv hP hw hwg x) = coverMap hP hwg x := by
  rw [← hopfCoverMap_comp_toHopfCover hP hw hwg, MonoidHom.comp_apply]
  unfold presentedCoverEquiv
  rfl

def hopfMultiplierEquivKer : hopfMultiplier X ≃* (coverMap hP hwg).ker :=
  ((presentedCoverEquiv hP hw hwg).subgroupMap (coverMap hP hwg).ker |>.trans <|
    MulEquiv.subgroupCongr <| by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
        rw [MonoidHom.mem_ker]
        rw [MonoidHom.coe_ofClass, hopfCoverMap_presentedCoverEquiv, hx]
      · intro hu
        refine ⟨(presentedCoverEquiv hP hw hwg).symm u, ?_, MulEquiv.apply_symm_apply _ u⟩
        rw [MonoidHom.mem_ker] at hu
        rw [SetLike.mem_coe, MonoidHom.mem_ker]
        rw [← hopfCoverMap_presentedCoverEquiv hP hw hwg, MulEquiv.apply_symm_apply, hu]).symm

def griessHopfMultiplierEquivKer : griessHopfMultiplier X ≃* (coverMap hP hwg).ker :=
  (hopfMultiplierEquivGriess X).trans (hopfMultiplierEquivKer hP hw hwg)

include hw in
theorem coverMap_ker_mulEquiv_griessHopfMultiplier :
    Nonempty (griessHopfMultiplier X ≃* (coverMap hP hwg).ker) :=
  ⟨griessHopfMultiplierEquivKer hP hw hwg⟩

include hP hw hwg in
theorem card_presentedCover :
    Nat.card (PresentedCover R w) = Nat.card X * Nat.card (griessHopfMultiplier X) := by
  rw [(coverMap hP hwg).ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (coverMap_surjective hP hwg)).toEquiv,
    Nat.card_congr (griessHopfMultiplierEquivKer hP hw hwg).toEquiv]

include hw in
theorem nonempty_griessHopfMultiplier_mulEquiv_of_card_le [Finite (PresentedCover R w)]
    {m : ℕ} (hcard : Nat.card (PresentedCover R w) ≤ m * Nat.card X) {E : Type*} [Group E]
    {e : ι → E} (he : ∀ r ∈ coverRelators R w, FreeGroup.lift e r = 1) {K₀ : Subgroup E}
    (hK₀ : Nat.card K₀ = m)
    (hK : K₀ ≤ (coverMap hP hwg).ker.map (PresentedGroup.toGroup he)) :
    Nonempty (griessHopfMultiplier X ≃* K₀) := by
  have hX : Finite X := Finite.of_surjective _ (coverMap_surjective hP hwg)
  have hcardK : Nat.card (coverMap hP hwg).ker ≤ m := by
    have h1 := card_presentedCover hP hw hwg
    rw [Nat.card_congr (griessHopfMultiplierEquivKer hP hw hwg).toEquiv, mul_comm] at h1
    exact Nat.le_of_mul_le_mul_right (h1 ▸ hcard) Nat.card_pos
  have hs := (PresentedGroup.toGroup he).subgroupMap_surjective (coverMap hP hwg).ker
  have hfin : Finite ((coverMap hP hwg).ker.map (PresentedGroup.toGroup he)) :=
    Finite.of_surjective _ hs
  have hmap : Nat.card ((coverMap hP hwg).ker.map (PresentedGroup.toGroup he)) ≤
      Nat.card (coverMap hP hwg).ker := Nat.card_le_card_of_surjective _ hs
  have heq : K₀ = (coverMap hP hwg).ker.map (PresentedGroup.toGroup he) :=
    eq_of_le_of_card_ge hK (by omega)
  have hle : Nat.card (coverMap hP hwg).ker ≤
      Nat.card ((coverMap hP hwg).ker.map (PresentedGroup.toGroup he)) := by
    rw [← heq]
    omega
  have hbij := hs.bijective_of_nat_card_le hle
  exact ⟨(griessHopfMultiplierEquivKer hP hw hwg).trans <|
    (MulEquiv.ofBijective _ hbij).trans (MulEquiv.subgroupCongr heq.symm)⟩

theorem closure_lift_le_map_ker {E : Type*} [Group E] {e : ι → E}
    (he : ∀ r ∈ coverRelators R w, FreeGroup.lift e r = 1) {T : Set (FreeGroup ι)}
    (hT : ∀ t ∈ T, FreeGroup.lift g t = 1) :
    closure (FreeGroup.lift e '' T) ≤ (coverMap hP hwg).ker.map (PresentedGroup.toGroup he) := by
  rw [closure_le]
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨PresentedGroup.mk _ t, hT t ht, rfl⟩

include hP hw hwg in
theorem nonempty_griessHopfMultiplier_mulEquiv_closure [Finite (PresentedCover R w)]
    {m : ℕ} (hcard : Nat.card (PresentedCover R w) ≤ m * Nat.card X) {E : Type*} [Group E]
    {e : ι → E} (he : ∀ r ∈ coverRelators R w, FreeGroup.lift e r = 1) {T : Set (FreeGroup ι)}
    (hT : ∀ t ∈ T, FreeGroup.lift g t = 1) {K₀ : Subgroup E} (hK₀ : Nat.card K₀ = m)
    (hK : K₀ ≤ closure (FreeGroup.lift e '' T)) :
    Nonempty (griessHopfMultiplier X ≃* K₀) :=
  nonempty_griessHopfMultiplier_mulEquiv_of_card_le hP hw hwg hcard he hK₀
    (hK.trans (closure_lift_le_map_ker hP hwg he hT))

end Cover

end CFSG.LieType.Multipliers
