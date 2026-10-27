module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourCover
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupCertificate

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def c8FourActionCentral (H : Subgroup C8FourCode) (g : C8FourCode) : Prop :=
  g ∈ H ∧ ∀ h ∈ H, g * h = h * g

@[expose] def c8FourActionInvolution (g : C8FourCode) : Prop :=
  g ≠ 1 ∧ g ^ 2 = 1

@[expose] def c8FourActionFixedNorm (g : C8FourCode) : Prop :=
  ∀ x : CyclicPair 2 4, c8FourApply g x = x →
    ∃ y : CyclicPair 2 4, c8FourApply g y + y = x

@[expose] def c8FourActionNormImage (g : C8FourCode) : Prop :=
  ∀ x : CyclicPair 2 4, (∃ y : CyclicPair 2 4, c8FourApply g y + y = x) ↔
    ∃ y : CyclicPair 2 4, 2 • y = x

@[expose] def c8FourActionAdmissible (H : Subgroup C8FourCode) : Prop :=
  (∀ g : C8FourCode, c8FourActionCentral H g → c8FourActionInvolution g →
    c8FourNormKernel g → ¬c8FourActionFixedNorm g) ∧
  ¬(c8FourDelta ∈ H ∧ c8FourActionCentral H c8FourNu) ∧
  (c8FourDelta ∈ H → c8FourCompatible H)

@[expose] def c8FourActionPrimitive (H Q : Subgroup C8FourCode) (g : C8FourCode) : Prop :=
  g ∈ Q ∧ c8FourActionCentral H g ∧ c8FourActionInvolution g ∧
    c8FourNormKernel g ∧ c8FourActionNormImage g

instance c8FourActionInvolution_decidable (g : C8FourCode) :
    Decidable (c8FourActionInvolution g) := inferInstanceAs (Decidable (g ≠ 1 ∧ g ^ 2 = 1))

instance c8FourActionFixedNorm_decidable (g : C8FourCode) :
    Decidable (c8FourActionFixedNorm g) := Fintype.decidableForallFintype

instance c8FourActionNormImage_decidable (g : C8FourCode) :
    Decidable (c8FourActionNormImage g) := Fintype.decidableForallFintype

theorem c8FourActionNormImage_doubles {g : C8FourCode} (hg : c8FourActionNormImage g) :
    c8FourNormDoubles g := by
  intro x
  exact (hg (2 • x)).mpr ⟨x, rfl⟩

theorem c8FourActionCentral_center (H : Subgroup C8FourCode) (g : H) :
    c8FourActionCentral H g.val ↔ g ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hg h
    exact Subtype.ext (hg.2 h.val h.property).symm
  · intro hg
    refine ⟨g.property, ?_⟩
    intro h hh
    exact (congrArg Subtype.val (hg ⟨h, hh⟩)).symm

theorem c8FourActionCentral_mono {H M Q : Subgroup C8FourCode} {g : C8FourCode}
    (hHM : H ≤ M) (hQH : Q ≤ H) (hgQ : g ∈ Q) (hgM : c8FourActionCentral M g) :
    c8FourActionCentral H g :=
  ⟨hQH hgQ, fun h hh => hgM.2 h (hHM hh)⟩

@[expose] def c8FourActionFixed (g : C8FourCode) : AddSubgroup (CyclicPair 2 4) where
  carrier := {x | c8FourApply g x = x}
  zero_mem' := by
    change c8FourApply g 0 = 0
    rw [← c8FourNativeUnit_apply, map_zero]
  add_mem' := by
    intro x y hx hy
    change c8FourApply g x = x at hx
    change c8FourApply g y = y at hy
    change c8FourApply g (x + y) = x + y
    rw [← c8FourNativeUnit_apply, map_add, c8FourNativeUnit_apply,
      c8FourNativeUnit_apply, hx, hy]
  neg_mem' := by
    intro x hx
    change c8FourApply g x = x at hx
    change c8FourApply g (-x) = -x
    rw [← c8FourNativeUnit_apply, map_neg, c8FourNativeUnit_apply, hx]

@[expose] def c8FourActionFixedParity (g : C8FourCode) : AddSubgroup (ZMod 2 × ZMod 2) :=
  (c8FourActionFixed g).map c8FourBinaryCoordinates

theorem c8FourActionFixedParity_mem (g : C8FourCode) (p : ZMod 2 × ZMod 2) :
    p ∈ c8FourActionFixedParity g ↔
      ∃ x : CyclicPair 2 4, c8FourApply g x = x ∧ c8FourBinaryCoordinates x = p := by
  exact AddSubgroup.mem_map

@[expose] def c8FourActionFixedParityElements (g : C8FourCode) : Finset (ZMod 2 × ZMod 2) :=
  (Finset.univ.filter (fun x : CyclicPair 2 4 => c8FourApply g x = x)).image c8FourBinaryCoordinates

theorem c8FourActionFixedParityElements_mem (g : C8FourCode) (p : ZMod 2 × ZMod 2) :
    p ∈ c8FourActionFixedParityElements g ↔ p ∈ c8FourActionFixedParity g := by
  rw [c8FourActionFixedParity_mem]
  simp [c8FourActionFixedParityElements]

theorem c8FourActionFixedParity_card (g : C8FourCode) :
    Nat.card (c8FourActionFixedParity g) = (c8FourActionFixedParityElements g).card := by
  let e : c8FourActionFixedParity g ≃ (c8FourActionFixedParityElements g) :=
    { toFun := fun p => ⟨p.val, (c8FourActionFixedParityElements_mem g p.val).mpr p.property⟩
      invFun := fun p => ⟨p.val, (c8FourActionFixedParityElements_mem g p.val).mp p.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

@[expose] def c8FourActionDistinctFixedLines (g h : C8FourCode) : Prop :=
  Nat.card (c8FourActionFixedParity g) = 2 ∧
    Nat.card (c8FourActionFixedParity h) = 2 ∧
    c8FourActionFixedParity g ≠ c8FourActionFixedParity h

@[expose] def c8FourActionRecordCentral (r : C8FourSubgroupRecord) (g : C8FourCode) : Prop :=
  c8FourRecordMem r g ∧
    certificateListAll r.generators (fun h => g * h = h * g)

instance c8FourActionRecordCentral_decidable (r : C8FourSubgroupRecord) (g : C8FourCode) :
    Decidable (c8FourActionRecordCentral r g) := inferInstanceAs (Decidable (
      c8FourRecordMem r g ∧ certificateListAll r.generators (fun h => g * h = h * g)))

@[expose] def c8FourActionSubrecord (r s : C8FourSubgroupRecord) : Prop :=
  certificateListAll r.generators (c8FourRecordMem s)

instance c8FourActionSubrecord_decidable (r s : C8FourSubgroupRecord) :
    Decidable (c8FourActionSubrecord r s) :=
  inferInstanceAs (Decidable (certificateListAll r.generators (c8FourRecordMem s)))

theorem c8FourActionSubrecord_iff (r s : C8FourSubgroupRecord)
    (hr : c8FourRecordValid r) (hs : c8FourRecordValid s) :
    c8FourActionSubrecord r s ↔ c8FourRecordSubgroup r hr ≤ c8FourRecordSubgroup s hs := by
  rw [← c8FourRecord_generates r hr, Subgroup.closure_le]
  change certificateListAll r.generators (c8FourRecordMem s) ↔
    (r.generators.toFinset : Set C8FourCode) ⊆ {g | c8FourRecordMem s g}
  rw [certificateListAll_iff]
  constructor
  · intro h g hg
    exact h g (List.mem_toFinset.mp hg)
  · intro h g hg
    exact h (List.mem_toFinset.mpr hg)

theorem c8FourActionRecordCentral_iff (r : C8FourSubgroupRecord)
    (hr : c8FourRecordValid r) (g : C8FourCode) :
    c8FourActionRecordCentral r g ↔ c8FourActionCentral (c8FourRecordSubgroup r hr) g := by
  constructor
  · rintro ⟨hg, hcomm⟩
    refine ⟨hg, ?_⟩
    have hgenerators : (r.generators.toFinset : Set C8FourCode) ⊆
        Subgroup.centralizer ({g} : Set C8FourCode) := by
      intro h hh
      change h ∈ Subgroup.centralizer ({g} : Set C8FourCode)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzg : z = g := Set.mem_singleton_iff.mp hz
      subst z
      exact (certificateListAll_iff _ _).mp hcomm h (List.mem_toFinset.mp hh)
    have hle := (Subgroup.closure_le _).mpr hgenerators
    rw [c8FourRecord_generates r hr] at hle
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (hle hh)) g (Set.mem_singleton g)
  · rintro ⟨hg, hcomm⟩
    refine ⟨hg, (certificateListAll_iff _ _).mpr ?_⟩
    intro h hh
    exact hcomm h ((certificateListAll_iff _ _).mp hr.2.2.2.1 h hh)

end CFSG.LargeEvenClassification.Helpers
