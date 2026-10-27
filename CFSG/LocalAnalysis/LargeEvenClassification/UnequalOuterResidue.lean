module

public import CFSG.LocalAnalysis.LargeEvenClassification.FullActionGeneratorBound
public meta import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoBinaryEndResidue
public meta import CFSG.LocalAnalysis.LargeEvenClassification.ResidualRing

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def unequalResidueTrace : RankTwoBinaryResidue 0 →ₗ[ZMod 2] ZMod 2 :=
  let : CommRing (ZMod 2) := ZMod.commRing 2
  { toFun := fun x => x.1.1 + x.2.2
    map_add' := by intro x y; change (x.1.1 + y.1.1) + (x.2.2 + y.2.2) = _; abel
    map_smul' := by
      intro a x
      have ha : a = 0 ∨ a = 1 := by
        have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
        exact h a
      rcases ha with rfl | rfl
      · change ((0 : ZMod 2) • x).1.1 + ((0 : ZMod 2) • x).2.2 =
          (0 : ZMod 2) • (x.1.1 + x.2.2)
        rw [zero_smul]
        change (0 : ZMod 2) = (0 : ZMod 2) • (x.1.1 + x.2.2)
        exact (zero_smul (ZMod 2) _).symm
      · change ((1 : ZMod 2) • x).1.1 + ((1 : ZMod 2) • x).2.2 =
          (1 : ZMod 2) • (x.1.1 + x.2.2)
        rw [one_smul]
        exact (one_smul (ZMod 2) _).symm }

@[expose] def unequalResidueOff : RankTwoBinaryResidue 0 →ₗ[ZMod 2] RankTwoBinaryResidue 0 :=
  AddMonoidHom.toZModLinearMap 2 {
    toFun := fun x => ((0, x.1.2), (x.2.1, 0))
    map_zero' := rfl
    map_add' := by
      intro x y
      change ((0, x.1.2 + y.1.2), (x.2.1 + y.2.1, 0)) =
        rankTwoBinaryResidueAdd ((0, x.1.2), (x.2.1, 0)) ((0, y.1.2), (y.2.1, 0))
      simp [rankTwoBinaryResidueAdd] }

theorem unequalResidue_square_trace_zero :
    ∀ x : RankTwoBinaryResidue 0, unequalResidueTrace x = 0 → x + x * x = unequalResidueOff x := by
  decide

theorem unequalResidue_outer_difference_trace_one :
    ∀ (j : (RankTwoBinaryResidue 0)ˣ) (x : RankTwoBinaryResidue 0),
      unequalResidueTrace x = 1 → binaryResidueConjugationDifference j x = j.val - 1 := by
  decide

theorem unequalResidue_scalar_kernel_card :
    Fintype.card {x : RankTwoBinaryResidue 0 // unequalResidueTrace x = 0 ∧ unequalResidueOff x = 0} = 2 := by
  decide

theorem unequalResidue_trace_zero_square_bound
    (W : Submodule (ZMod 2) (RankTwoBinaryResidue 0))
    (htrace : ∀ x ∈ W, unequalResidueTrace x = 0) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) + 1 := by
  let off := unequalResidueOff.domRestrict W
  have hdimension := off.finrank_range_add_finrank_ker
  have hrange : off.range ≤ residueSquareCommutatorSpan W := by
    intro x hx
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hx
    change unequalResidueOff w.val ∈ residueSquareCommutatorSpan W
    rw [← unequalResidue_square_trace_zero w.val (htrace _ w.property)]
    exact residue_square_mem_span W w.property
  have hrank := Submodule.finrank_mono hrange
  let toScalar : off.ker → {x : RankTwoBinaryResidue 0 // unequalResidueTrace x = 0 ∧ unequalResidueOff x = 0} :=
    fun x => ⟨x.val.val, htrace _ x.val.property, x.property⟩
  have hinjective : Function.Injective toScalar := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.val) h
  have hcard := Nat.card_le_card_of_injective toScalar hinjective
  rw [Nat.card_eq_fintype_card (α :=
    {x : RankTwoBinaryResidue 0 // unequalResidueTrace x = 0 ∧ unequalResidueOff x = 0}),
    unequalResidue_scalar_kernel_card, ← FiniteField.pow_finrank_eq_natCard 2 off.ker] at hcard
  have hker : Module.finrank (ZMod 2) off.ker ≤ 1 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  omega

set_option maxRecDepth 10000 in
theorem unequalResidualRing_outer_relations_nonzero :
    ∀ (twist : ZMod 4) (u v : ResidualRing twist),
      (twist = 0 ∨ twist = 2) →
      (u.1.1.val % 2 = 1 ∧ u.1.2.val % 2 = 1 ∧ u.2.1.val % 2 = 0 ∧ u.2.2.val % 2 = 1) →
      (v.1.1.val % 2 = 1 ∧ v.1.2.val % 2 = 0 ∧ v.2.1.val % 2 = 1 ∧ v.2.2.val % 2 = 1) →
      u ^ 2 ≠ 1 ∨ v ^ 2 ≠ 1 ∨ u * v ≠ v * u := by
  decide +kernel

@[expose] def unequalResidueUnitOffHom : (RankTwoBinaryResidue 0)ˣ →* Multiplicative (ZMod 2 × ZMod 2) where
  toFun j := Multiplicative.ofAdd (j.val.1.2, j.val.2.1)
  map_one' := rfl
  map_mul' := by
    have h : ∀ j k : (RankTwoBinaryResidue 0)ˣ,
        (((j * k).val.1.2, (j * k).val.2.1) : ZMod 2 × ZMod 2) =
          (j.val.1.2, j.val.2.1) + (k.val.1.2, k.val.2.1) := by decide
    intro j k
    exact congrArg Multiplicative.ofAdd (h j k)

theorem unequalResidueUnitOffHom_bijective : Function.Bijective unequalResidueUnitOffHom := by
  constructor
  · have h : ∀ j k : (RankTwoBinaryResidue 0)ˣ,
        (j.val.1.2, j.val.2.1) = (k.val.1.2, k.val.2.1) → j = k := by decide
    intro j k hjk
    exact h j k (congrArg Multiplicative.toAdd hjk)
  · have h : ∀ z : ZMod 2 × ZMod 2, ∃ j : (RankTwoBinaryResidue 0)ˣ,
        (j.val.1.2, j.val.2.1) = z := by decide
    intro z
    obtain ⟨j, hj⟩ := h z.toAdd
    exact ⟨j, congrArg Multiplicative.ofAdd hj⟩

@[expose] noncomputable def unequalResidueUnitOffEquiv :
    (RankTwoBinaryResidue 0)ˣ ≃* Multiplicative (ZMod 2 × ZMod 2) :=
  MulEquiv.ofBijective unequalResidueUnitOffHom unequalResidueUnitOffHom_bijective

theorem unequalResidue_unit_off_recover :
    ∀ j : (RankTwoBinaryResidue 0)ˣ,
      (j.val : RankTwoBinaryResidue 0) - (1 : RankTwoBinaryResidue 0) =
        (((0, j.val.1.2), (j.val.2.1, 0)) : RankTwoBinaryResidue 0) := by
  have h : ∀ j : (RankTwoBinaryResidue 0)ˣ, j.val.1.1 = 1 ∧ j.val.2.2 = 1 := by decide
  intro j
  have hone : -(1 : ZMod 2) = 1 := by decide
  have hzero : -(0 : ZMod 2) = 0 := by decide
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  change rankTwoBinaryResidueAdd j.val ((-(1 : ZMod 2), -(0 : ZMod 2)),
    (-(0 : ZMod 2), -(1 : ZMod 2))) = _
  apply Prod.ext <;> apply Prod.ext <;>
    simp [rankTwoBinaryResidueAdd, (h j).1, (h j).2, hone, hzero, htwo]

@[expose] def unequalResidueUnitDifferenceHom :
    (RankTwoBinaryResidue 0)ˣ →* Multiplicative (RankTwoBinaryResidue 0) where
  toFun j := Multiplicative.ofAdd ((0, j.val.1.2), (j.val.2.1, 0))
  map_one' := rfl
  map_mul' := by
    have h : ∀ j k : (RankTwoBinaryResidue 0)ˣ,
        (((0, (j * k).val.1.2), ((j * k).val.2.1, 0)) : RankTwoBinaryResidue 0) =
          (((0, j.val.1.2), (j.val.2.1, 0)) : RankTwoBinaryResidue 0) +
            (((0, k.val.1.2), (k.val.2.1, 0)) : RankTwoBinaryResidue 0) := by decide
    intro j k
    exact congrArg Multiplicative.ofAdd (h j k)

theorem unequalResidueUnitDifferenceHom_injective : Function.Injective unequalResidueUnitDifferenceHom := by
  intro j k h
  have hi : ∀ j k : (RankTwoBinaryResidue 0)ˣ,
      (j.val.1.2, j.val.2.1) = (k.val.1.2, k.val.2.1) → j = k := by decide
  have ha := congrArg Multiplicative.toAdd h
  change (((0, j.val.1.2), (j.val.2.1, 0)) : RankTwoBinaryResidue 0) =
    (((0, k.val.1.2), (k.val.2.1, 0)) : RankTwoBinaryResidue 0) at ha
  have hf := congrArg (fun x : RankTwoBinaryResidue 0 => x.1.2) ha
  have hs := congrArg (fun x : RankTwoBinaryResidue 0 => x.2.1) ha
  apply hi j k
  exact Prod.ext hf hs

@[expose] def unequalResidueOuterHom {R : Type*} [Ring R]
    (residue : R →+* RankTwoBinaryResidue 0) (Action : Subgroup Rˣ) :
    Action →* Multiplicative (RankTwoBinaryResidue 0) :=
  unequalResidueUnitDifferenceHom.comp ((Units.map residue.toMonoidHom).comp Action.subtype)

@[expose] def residualBinaryCoordinates {twist : ZMod 4} (x : ResidualRing twist) :
    RankTwoBinaryResidue 0 :=
  let f := ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)
  ((f x.1.1, f x.1.2), (f x.2.1, f x.2.2))

theorem residualBinaryCoordinates_parity {twist : ZMod 4} (x : ResidualRing twist) :
    residualBinaryCoordinates x =
      ((((x.1.1.val % 2 : ℕ) : ZMod 2), ((x.1.2.val % 2 : ℕ) : ZMod 2)),
        (((x.2.1.val % 2 : ℕ) : ZMod 2), ((x.2.2.val % 2 : ℕ) : ZMod 2))) := by
  have h : ∀ x : ZMod 4,
      ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) x = (x.val % 2 : ℕ) := by decide
  apply Prod.ext <;> apply Prod.ext <;> exact h _

theorem residualBinaryCoordinates_outer_relations_nonzero (twist : ZMod 4) (u v : ResidualRing twist)
    (htwist : twist = 0 ∨ twist = 2)
    (hu : residualBinaryCoordinates u = (((1, 1), (0, 1)) : RankTwoBinaryResidue 0))
    (hv : residualBinaryCoordinates v = (((1, 0), (1, 1)) : RankTwoBinaryResidue 0)) :
    u ^ 2 ≠ 1 ∨ v ^ 2 ≠ 1 ∨ u * v ≠ v * u := by
  have h : ∀ x : ZMod 4,
      (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) x = 0 ↔ x.val % 2 = 0) ∧
        (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) x = 1 ↔ x.val % 2 = 1) := by decide
  have huf := congrArg (fun z : RankTwoBinaryResidue 0 => z.1.1) hu
  have hub := congrArg (fun z : RankTwoBinaryResidue 0 => z.1.2) hu
  have huc := congrArg (fun z : RankTwoBinaryResidue 0 => z.2.1) hu
  have hud := congrArg (fun z : RankTwoBinaryResidue 0 => z.2.2) hu
  have hvf := congrArg (fun z : RankTwoBinaryResidue 0 => z.1.1) hv
  have hvb := congrArg (fun z : RankTwoBinaryResidue 0 => z.1.2) hv
  have hvc := congrArg (fun z : RankTwoBinaryResidue 0 => z.2.1) hv
  have hvd := congrArg (fun z : RankTwoBinaryResidue 0 => z.2.2) hv
  exact unequalResidualRing_outer_relations_nonzero twist u v htwist
    ⟨(h _).2.mp huf, (h _).2.mp hub, (h _).1.mp huc, (h _).2.mp hud⟩
    ⟨(h _).2.mp hvf, (h _).1.mp hvb, (h _).2.mp hvc, (h _).2.mp hvd⟩

section OuterSaving

variable {R : Type*} [Ring R]
variable (residue : R →+* RankTwoBinaryResidue 0)
variable (hkernel : ∀ r : R, residue r = 0 ↔ ∃ s : R, r = 2 • s)
variable (hcancelTwo : ∀ r : R, 2 • r = 0 → residue r = 0)
variable (Action : Subgroup Rˣ) [Finite Action]

include hkernel in
omit [Finite Action] in
theorem unequalResidueOuterHom_ker :
    (unequalResidueOuterHom residue Action).ker = fullActionEven Action := by
  ext u
  change unequalResidueUnitDifferenceHom (Units.map residue.toMonoidHom u.val) = 1 ↔ _
  rw [show (1 : Multiplicative (RankTwoBinaryResidue 0)) = unequalResidueUnitDifferenceHom 1 from rfl,
    unequalResidueUnitDifferenceHom_injective.eq_iff]
  exact residue_units_kernel residue hkernel u.val

omit [Finite Action] in
theorem unequalResidueOuter_finrank_le_two :
    Module.finrank (ZMod 2) (binaryHomRange (unequalResidueOuterHom residue Action)) ≤ 2 := by
  let Off := {x : RankTwoBinaryResidue 0 // x.1.1 = 0 ∧ x.2.2 = 0}
  let toOff : binaryHomRange (unequalResidueOuterHom residue Action) → Off := fun x =>
    ⟨x.val, by
      obtain ⟨u, hu⟩ := (binaryHomRange_mem _ _).mp x.property
      have h := congrArg Multiplicative.toAdd hu
      change ((0, _), (_, 0)) = x.val at h
      rw [← h]
      exact ⟨rfl, rfl⟩⟩
  have hinj : Function.Injective toOff := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Off => z.val) h)
  have hc := Nat.card_le_card_of_injective toOff hinj
  have hoff : Nat.card Off = 4 := by rw [Nat.card_eq_fintype_card]; decide
  rw [hoff, ← FiniteField.pow_finrank_eq_natCard 2 (binaryHomRange (unequalResidueOuterHom residue Action))] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

omit [Finite Action] in
theorem unequalResidueOuter_full_image
    (hfull : Module.finrank (ZMod 2) (binaryHomRange (unequalResidueOuterHom residue Action)) = 2)
    (b c : ZMod 2) :
    ∃ u : Action, (unequalResidueOuterHom residue Action u).toAdd =
      (((0, b), (c, 0)) : RankTwoBinaryResidue 0) := by
  classical
  let L := binaryHomRange (unequalResidueOuterHom residue Action)
  let Off := {x : RankTwoBinaryResidue 0 // x.1.1 = 0 ∧ x.2.2 = 0}
  let f : L → Off := fun x => ⟨x.val, by
    obtain ⟨u, hu⟩ := (binaryHomRange_mem _ _).mp x.property
    have h := congrArg Multiplicative.toAdd hu
    change ((0, _), (_, 0)) = x.val at h
    rw [← h]
    exact ⟨rfl, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Off => z.val) h)
  have hcard : Nat.card L = Nat.card Off := by
    rw [← FiniteField.pow_finrank_eq_natCard 2 L]
    change 2 ^ Module.finrank (ZMod 2) (binaryHomRange (unequalResidueOuterHom residue Action)) = _
    rw [hfull, Nat.card_eq_fintype_card (α := Off)]
    decide
  let : Fintype L := Fintype.ofFinite L
  have hsurj := ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using hcard⟩).surjective
  obtain ⟨x, hx⟩ := hsurj ⟨((0, b), (c, 0)), rfl, rfl⟩
  obtain ⟨u, hu⟩ := (binaryHomRange_mem _ _).mp x.property
  refine ⟨u, ?_⟩
  exact (congrArg Multiplicative.toAdd hu).trans (congrArg (fun z : Off => z.val) hx)

include hkernel hcancelTwo in
theorem unequalResidue_trace_one_outer_saving (hpgroup : IsPGroup 2 Action)
    (x : RankTwoBinaryResidue 0)
    (hx : x ∈ binaryHomRange (fullActionEvenLeadingHom residue hkernel hcancelTwo Action))
    (htrace : unequalResidueTrace x = 1) :
    binaryHomRange (unequalResidueOuterHom residue Action) ≤
      binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action) := by
  intro z hz
  obtain ⟨u, hu⟩ := (binaryHomRange_mem _ _).mp hz
  let j := Units.map residue.toMonoidHom u.val
  have hd := fullAction_outer_difference_le_killed residue hkernel hcancelTwo Action hpgroup u
  have hmem : binaryResidueConjugationDifference j x ∈
      binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action) :=
    hd (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
  rw [unequalResidue_outer_difference_trace_one j x htrace, unequalResidue_unit_off_recover j] at hmem
  have heq := congrArg Multiplicative.toAdd hu
  change (((0, j.val.1.2), (j.val.2.1, 0)) : RankTwoBinaryResidue 0) = z at heq
  exact heq ▸ hmem

include hkernel hcancelTwo in
omit [Finite Action] in
theorem fullActionEvenLeadingHom_eq_one_iff (u : fullActionEven Action) :
    fullActionEvenLeadingHom residue hkernel hcancelTwo Action u = 1 ↔
      u.val.val ∈ principalFourSubgroup R := by
  change principalLeadingResidueHom residue hkernel 2 (by decide) hcancelTwo
    ⟨u.val.val, u.property⟩ = 1 ↔ _
  rw [principalLeadingResidueHom_kernel residue hkernel 2 (by decide) hcancelTwo,
    principalCongruenceSubgroup_four]

variable {twist : ZMod 4}
variable (fourResidue : R →+* ResidualRing twist)
variable (hfactor : ∀ r : R, residualBinaryCoordinates (fourResidue r) = residue r)
variable (hfourKernel : ∀ u : Rˣ, fourResidue u.val = 1 ↔ u ∈ principalFourSubgroup R)

include hkernel hcancelTwo hfactor hfourKernel in
theorem unequalResidue_full_outer_killed_nonzero (hpgroup : IsPGroup 2 Action)
    (htwist : twist = 0 ∨ twist = 2)
    (hfull : Module.finrank (ZMod 2) (binaryHomRange (unequalResidueOuterHom residue Action)) = 2) :
    binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action) ≠ ⊥ := by
  intro hzero
  obtain ⟨u, hu⟩ := unequalResidueOuter_full_image residue Action hfull 1 0
  obtain ⟨v, hv⟩ := unequalResidueOuter_full_image residue Action hfull 0 1
  have hrecover (g : Action) : residue g.val.val =
      1 + (unequalResidueOuterHom residue Action g).toAdd := by
    let j := Units.map residue.toMonoidHom g.val
    have h := unequalResidue_unit_off_recover j
    change residue g.val.val - 1 = (unequalResidueOuterHom residue Action g).toAdd at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  have hunitU : residualBinaryCoordinates (fourResidue u.val.val) =
      (((1, 1), (0, 1)) : RankTwoBinaryResidue 0) := by
    rw [hfactor, hrecover, hu]
    rfl
  have hunitV : residualBinaryCoordinates (fourResidue v.val.val) =
      (((1, 0), (1, 1)) : RankTwoBinaryResidue 0) := by
    rw [hfactor, hrecover, hv]
    rfl
  have hfrattini : frattini Action ≤ fullActionEven Action := by
    rw [← unequalResidueOuterHom_ker residue hkernel Action]
    exact binaryHom_frattini_le_ker _
  have hrelations (g : Action) (hg : g ∈ frattini Action) : fourResidue g.val.val = 1 := by
    let killed : fullActionKilledEven Action := ⟨⟨g, hfrattini hg⟩, hg⟩
    have hm : (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action killed).toAdd ∈
        binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action) :=
      (binaryHomRange_mem _ _).mpr ⟨killed, rfl⟩
    rw [hzero] at hm
    have hleading : fullActionEvenLeadingHom residue hkernel hcancelTwo Action ⟨g, hfrattini hg⟩ = 1 :=
      Multiplicative.toAdd.injective (show _ = 0 from hm)
    exact (hfourKernel g.val).mpr
      ((fullActionEvenLeadingHom_eq_one_iff residue hkernel hcancelTwo Action _).mp hleading)
  have hsquareU : fourResidue u.val.val ^ 2 = 1 := by
    have h := hrelations (u ^ 2) (pGroup_pow_mem_frattini Nat.prime_two hpgroup u)
    change fourResidue (u.val.val ^ 2) = 1 at h
    rwa [map_pow] at h
  have hsquareV : fourResidue v.val.val ^ 2 = 1 := by
    have h := hrelations (v ^ 2) (pGroup_pow_mem_frattini Nat.prime_two hpgroup v)
    change fourResidue (v.val.val ^ 2) = 1 at h
    rwa [map_pow] at h
  have hcommute : fourResidue u.val.val * fourResidue v.val.val =
      fourResidue v.val.val * fourResidue u.val.val := by
    let f : Action →* (ResidualRing twist)ˣ := (Units.map fourResidue.toMonoidHom).comp Action.subtype
    have hc : f (u * v * u⁻¹ * v⁻¹) = 1 := Units.ext
      (hrelations _ (pGroup_commutator_mem_frattini Nat.prime_two hpgroup u v))
    have hc' : f u * f v * (f u)⁻¹ * (f v)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using hc
    have hcomm : Commute (f u) (f v) := by
      exact commutatorElement_eq_one_iff_commute.mp hc'
    exact congrArg Units.val hcomm.eq
  rcases residualBinaryCoordinates_outer_relations_nonzero twist _ _ htwist hunitU hunitV with h | h | h
  · exact h hsquareU
  · exact h hsquareV
  · exact h hcommute

variable (hcancelFour : ∀ r : R, 4 • r = 0 → residue r = 0)

include hkernel hcancelTwo hfactor hfourKernel hcancelFour in
theorem unequal_fullAction_generator_rank_bound (hpgroup : IsPGroup 2 Action)
    (htwist : twist = 0 ∨ twist = 2) :
    pGeneratorRank 2 Action ≤ pGeneratorRank 2 (evenActionDeep Action) + 2 := by
  let W := binaryHomRange (fullActionEvenLeadingHom residue hkernel hcancelTwo Action)
  let D := binaryHomRange (fullActionKilledEvenResidueHom residue hkernel hcancelTwo Action)
  let L := binaryHomRange (unequalResidueOuterHom residue Action)
  have houter := binaryHom_quotient_generator_rank hpgroup (fullActionEven Action)
    (unequalResidueOuterHom residue Action) (unequalResidueOuterHom_ker residue hkernel Action)
  change pGeneratorRank 2 (Action ⧸ fullActionEven Action) = Module.finrank (ZMod 2) L at houter
  have hsaving := fullAction_generator_rank_double_saving residue hkernel hcancelTwo Action hcancelFour
    hpgroup D le_rfl
  change pGeneratorRank 2 Action + Module.finrank (ZMod 2) (residueSquareCommutatorSpan W) +
      Module.finrank (ZMod 2) D ≤ pGeneratorRank 2 (Action ⧸ fullActionEven Action) +
      Module.finrank (ZMod 2) W + pGeneratorRank 2 (evenActionDeep Action) at hsaving
  rw [houter] at hsaving
  have hsmall := unequalResidueOuter_finrank_le_two residue Action
  change Module.finrank (ZMod 2) L ≤ 2 at hsmall
  by_cases htrace : ∀ x ∈ W, unequalResidueTrace x = 0
  · have hinner := unequalResidue_trace_zero_square_bound W htrace
    by_cases hthin : Module.finrank (ZMod 2) L ≤ 1
    · omega
    · have hfull : Module.finrank (ZMod 2) L = 2 := by omega
      have hnonzero := unequalResidue_full_outer_killed_nonzero residue hkernel hcancelTwo Action
        fourResidue hfactor hfourKernel hpgroup htwist hfull
      have hpositive : 1 ≤ Module.finrank (ZMod 2) D := by
        by_contra hz
        have hrank : Module.finrank (ZMod 2) D = 0 := by omega
        exact hnonzero (Submodule.finrank_eq_zero.mp hrank)
      omega
  · push Not at htrace
    obtain ⟨x, hx, htrace⟩ := htrace
    have hone : unequalResidueTrace x = 1 := by
      have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      exact (hbinary _).resolve_left htrace
    have hD := unequalResidue_trace_one_outer_saving residue hkernel hcancelTwo Action hpgroup x hx hone
    have hrank := Submodule.finrank_mono hD
    change Module.finrank (ZMod 2) L ≤ Module.finrank (ZMod 2) D at hrank
    have hinner := rankTwoBinaryResidue_square_commutator_bound 0 W
    omega

include hkernel hcancelTwo hfactor hfourKernel hcancelFour in
theorem unequal_fullAction_generator_rank_involution_bound (hpgroup : IsPGroup 2 Action)
    (htwist : twist = 0 ∨ twist = 2)
    {exponent : ℕ} (hcharacteristic : (2 : R) ^ exponent = 0) :
    pGeneratorRank 2 Action ≤
      Nat.log 2 (Nat.card (principalInvolutionSubgroup hcharacteristic
        (Action ⊓ principalFourSubgroup R) (fun u => u.property.2))) + 2 :=
  (unequal_fullAction_generator_rank_bound residue hkernel hcancelTwo Action fourResidue hfactor
    hfourKernel hcancelFour hpgroup htwist).trans
      (Nat.add_le_add_right (deepAction_generator_rank_involution_bound Action hpgroup hcharacteristic) 2)

end OuterSaving

end CFSG.LargeEvenClassification.Helpers
