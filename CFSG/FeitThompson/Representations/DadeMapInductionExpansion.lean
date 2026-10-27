module

public import CFSG.FeitThompson.Representations.InducedProjectedRestrictionOrbitConstant
public import CFSG.FeitThompson.Representations.SubsetTransporterSumCancellation
public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
public import CFSG.FeitThompson.Representations.DadeSupportPacketCount
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.DadeSupportPacketsLocalClasses
import CFSG.FeitThompson.Foundations.LiftHallByNormalComplement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MulAction Pointwise

section Finsum

variable {α β : Type*}

private theorem finsum_mem_const_eq (S : Set α) (hS : S.Finite) (c : ℂ) :
    ∑ᶠ _x ∈ S, c = (S.ncard : ℂ) * c := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_const, nsmul_eq_mul,
    Set.ncard_eq_toFinset_card _ hS]

private theorem mul_finsum_mem (S : Set α) (hS : S.Finite) (c : ℂ) (F : α → ℂ) :
    c * ∑ᶠ x ∈ S, F x = ∑ᶠ x ∈ S, c * F x := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    Finset.mul_sum]

private theorem finsum_mem_ratCast (S : Set α) (hS : S.Finite) (F : α → ℚ) :
    ((∑ᶠ x ∈ S, F x : ℚ) : ℂ) = ∑ᶠ x ∈ S, ((F x : ℚ) : ℂ) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finsum_mem_eq_finite_toFinset_sum _ hS,
    Rat.cast_sum]

open scoped Classical in
private theorem finsum_mem_eq_sum_ite [Fintype α] (S : Set α) (F : α → ℂ) :
    ∑ᶠ x ∈ S, F x = ∑ x : α, if x ∈ S then F x else 0 := by
  classical
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun x _ => Set.indicator_apply S F x

private theorem finsum_mem_comm_of_iff [Finite α] [Finite β] (S : Set α) (t : α → Set β)
    (T : Set β) (u : β → Set α) (F : α → β → ℂ)
    (h : ∀ (x : α) (y : β), (x ∈ S ∧ y ∈ t x) ↔ (y ∈ T ∧ x ∈ u y)) :
    ∑ᶠ x ∈ S, ∑ᶠ y ∈ t x, F x y = ∑ᶠ y ∈ T, ∑ᶠ x ∈ u y, F x y := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [finsum_mem_eq_sum_ite, finsum_mem_eq_sum_ite]
  have h1 : ∀ x : α, (if x ∈ S then ∑ᶠ y ∈ t x, F x y else 0)
      = ∑ y : β, if x ∈ S ∧ y ∈ t x then F x y else 0 := by
    intro x
    by_cases hx : x ∈ S
    · rw [if_pos hx, finsum_mem_eq_sum_ite]
      exact Finset.sum_congr rfl fun y _ => by simp [hx]
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun y _ => by simp [hx]).symm
  have h2 : ∀ y : β, (if y ∈ T then ∑ᶠ x ∈ u y, F x y else 0)
      = ∑ x : α, if y ∈ T ∧ x ∈ u y then F x y else 0 := by
    intro y
    by_cases hy : y ∈ T
    · rw [if_pos hy, finsum_mem_eq_sum_ite]
      exact Finset.sum_congr rfl fun x _ => by simp [hy]
    · rw [if_neg hy]
      exact (Finset.sum_eq_zero fun x _ => by simp [hy]).symm
  rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_congr rfl fun y _ => h2 y,
    Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun x _ => by simp only [h x y]

end Finsum

variable {G : Type*} [Group G] {L : Subgroup G} {A B C : Set G} {H : G → Subgroup G} {a b g l : G}

def dadeSubsetOrbit (L : Subgroup G) (B : Set G) : Set (Set G) :=
  {C : Set G | ∃ l ∈ L, (fun x => l⁻¹ * x * l) '' B = C}

theorem mem_dadeSubsetOrbit_iff :
    C ∈ dadeSubsetOrbit L B ↔ ∃ l ∈ L, (fun x => l⁻¹ * x * l) '' B = C := Iff.rfl

theorem self_mem_dadeSubsetOrbit (L : Subgroup G) (B : Set G) : B ∈ dadeSubsetOrbit L B :=
  ⟨1, one_mem L, by ext x; simp⟩

theorem dadeSubsetOrbit_symm (h : C ∈ dadeSubsetOrbit L B) : B ∈ dadeSubsetOrbit L C := by
  obtain ⟨l, hl, rfl⟩ := h
  refine ⟨l⁻¹, inv_mem hl, ?_⟩
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa [mul_assoc] using hz
  · intro hx
    exact ⟨l⁻¹ * x * l, ⟨x, hx, rfl⟩, by group⟩

theorem dadeSubsetOrbit_trans (h : C ∈ dadeSubsetOrbit L B) {D : Set G}
    (h' : D ∈ dadeSubsetOrbit L C) : D ∈ dadeSubsetOrbit L B := by
  obtain ⟨l, hl, rfl⟩ := h
  obtain ⟨m, hm, rfl⟩ := h'
  refine ⟨l * m, mul_mem hl hm, ?_⟩
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨l⁻¹ * y * l, ⟨y, hy, rfl⟩, by group⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by group⟩

theorem ncard_of_mem_dadeSubsetOrbit (h : C ∈ dadeSubsetOrbit L B) : C.ncard = B.ncard := by
  obtain ⟨l, -, rfl⟩ := h
  exact Set.ncard_image_of_injective _ fun x y hxy => by simpa using hxy

theorem nonempty_of_mem_dadeSubsetOrbit (hB : B.Nonempty) (h : C ∈ dadeSubsetOrbit L B) :
    C.Nonempty := by
  obtain ⟨l, -, rfl⟩ := h
  exact hB.image _

theorem conjAct_smul_set (c : G) (B : Set G) :
    ConjAct.toConjAct c • B = (MulAut.conj c) '' B := by
  ext y
  simp [Set.mem_smul_set, ConjAct.smul_def]

theorem orbit_toConjActSubgroup_set (L : Subgroup G) (B : Set G) :
    orbit (toConjActSubgroup L) B = dadeSubsetOrbit L B := by
  ext C
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    refine ⟨(ConjAct.ofConjAct s)⁻¹, inv_mem (mem_toConjActSubgroup_iff.1 hs), ?_⟩
    change _ = (⟨s, hs⟩ : toConjActSubgroup L) • B
    rw [Subgroup.smul_def]
    ext y
    simp [ConjAct.smul_def, Set.mem_smul_set]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨⟨ConjAct.toConjAct l⁻¹, toConjAct_mem_toConjActSubgroup (inv_mem hl)⟩, ?_⟩
    change (ConjAct.toConjAct l⁻¹) • B = _
    rw [conjAct_smul_set]
    ext y
    simp [MulAut.conj]

def stabilizerToConjActSubgroupSetEquiv (L : Subgroup G) (B : Set G) :
    stabilizer (toConjActSubgroup L) B ≃ dadeStab L B where
  toFun x := ⟨ConjAct.ofConjAct (x : ConjAct G), by
    rw [dadeStab_eq_inf]
    refine Subgroup.mem_inf.2 ⟨mem_toConjActSubgroup_iff.1 x.1.2, ?_⟩
    have h : (x : ConjAct G) • B = B := x.2
    rw [Subgroup.mem_normalizer_iff_conj_image_eq, ← conjAct_smul_set]
    simpa using h⟩
  invFun y := ⟨⟨ConjAct.toConjAct (y : G), toConjAct_mem_toConjActSubgroup (dadeStab_le_left y.2)⟩,
    by
      have h : (MulAut.conj (y : G)) '' B = B :=
        Subgroup.mem_normalizer_iff_conj_image_eq.1 (dadeStab_le_normalizer y.2)
      change ConjAct.toConjAct (y : G) • B = B
      rw [conjAct_smul_set]
      exact h⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

theorem ncard_dadeSubsetOrbit_mul_natCard_dadeStab (L : Subgroup G) (B : Set G) :
    (dadeSubsetOrbit L B).ncard * Nat.card (dadeStab L B) = Nat.card L := by
  rw [← orbit_toConjActSubgroup_set L B,
    ← Nat.card_congr (stabilizerToConjActSubgroupSetEquiv L B),
    ← MulAction.index_stabilizer, Subgroup.index_mul_card, natCard_toConjActSubgroup]

theorem natCard_dadeStab_conjInv_image [Finite G] (hl : l ∈ L) (B : Set G) :
    Nat.card (dadeStab L ((fun x => l⁻¹ * x * l) '' B)) = Nat.card (dadeStab L B) := by
  rw [dadeStab_conjInv_image hl, Subgroup.pointwise_smul_def]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (MulAut.conj (l⁻¹ : G)).injective).symm.toEquiv

def dadeNonemptySubsets (A : Set G) : Set (Set G) := {B : Set G | B.Nonempty ∧ B ⊆ A}

omit [Group G] in
theorem mem_dadeNonemptySubsets_iff : B ∈ dadeNonemptySubsets A ↔ B.Nonempty ∧ B ⊆ A := Iff.rfl

omit [Group G] in
@[simp]
theorem dadeNonemptySubsets_empty : dadeNonemptySubsets (∅ : Set G) = ∅ := by
  ext B
  simp only [mem_dadeNonemptySubsets_iff, Set.subset_empty_iff, Set.mem_empty_iff_false, iff_false,
    not_and]
  rintro hB rfl
  exact absurd rfl (Set.nonempty_iff_ne_empty.1 hB)

structure IsDadeSubsetTransversal (L : Subgroup G) (A : Set G) (T : Set (Set G)) : Prop where
  subset : T ⊆ dadeNonemptySubsets A
  existsUnique : ∀ B ∈ dadeNonemptySubsets A, ∃! C, C ∈ T ∧ B ∈ dadeSubsetOrbit L C

namespace IsDadeSubsetTransversal

variable {T : Set (Set G)}

theorem exists_mem (hT : IsDadeSubsetTransversal L A T) (hB : B ∈ dadeNonemptySubsets A) :
    ∃ C ∈ T, B ∈ dadeSubsetOrbit L C := by
  obtain ⟨C, hC, -⟩ := hT.existsUnique B hB
  exact ⟨C, hC.1, hC.2⟩

theorem unique (hT : IsDadeSubsetTransversal L A T) (hB : B ∈ dadeNonemptySubsets A) {C D : Set G}
    (hC : C ∈ T) (hCB : B ∈ dadeSubsetOrbit L C) (hD : D ∈ T)
    (hDB : B ∈ dadeSubsetOrbit L D) : C = D := by
  obtain ⟨E, -, hE⟩ := hT.existsUnique B hB
  rw [hE C ⟨hC, hCB⟩, hE D ⟨hD, hDB⟩]

theorem setOf_mem_and_mem_dadeSubsetOrbit (hT : IsDadeSubsetTransversal L A T)
    (hB : B ∈ dadeNonemptySubsets A) :
    ∃ C ∈ T, {C' : Set G | C' ∈ T ∧ B ∈ dadeSubsetOrbit L C'} = {C} := by
  obtain ⟨C, hC, hCuniq⟩ := hT.existsUnique B hB
  refine ⟨C, hC.1, Set.ext fun C' => ⟨fun h => hCuniq C' h, fun h => ?_⟩⟩
  rw [Set.mem_singleton_iff] at h
  rw [h]
  exact hC

theorem eq_empty_of_empty (hT : IsDadeSubsetTransversal L (∅ : Set G) T) : T = ∅ :=
  Set.subset_empty_iff.1 (by simpa using hT.subset)

end IsDadeSubsetTransversal

theorem IsDadeData.mem_dadeNonemptySubsets_of_mem_dadeSubsetOrbit [Finite G]
    (hD : IsDadeData L A H) (hB : B ∈ dadeNonemptySubsets A) (h : C ∈ dadeSubsetOrbit L B) :
    C ∈ dadeNonemptySubsets A := by
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨hB.1.image _, hD.conjInv_image_subset hB.2 hl⟩

theorem exists_isDadeSubsetTransversal [Finite G] (hD : IsDadeData L A H) :
    ∃ T : Set (Set G), IsDadeSubsetTransversal L A T := by
  classical
  let s : Setoid (Set G) :=
    { r := fun B C => C ∈ dadeSubsetOrbit L B
      iseqv :=
        { refl := fun B => self_mem_dadeSubsetOrbit L B
          symm := fun h => dadeSubsetOrbit_symm h
          trans := fun h h' => dadeSubsetOrbit_trans h h' } }
  have hrep : ∀ B : Set G, Quotient.out (Quotient.mk s B) ∈ dadeSubsetOrbit L B :=
    fun B => dadeSubsetOrbit_symm (Quotient.mk_out (s := s) B)
  refine ⟨{B : Set G | B ∈ dadeNonemptySubsets A ∧ B = Quotient.out (Quotient.mk s B)},
    fun B hB => hB.1, fun B hB => ?_⟩
  refine ⟨Quotient.out (Quotient.mk s B), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact hD.mem_dadeNonemptySubsets_of_mem_dadeSubsetOrbit hB (hrep B)
  · rw [Quotient.out_eq (Quotient.mk s B)]
  · exact dadeSubsetOrbit_symm (hrep B)
  · rintro C ⟨⟨-, hC⟩, hCB⟩
    rw [hC, Quotient.eq.2 (hCB : s.r C B)]

section Term

variable [Fintype G]

open Classical in
noncomputable def dadeExpansionTerm (hD : IsDadeData L A H) (f : L → ℂ) (B : Set G) (g : G) : ℂ :=
  if h : B.Nonempty ∧ B ⊆ A then
    (-1 : ℂ) ^ (B.ncard + 1) *
      indClassFun (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj h.2 h.1) f) g
  else 0

theorem dadeExpansionTerm_of_mem (hD : IsDadeData L A H) (f : L → ℂ) (hB : B.Nonempty)
    (hBA : B ⊆ A) (g : G) :
    dadeExpansionTerm hD f B g
      = (-1 : ℂ) ^ (B.ncard + 1) *
        indClassFun (dadeSubsetGroup H L B) (dadePullback (hD.dadeProj hBA hB) f) g := by
  classical
  rw [dadeExpansionTerm, dif_pos ⟨hB, hBA⟩]

theorem dadeExpansionTerm_of_notMem (hD : IsDadeData L A H) (f : L → ℂ)
    (h : B ∉ dadeNonemptySubsets A) (g : G) : dadeExpansionTerm hD f B g = 0 := by
  classical
  rw [dadeExpansionTerm, dif_neg (mem_dadeNonemptySubsets_iff.not.1 h)]

noncomputable def dadeExpansionWeightedTerm (hD : IsDadeData L A H) (f : L → ℂ) (B : Set G)
    (g : G) : ℂ :=
  (Nat.card (dadeStab L B) : ℂ) / (Nat.card L : ℂ) * dadeExpansionTerm hD f B g

theorem dadeExpansionWeightedTerm_of_notMem (hD : IsDadeData L A H) (f : L → ℂ)
    (h : B ∉ dadeNonemptySubsets A) (g : G) : dadeExpansionWeightedTerm hD f B g = 0 := by
  rw [dadeExpansionWeightedTerm, dadeExpansionTerm_of_notMem hD f h, mul_zero]

theorem dadeExpansionWeightedTerm_conjInv_image (hD : IsDadeData L A H) {f : L → ℂ}
    (hf : IsClassFun f) (hB : B.Nonempty) (hBA : B ⊆ A) (hl : l ∈ L) (g : G) :
    dadeExpansionWeightedTerm hD f ((fun x => l⁻¹ * x * l) '' B) g
      = dadeExpansionWeightedTerm hD f B g := by
  have hB' : ((fun x => l⁻¹ * x * l) '' B).Nonempty := hB.image _
  have hB'A : (fun x => l⁻¹ * x * l) '' B ⊆ A := hD.conjInv_image_subset hBA hl
  rw [dadeExpansionWeightedTerm, dadeExpansionWeightedTerm,
    dadeExpansionTerm_of_mem hD f hB' hB'A, dadeExpansionTerm_of_mem hD f hB hBA,
    natCard_dadeStab_conjInv_image hl B,
    hD.indClassFun_dadePullback_conjInv_image hBA hB hl hf,
    ncard_of_mem_dadeSubsetOrbit (L := L) (B := B) ⟨l, hl, rfl⟩]

theorem dadeExpansionWeightedTerm_of_mem_dadeSubsetOrbit (hD : IsDadeData L A H) {f : L → ℂ}
    (hf : IsClassFun f) (hB : B ∈ dadeNonemptySubsets A) (h : C ∈ dadeSubsetOrbit L B) (g : G) :
    dadeExpansionWeightedTerm hD f C g = dadeExpansionWeightedTerm hD f B g := by
  obtain ⟨l, hl, rfl⟩ := h
  exact dadeExpansionWeightedTerm_conjInv_image hD hf hB.1 hB.2 hl g

theorem finsum_dadeSubsetOrbit_dadeExpansionWeightedTerm (hD : IsDadeData L A H) {f : L → ℂ}
    (hf : IsClassFun f) (hB : B ∈ dadeNonemptySubsets A) (g : G) :
    ∑ᶠ C ∈ dadeSubsetOrbit L B, dadeExpansionWeightedTerm hD f C g
      = dadeExpansionTerm hD f B g := by
  have hcard : ((dadeSubsetOrbit L B).ncard : ℂ) * (Nat.card (dadeStab L B) : ℂ)
      = (Nat.card L : ℂ) := by
    rw [← Nat.cast_mul, ncard_dadeSubsetOrbit_mul_natCard_dadeStab]
  have hLne : (Nat.card L : ℂ) ≠ 0 := by
    simpa using (Nat.card_pos (α := L)).ne'
  rw [finsum_mem_congr (rfl : dadeSubsetOrbit L B = dadeSubsetOrbit L B)
      (fun C hC => dadeExpansionWeightedTerm_of_mem_dadeSubsetOrbit hD hf hB hC g),
    finsum_mem_const_eq _ (Set.toFinite _), dadeExpansionWeightedTerm]
  field_simp
  rw [hcard]

theorem finsum_dadeExpansionTerm_eq_finsum_dadeExpansionWeightedTerm (hD : IsDadeData L A H)
    {T : Set (Set G)} (hT : IsDadeSubsetTransversal L A T) {f : L → ℂ} (hf : IsClassFun f)
    (g : G) :
    ∑ᶠ B ∈ T, dadeExpansionTerm hD f B g
      = ∑ᶠ B ∈ dadeNonemptySubsets A, dadeExpansionWeightedTerm hD f B g := by
  have hstep : ∑ᶠ C ∈ T, ∑ᶠ B ∈ dadeSubsetOrbit L C, dadeExpansionWeightedTerm hD f B g
      = ∑ᶠ B ∈ dadeNonemptySubsets A,
          ∑ᶠ C ∈ {C : Set G | C ∈ T ∧ B ∈ dadeSubsetOrbit L C},
            dadeExpansionWeightedTerm hD f B g := by
    refine finsum_mem_comm_of_iff _ _ _ _ (fun _ B => dadeExpansionWeightedTerm hD f B g) ?_
    intro C B
    constructor
    · rintro ⟨hC, hCB⟩
      exact ⟨hD.mem_dadeNonemptySubsets_of_mem_dadeSubsetOrbit (hT.subset hC) hCB, hC, hCB⟩
    · rintro ⟨-, hC, hCB⟩
      exact ⟨hC, hCB⟩
  rw [finsum_mem_congr (rfl : T = T)
      (fun C hC => (finsum_dadeSubsetOrbit_dadeExpansionWeightedTerm hD hf (hT.subset hC) g).symm),
    hstep]
  refine finsum_mem_congr rfl fun B hB => ?_
  obtain ⟨C, -, hsingle⟩ := hT.setOf_mem_and_mem_dadeSubsetOrbit hB
  rw [hsingle, finsum_mem_singleton]

theorem IsDadeData.natCard_dadeSubsetGroup (hD : IsDadeData L A H) (hBA : B ⊆ A)
    (hB : B.Nonempty) :
    Nat.card (dadeSubsetGroup H L B) = Nat.card (dadeInter H B) * Nat.card (dadeStab L B) :=
  natCard_eq_mul_of_mul_eq_of_inf_eq_bot (hD.coe_dadeInter_mul_dadeStab hBA)
    (hD.dadeInter_inf_dadeStab_eq_bot hBA hB)

theorem finsum_dadeExpansionWeightedTerm_eq_zero (hD : IsDadeData L A H) {f : L → ℂ}
    (hf0 : ∀ x : L, (x : G) ∉ A → f x = 0) (hg : g ∉ totalDadeSupport A H) :
    ∑ᶠ B ∈ dadeNonemptySubsets A, dadeExpansionWeightedTerm hD f B g = 0 := by
  refine finsum_mem_of_eqOn_zero fun B hB => ?_
  rw [dadeExpansionWeightedTerm, dadeExpansionTerm_of_mem hD f hB.1 hB.2,
    hD.indClassFun_dadePullback_eq_zero hB.2 hB.1 hf0 hg]
  simp

theorem dadeExpansionWeightedTerm_apply_of_mem_dadeSupport (hD : IsDadeData L A H)
    (hBA : B ⊆ A) (hB : B.Nonempty) {f : L → ℂ} (hf : IsClassFun f)
    (hf0 : ∀ x : L, (x : G) ∉ A → f x = 0) (ha : a ∈ A) (hg : g ∈ dadeSupport H a) :
    dadeExpansionWeightedTerm hD f B g
      = -(f ⟨a, hD.mem_of_mem ha⟩ / (Nat.card L : ℂ)) *
        ∑ᶠ b ∈ ((dadeStab L B : Set G) ∩ conjClassIn L a),
          ((-1 : ℂ) ^ B.ncard * ((dadeTransporter H B g b).ncard : ℂ) /
            (Nat.card (dadeInter H B) : ℂ)) := by
  have hHne : (Nat.card (dadeInter H B) : ℂ) ≠ 0 := by
    simpa using (Nat.card_pos (α := dadeInter H B)).ne'
  have hNne : (Nat.card (dadeStab L B) : ℂ) ≠ 0 := by
    simpa using (Nat.card_pos (α := dadeStab L B)).ne'
  have hLne : (Nat.card L : ℂ) ≠ 0 := by
    simpa using (Nat.card_pos (α := L)).ne'
  have hpull : ∑ᶠ b ∈ ((dadeStab L B : Set G) ∩ conjClassIn L a),
        ((-1 : ℂ) ^ B.ncard * ((dadeTransporter H B g b).ncard : ℂ) /
          (Nat.card (dadeInter H B) : ℂ))
      = ((-1 : ℂ) ^ B.ncard / (Nat.card (dadeInter H B) : ℂ)) *
        ∑ᶠ b ∈ ((dadeStab L B : Set G) ∩ conjClassIn L a),
          ((dadeTransporter H B g b).ncard : ℂ) := by
    rw [mul_finsum_mem _ (Set.toFinite _)]
    exact finsum_mem_congr rfl fun b _ => by ring
  rw [hpull, dadeExpansionWeightedTerm, dadeExpansionTerm_of_mem hD f hB hBA,
    hD.indClassFun_dadePullback_apply_of_mem_dadeSupport hBA hB hf hf0 ha hg,
    hD.natCard_dadeSubsetGroup hBA hB]
  push_cast
  rw [pow_succ]
  field_simp

theorem conjClassIn_eq_setOf (L : Subgroup G) (a : G) :
    conjClassIn L a = {b : G | ∃ l ∈ L, l * a * l⁻¹ = b} :=
  Set.ext fun _ => mem_conjClassIn_iff

theorem ncard_conjClassIn_mul_natCard_inf_centralizer_cast (L : Subgroup G) (a : G) :
    ((conjClassIn L a).ncard : ℂ) *
      (Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : ℂ) = (Nat.card L : ℂ) := by
  rw [conjClassIn_eq_setOf, ← Nat.cast_mul]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (ncard_setOf_conj_mul_natCard_inf_centralizer L a)

theorem setOf_mem_dadeNonemptySubsets_and_mem_dadeStab (hbL : b ∈ L) :
    {B : Set G | B ∈ dadeNonemptySubsets A ∧ b ∈ dadeStab L B} = dadeInvariantSubsets A b := by
  ext B
  simp only [Set.mem_ofPred_eq, mem_dadeNonemptySubsets_iff, mem_dadeInvariantSubsets_iff,
    dadeStab_eq_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, hbL, h3⟩

theorem finsum_alternating_eq_neg_natCard_inf_centralizer (hD : IsDadeData L A H)
    (ha : a ∈ A) (hg : g ∈ dadeSupport H a) (hb : b ∈ conjClassIn L a) :
    ∑ᶠ B ∈ {B : Set G | B ∈ dadeNonemptySubsets A ∧ b ∈ dadeStab L B},
        ((-1 : ℂ) ^ B.ncard * ((dadeTransporter H B g b).ncard : ℂ) /
          (Nat.card (dadeInter H B) : ℂ))
      = -(Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : ℂ) := by
  obtain ⟨l, hl, hlb⟩ := mem_conjClassIn_iff.1 hb
  have hbA : b ∈ A := hlb ▸ hD.conj_mem ha hl
  have hbL : b ∈ L := hD.mem_of_mem hbA
  have hgb : g ∈ dadeSupport H b := by
    rw [← hlb, hD.dadeSupport_conj ha hl]
    exact hg
  have hcard : Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G)
      = Nat.card (L ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) :=
    natCard_inf_centralizer_eq_of_conj L hl hlb
  have hcast := finsum_mem_ratCast (dadeInvariantSubsets A b) (Set.toFinite _)
    (dadeAlternatingTerm H g b)
  rw [hD.finsum_dadeAlternatingTerm hbA hgb] at hcast
  have hterm : ∀ B : Set G,
      ((-1 : ℂ) ^ B.ncard * ((dadeTransporter H B g b).ncard : ℂ) /
        (Nat.card (dadeInter H B) : ℂ)) = ((dadeAlternatingTerm H g b B : ℚ) : ℂ) := by
    intro B
    rw [dadeAlternatingTerm_eq_mul_div]
    push_cast [Nat.card_coe_set_eq]
    ring
  rw [setOf_mem_dadeNonemptySubsets_and_mem_dadeStab (A := A) hbL, hcard,
    finsum_mem_congr rfl (fun B (_ : B ∈ dadeInvariantSubsets A b) => hterm B), ← hcast]
  push_cast
  ring

theorem finsum_dadeExpansionWeightedTerm_apply_of_mem_dadeSupport (hD : IsDadeData L A H)
    {f : L → ℂ} (hf : IsClassFun f) (hf0 : ∀ x : L, (x : G) ∉ A → f x = 0) (ha : a ∈ A)
    (hg : g ∈ dadeSupport H a) :
    ∑ᶠ B ∈ dadeNonemptySubsets A, dadeExpansionWeightedTerm hD f B g
      = f ⟨a, hD.mem_of_mem ha⟩ := by
  have hLne : (Nat.card L : ℂ) ≠ 0 := by
    simpa using (Nat.card_pos (α := L)).ne'
  have horb := ncard_conjClassIn_mul_natCard_inf_centralizer_cast L a
  set q : Set G → G → ℂ := fun B b =>
    (-1 : ℂ) ^ B.ncard * ((dadeTransporter H B g b).ncard : ℂ) /
      (Nat.card (dadeInter H B) : ℂ)
  have hswap : ∑ᶠ B ∈ dadeNonemptySubsets A,
        ∑ᶠ b ∈ ((dadeStab L B : Set G) ∩ conjClassIn L a), q B b
      = ∑ᶠ b ∈ conjClassIn L a,
        ∑ᶠ B ∈ {B : Set G | B ∈ dadeNonemptySubsets A ∧ b ∈ dadeStab L B}, q B b := by
    refine finsum_mem_comm_of_iff _ _ _ _ q fun B b => ?_
    constructor
    · rintro ⟨hB, hb1, hb2⟩
      exact ⟨hb2, hB, hb1⟩
    · rintro ⟨hb2, hB, hb1⟩
      exact ⟨hB, hb1, hb2⟩
  rw [finsum_mem_congr (rfl : dadeNonemptySubsets A = dadeNonemptySubsets A) (fun B hB => by
      rw [dadeExpansionWeightedTerm_apply_of_mem_dadeSupport hD hB.2 hB.1 hf hf0 ha hg]),
    ← mul_finsum_mem _ (Set.toFinite _), hswap,
    finsum_mem_congr (rfl : conjClassIn L a = conjClassIn L a) (fun b hb =>
      finsum_alternating_eq_neg_natCard_inf_centralizer hD ha hg hb),
    finsum_mem_const_eq _ (Set.toFinite _),
    show -(f ⟨a, hD.mem_of_mem ha⟩ / (Nat.card L : ℂ)) * (((conjClassIn L a).ncard : ℂ) *
        -(Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : ℂ))
      = (f ⟨a, hD.mem_of_mem ha⟩ / (Nat.card L : ℂ)) * (((conjClassIn L a).ncard : ℂ) *
        (Nat.card (L ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : ℂ)) by ring, horb]
  field_simp

theorem IsDadeData.dadeMap_apply_eq_finsum_dadeExpansionTerm (hD : IsDadeData L A H)
    {T : Set (Set G)} (hT : IsDadeSubsetTransversal L A T) (f : dadeDomain L A) :
    ((dadeMap hD f : classFun G) : G → ℂ)
      = fun g => ∑ᶠ B ∈ T, dadeExpansionTerm hD (f : L → ℂ) B g := by
  have hf : IsClassFun (f : L → ℂ) :=
    isClassFun_iff.2 fun x _ =>
      dadeDomain.apply_eq_of_isConj (SetLike.coe_mem f) (_root_.isConj_iff.2 ⟨x⁻¹, by group⟩)
  have hf0 : ∀ x : L, (x : G) ∉ A → (f : L → ℂ) x = 0 :=
    fun _ hx => dadeDomain.apply_eq_zero (SetLike.coe_mem f) hx
  funext g
  rw [finsum_dadeExpansionTerm_eq_finsum_dadeExpansionWeightedTerm hD hT hf g]
  by_cases hg : g ∈ totalDadeSupport A H
  · obtain ⟨a, ha, hga⟩ := mem_totalDadeSupport_iff.1 hg
    rw [dadeMap_apply_of_mem_dadeSupport hD f ha hga,
      finsum_dadeExpansionWeightedTerm_apply_of_mem_dadeSupport hD hf hf0 ha hga]
  · rw [finsum_dadeExpansionWeightedTerm_eq_zero hD hf0 hg, dadeMap_apply_coe,
      dadeSupportExtension_eq_zero_of_notMem hg]

theorem IsDadeData.dadeMap_apply_apply_eq_finsum_dadeExpansionTerm (hD : IsDadeData L A H)
    {T : Set (Set G)} (hT : IsDadeSubsetTransversal L A T) (f : dadeDomain L A) (g : G) :
    ((dadeMap hD f : classFun G) : G → ℂ) g
      = ∑ᶠ B ∈ T, dadeExpansionTerm hD (f : L → ℂ) B g := by
  rw [hD.dadeMap_apply_eq_finsum_dadeExpansionTerm hT f]

theorem IsDadeData.dadeMap_apply_eq_zero_of_empty (hD : IsDadeData L (∅ : Set G) H)
    (f : dadeDomain L (∅ : Set G)) : ((dadeMap hD f : classFun G) : G → ℂ) = 0 := by
  obtain ⟨T, hT⟩ := exists_isDadeSubsetTransversal hD
  rw [hD.dadeMap_apply_eq_finsum_dadeExpansionTerm hT f, hT.eq_empty_of_empty]
  funext g
  simp

end Term

end CFSG.FeitThompson
