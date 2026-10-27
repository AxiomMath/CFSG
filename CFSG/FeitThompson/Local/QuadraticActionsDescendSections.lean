module

public import CFSG.FeitThompson.Definitions.ElementActingQuadraticallyOnAGroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A P : Type*} [Group A] [Group P] {ρ : A →* MulAut P} {a : A} {N : Subgroup P}

def IsInvariantSubgroup (ρ : A →* MulAut P) (N : Subgroup P) : Prop :=
  ∀ b : A, ∀ v ∈ N, ρ b v ∈ N

theorem IsInvariantSubgroup.apply_mem (hN : IsInvariantSubgroup ρ N) (b : A) {v : P}
    (hv : v ∈ N) : ρ b v ∈ N := hN b v hv

theorem IsInvariantSubgroup.map_eq (hN : IsInvariantSubgroup ρ N) (b : A) :
    N.map (ρ b : P →* P) = N := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨v, hv, rfl⟩
    exact hN.apply_mem b hv
  · intro v hv
    refine ⟨ρ b⁻¹ v, hN.apply_mem b⁻¹ hv, ?_⟩
    change ρ b (ρ b⁻¹ v) = v
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem isInvariantSubgroup_iff_forall_map_eq :
    IsInvariantSubgroup ρ N ↔ ∀ b : A, N.map (ρ b : P →* P) = N :=
  ⟨fun hN => hN.map_eq, fun h b v hv => h b ▸ ⟨v, hv, rfl⟩⟩

theorem isInvariantSubgroup_top (ρ : A →* MulAut P) : IsInvariantSubgroup ρ (⊤ : Subgroup P) :=
  fun _ _ _ => Subgroup.mem_top _

theorem isInvariantSubgroup_bot (ρ : A →* MulAut P) : IsInvariantSubgroup ρ (⊥ : Subgroup P) := by
  intro b v hv
  rw [Subgroup.mem_bot] at hv
  simp [hv]

def IsInvariantSubgroup.restrictAut (hN : IsInvariantSubgroup ρ N) : A →* MulAut N where
  toFun b := (MulEquiv.subgroupMap (ρ b) N).trans (MulEquiv.subgroupCongr (hN.map_eq b))
  map_one' := by
    ext x
    rw [MulEquiv.coe_trans, Function.comp_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.coe_subgroupMap_apply]
    simp
  map_mul' b c := by
    ext x
    rw [MulEquiv.coe_trans, Function.comp_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.coe_subgroupMap_apply, map_mul, MulAut.mul_apply]
    rfl

@[simp]
theorem IsInvariantSubgroup.coe_restrictAut_apply (hN : IsInvariantSubgroup ρ N) (b : A)
    (x : N) : ((hN.restrictAut b x : N) : P) = ρ b (x : P) := (rfl)

def IsInvariantSubgroup.quotientAut [N.Normal] (hN : IsInvariantSubgroup ρ N) :
    A →* MulAut (P ⧸ N) where
  toFun b := QuotientGroup.congr N N (ρ b) (hN.map_eq b)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v => rw [MulAut.one_apply, QuotientGroup.congr_mk]; simp
  map_mul' b c := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

@[simp]
theorem IsInvariantSubgroup.quotientAut_mk [N.Normal] (hN : IsInvariantSubgroup ρ N) (b : A)
    (v : P) : hN.quotientAut b (QuotientGroup.mk v) = (QuotientGroup.mk (ρ b v) : P ⧸ N) := (rfl)

theorem displacementSubgroup_restrictAut_map_subtype_le (hN : IsInvariantSubgroup ρ N) (a : A) :
    (displacementSubgroup hN.restrictAut a).map N.subtype ≤ displacementSubgroup ρ a := by
  rw [Subgroup.map_le_iff_le_comap, displacementSubgroup_le_iff]
  intro v
  rw [Subgroup.mem_comap]
  have hv : (N.subtype (v⁻¹ * hN.restrictAut a v) : P) = (v : P)⁻¹ * ρ a (v : P) := by
    rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hN.coe_restrictAut_apply]
  rw [hv]
  exact mem_displacementSubgroup ρ a (v : P)

theorem displacementSubgroup_quotientAut [N.Normal] (hN : IsInvariantSubgroup ρ N) (a : A) :
    displacementSubgroup hN.quotientAut a
      = (displacementSubgroup ρ a).map (QuotientGroup.mk' N) := by
  refine le_antisymm ?_ ?_
  · rw [displacementSubgroup_le_iff]
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      refine ⟨v⁻¹ * ρ a v, mem_displacementSubgroup ρ a v, ?_⟩
      rw [QuotientGroup.mk'_apply, hN.quotientAut_mk]
      simp
  · rw [Subgroup.map_le_iff_le_comap, displacementSubgroup_le_iff]
    intro v
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]
    have hv : ((v⁻¹ * ρ a v : P) : P ⧸ N)
        = (QuotientGroup.mk v : P ⧸ N)⁻¹ * hN.quotientAut a (QuotientGroup.mk v) := by
      rw [hN.quotientAut_mk]
      simp
    rw [hv]
    exact mem_displacementSubgroup hN.quotientAut a _

theorem ActsQuadratically.restrictAut (h : ActsQuadratically ρ a) (hN : IsInvariantSubgroup ρ N) :
    ActsQuadratically hN.restrictAut a := by
  rw [actsQuadratically_iff_forall] at h ⊢
  intro v
  refine Subtype.ext ?_
  rw [hN.coe_restrictAut_apply, Subgroup.coe_mul, Subgroup.coe_inv, hN.coe_restrictAut_apply]
  exact h (v : P)

theorem ActsQuadratically.quotientAut [N.Normal] (h : ActsQuadratically ρ a)
    (hN : IsInvariantSubgroup ρ N) : ActsQuadratically hN.quotientAut a := by
  rw [actsQuadratically_iff_forall] at h ⊢
  intro x
  induction x using QuotientGroup.induction_on with
  | H v =>
    have e : (QuotientGroup.mk v : P ⧸ N)⁻¹ * hN.quotientAut a (QuotientGroup.mk v)
        = (QuotientGroup.mk (v⁻¹ * ρ a v) : P ⧸ N) := by
      rw [hN.quotientAut_mk]; simp
    rw [e, hN.quotientAut_mk, h v]

end CFSG.FeitThompson
