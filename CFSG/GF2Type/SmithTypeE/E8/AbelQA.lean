module

public import CFSG.GF2Type.SmithTypeE.E8.LeadFilt
public import CFSG.GF2Type.SmithTypeE.E8.ModD6
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SylowGlue
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SplitTables

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc CFSG.GF2Type.SmithTypeE.E8.Lead
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7n6)


theorem parabolicRadicalRoots_eq :
    parabolicRadicalRoots .E7 {i | i ≠ e7n6} = Tset 15625 := by
  ext β
  simp only [parabolicRadicalRoots, parabolicPosRoots, parabolicRoots, Set.mem_diff,
    Set.mem_setOf_eq, Set.mem_inter_iff, Tset]
  constructor
  · rintro ⟨⟨hβ, hp⟩, hn⟩
    refine ⟨hβ, hp, (c7_eq_one_iff hβ hp).1 ?_⟩
    rcases c7_cases hβ hp with h | h
    · exact absurd ⟨⟨hβ, fun i hi => by
        have : i = e7n6 := by simpa using hi
        subst this; exact h⟩, hβ, hp⟩ hn
    · exact h
  · rintro ⟨hβ, hp, h⟩
    have h1 := (c7_eq_one_iff hβ hp).2 h
    refine ⟨⟨hβ, hp⟩, ?_⟩
    rintro ⟨⟨-, hz⟩, -⟩
    have := hz e7n6 (by simp)
    rw [show β e7n6 = 1 from h1] at this
    exact absurd this one_ne_zero

theorem parabolicRadical_eq_Ge :
    parabolicRadical .E7 (ZMod 2) {i | i ≠ e7n6} = Ge 15625 := by
  rw [parabolicRadical, parabolicRadicalRoots_eq]
  rfl

theorem card_Ge_15625 : Nat.card (Ge 15625) = 2 ^ 27 := by
  rw [card_Ge]
  exact congrArg (2 ^ ·) ncard_c7

theorem abelian_eq_Ge_of_le {X : Subgroup (ModGL .E7 (ZMod 2))}
    (hXU : X ≤ posUnipotent .E7 (ZMod 2)) (hab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hcard : 2 ^ 27 ≤ Nat.card X) : X = Ge 15625 := by
  classical
  have hcle := card_le_two_pow_Psi hXU
  have hfin := Psi_finite X
  have hS : ∀ α ∈ hfin.toFinset, IsRoot .E7 α ∧ 0 < height α := fun α hα =>
    Psi_subset X (hfin.mem_toFinset.1 hα)
  have hsum : ∀ α ∈ hfin.toFinset, ∀ β ∈ hfin.toFinset, ¬ IsRoot .E7 (α + β) := fun α hα β hβ =>
    Psi_no_sum hab (hfin.mem_toFinset.1 hα) (hfin.mem_toFinset.1 hβ)
  obtain ⟨hle27, hRA⟩ := e8m_abelian27 hfin.toFinset hS hsum
  have hn : (Psi X).ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  rw [← hn] at hle27 hRA
  have h27 : 27 ≤ (Psi X).ncard := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ (Psi X).ncard < 2 ^ 27 := Nat.pow_lt_pow_right (by norm_num) hlt
    omega
  have heq : (Psi X).ncard = 27 := le_antisymm hle27 h27
  have hΨ : ∀ δ ∈ Psi X, (15625 : ℤ) ≤ lw δ := fun δ hδ => by
    have h1 := hRA heq δ (hfin.mem_toFinset.2 hδ)
    exact (c7_eq_one_iff (Psi_subset X hδ).1 (Psi_subset X hδ).2).1 h1
  have hle : X ≤ Ge 15625 := le_Ge_of_forall_Psi hXU (by norm_num) hΨ
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_Ge_15625]; exact hcard)

theorem abelian_conj_QA (E : Subgroup (ModGL .E7 (ZMod 2))) (hE : E ≤ adjointGroup .E7 (ZMod 2))
    (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hp : IsPGroup 2 E)
    (hcard : 2 ^ 27 ≤ Nat.card E) :
    ∃ g ∈ adjointGroup .E7 (ZMod 2),
      E = (parabolicRadical .E7 (ZMod 2) {i | i ≠ e7n6}).map (MulAut.conj g).toMonoidHom := by
  classical
  set A : Subgroup ↥(adjointGroup .E7 (ZMod 2)) := E.subgroupOf (adjointGroup .E7 (ZMod 2)) with hA
  have hAp : IsPGroup 2 A := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hE).symm
  obtain ⟨g, hg⟩ := adjoint_conj_into_U (ZMod 2) .E7 A hAp
  have hX : E.map (MulAut.conj (g : ModGL .E7 (ZMod 2))).toMonoidHom ≤
      posUnipotent .E7 (ZMod 2) := by
    rintro _ ⟨e, he, rfl⟩
    have h1 : (MulAut.conj g) ⟨e, hE he⟩ ∈ A.map (MulAut.conj g).toMonoidHom :=
      ⟨⟨e, hE he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hg h1)
  have hXab : ∀ a ∈ E.map (MulAut.conj (g : ModGL .E7 (ZMod 2))).toMonoidHom,
      ∀ b ∈ E.map (MulAut.conj (g : ModGL .E7 (ZMod 2))).toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hab a ha b hb
    calc (g : ModGL .E7 (ZMod 2)) * a * (g : ModGL .E7 (ZMod 2))⁻¹ *
          ((g : ModGL .E7 (ZMod 2)) * b * (g : ModGL .E7 (ZMod 2))⁻¹)
        = (g : ModGL .E7 (ZMod 2)) * (a * b) * (g : ModGL .E7 (ZMod 2))⁻¹ := by group
      _ = (g : ModGL .E7 (ZMod 2)) * (b * a) * (g : ModGL .E7 (ZMod 2))⁻¹ := by rw [this]
      _ = _ := by group
  have hcX : 2 ^ 27 ≤ Nat.card (E.map (MulAut.conj (g : ModGL .E7 (ZMod 2))).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (g : ModGL .E7 (ZMod 2))).injective]
    exact hcard
  have hEq := abelian_eq_Ge_of_le hX hXab hcX
  refine ⟨(g⁻¹ : ↥(adjointGroup .E7 (ZMod 2))), (g⁻¹).2, ?_⟩
  rw [parabolicRadical_eq_Ge, ← hEq, Subgroup.map_map]
  have hcomp : (MulAut.conj
        ((g⁻¹ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2))).toMonoidHom.comp
      (MulAut.conj (g : ModGL .E7 (ZMod 2))).toMonoidHom = MonoidHom.id _ := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.id_apply, Subgroup.coe_inv]
    group
  rw [hcomp, Subgroup.map_id]

theorem abelian_conj_QA_of_sq (E : Subgroup (ModGL .E7 (ZMod 2)))
    (hE : E ≤ adjointGroup .E7 (ZMod 2)) (hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ a ∈ E, a * a = 1) (hcard : 2 ^ 27 ≤ Nat.card E) :
    ∃ g ∈ adjointGroup .E7 (ZMod 2),
      E = (parabolicRadical .E7 (ZMod 2) {i | i ≠ e7n6}).map (MulAut.conj g).toMonoidHom := by
  refine abelian_conj_QA E hE hab ?_ hcard
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have h := hsq x x.2
  simpa [pow_two] using h

end CFSG.GF2Type.SmithTypeE.E8
