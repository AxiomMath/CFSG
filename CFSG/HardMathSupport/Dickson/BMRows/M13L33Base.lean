
module

public import Certificates.Data.M13L33
public import Certificates.Certificate17633
public import CFSG.GH74.KGroups.L33
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

@[expose] public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows.M13L33

open CFSG.CosetTable CFSG.GH74.KGroups CFSG.GH74.KGroups.L33

def evalRel {H : Type*} [Group H] (f : Fin 2 → H) (r : List (Fin 2 × Bool)) : H :=
  (r.map fun l => cond l.2 (f l.1) (f l.1)⁻¹).prod

noncomputable def l33Hom {H : Type*} [Group H] (f : Fin 2 → H)
    (h : ∀ r ∈ l33Rels, evalRel f r = 1) : PG 2 l33Rels →* H :=
  PresentedGroup.toGroup (f := f) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact h w hw)

theorem l33Hom_of {H : Type*} [Group H] (f : Fin 2 → H) (h : ∀ r ∈ l33Rels, evalRel f r = 1)
    (i : Fin 2) : l33Hom f h (PresentedGroup.of i) = f i := by
  rw [l33Hom, PresentedGroup.toGroup.of]

theorem range_l33Hom {H : Type*} [Group H] (f : Fin 2 → H) (h : ∀ r ∈ l33Rels, evalRel f r = 1) :
    (l33Hom f h).range = Subgroup.closure (Set.range f) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin 2) | r ∈ l33Rels.map FreeGroup.mk}, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (l33Hom_of f h i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, l33Hom_of f h i⟩

section P13

def l33Img : Fin 2 → Equiv.Perm (Fin 13) := ![pa, pa * pb]

theorem l33Img_relators : ∀ w ∈ l33Rels, evalRel l33Img w = 1 := by
  decide +kernel

theorem pa_mul_self : pa * pa = 1 := by decide +kernel

noncomputable def l33HomP : PG 2 l33Rels →* Equiv.Perm (Fin 13) := l33Hom l33Img l33Img_relators

theorem range_l33HomP : l33HomP.range = Subgroup.closure {pa, pb} := by
  rw [l33HomP, range_l33Hom]
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · refine (Subgroup.closure_le _).2 ?_
    have ha : pa ∈ Subgroup.closure (Set.range l33Img) :=
      Subgroup.subset_closure ⟨0, rfl⟩
    have hb : pa * pb ∈ Subgroup.closure (Set.range l33Img) :=
      Subgroup.subset_closure ⟨1, rfl⟩
    rintro _ (rfl | rfl)
    · exact ha
    · have : pb = pa * (pa * pb) := by rw [← mul_assoc, pa_mul_self, one_mul]
      rw [this]
      exact mul_mem ha hb

theorem l33HomP_mem (g : PG 2 l33Rels) : l33HomP g ∈ QP13.originalSubgroup := by
  rw [QP13_closure, ← range_l33HomP]
  exact ⟨g, rfl⟩

noncomputable def l33HomQ : PG 2 l33Rels →* QP13.originalSubgroup :=
  l33HomP.codRestrict _ l33HomP_mem

theorem l33HomQ_surjective : Function.Surjective l33HomQ := by
  rintro ⟨y, hy⟩
  rw [QP13_closure, ← range_l33HomP] at hy
  obtain ⟨g, rfl⟩ := hy
  exact ⟨g, rfl⟩

section Card

theorem card_pg_le : Finite (PG 2 l33Rels) ∧ Nat.card (PG 2 l33Rels) ≤ 5616 :=
  Certificates.certificate17633

noncomputable def l33Equiv : PG 2 l33Rels ≃* QP13.originalSubgroup :=
  MulEquiv.ofBijective l33HomQ (by
    haveI := card_pg_le.1
    refine l33HomQ_surjective.bijective_of_nat_card_le ?_
    rw [card_group QP13 QP13_ok, QP13_valid.2]
    exact card_pg_le.2)

theorem nonempty_equiv_psl :
    Nonempty (PG 2 l33Rels ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3)) := by
  obtain ⟨e⟩ := equiv_psl_P13
  exact ⟨l33Equiv.trans e.symm⟩

theorem isSimple_pg : IsSimpleGroup (PG 2 l33Rels) := by
  obtain ⟨e⟩ := nonempty_equiv_psl
  have hlin := CFSG.LinearGroups.linear_projective_simple (K := ZMod 3) (n := 3)
    (by norm_num) (Or.inl (by norm_num))
  exact (MulEquiv.isSimpleGroup_congr e).mpr hlin.2.1

noncomputable def slEquivPsl :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 3) :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq center_bot.symm)

theorem nonempty_equiv_sl :
    Nonempty (PG 2 l33Rels ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) := by
  obtain ⟨e⟩ := nonempty_equiv_psl
  exact ⟨e.trans slEquivPsl.symm⟩

end Card

end P13

section Monster

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

noncomputable def l33Gen : Fin 2 → Gmat := ![gw j1W, gw yW]

theorem l33Gen_zero : l33Gen 0 = gw j1W := rfl

theorem l33Gen_one : l33Gen 1 = gw yW := rfl

theorem gw_relW (hI : gw yIW = (gw yW)⁻¹) (ha : (gw j1W)⁻¹ = gw j1W)
    (r : List (Fin 2 × Bool)) : gw (relW r) = evalRel l33Gen r := by
  induction r with
  | nil => simp [relW, evalRel, gw_nil]
  | cons l r ih =>
    have hl : gw (letterW l) = cond l.2 (l33Gen l.1) (l33Gen l.1)⁻¹ := by
      obtain ⟨i, b⟩ := l
      fin_cases i
      · cases b <;> simp [letterW, l33Gen, ha]
      · cases b <;> simp [letterW, l33Gen, hI]
    have hrw : relW (l :: r) = relW r ++ letterW l := by
      simp [relW]
    rw [hrw, gw_append, ih, hl]
    simp [evalRel]

end Monster

end CFSG.HardMathSupport.Dickson.BMRows.M13L33
