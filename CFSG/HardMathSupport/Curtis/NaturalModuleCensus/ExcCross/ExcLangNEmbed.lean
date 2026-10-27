module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE

section Main


theorem exists_embedding_nfix {τ : Tag} (w : WeylGroup τ) {F : Type} [Field F] [Finite F]
    {L : Type} [Field L] [Algebra F L] [IsAlgClosure F L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card F)
    (hrel : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
      ((adjointGroup τ F).map (baseChangeGL (algebraMap F L))).relIndex X ∣ 1)
    (hfin : Finite (NFix (canonicalRep (coxeterSystem τ) L w) Fr)) :
    ∃ ι : NFix (canonicalRep (coxeterSystem τ) L w) Fr →* ↥(adjointGroup τ F),
      Function.Injective ι := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨hℓ⟩
  have hq : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP F (ringChar F) := ringChar.charP F
  have : CharP L (ringChar F) := charP_of_injective_algebraMap (algebraMap F L).injective _
  have hFrEq : Fr = iterateFrobenius L (ringChar F) (f : ℕ) := RingHom.ext fun c => by
    rw [hFr, hq]
    exact (iterateFrobenius_def (ringChar F) (f : ℕ) c).symm
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ F (ℓ := ringChar F) (f := (f : ℕ)) f.pos L w
  rw [← hFrEq] at hg0
  let c : ModGL τ L →* ModGL τ L := (MulAut.conj g0).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g0).injective
  have hc_apply : ∀ x, c x = g0 * x * g0⁻¹ := fun x => rfl
  set X : Subgroup (ModGL τ L) := (NFix (canonicalRep (coxeterSystem τ) L w) Fr).map c with hX
  have hXfin : Finite X :=
    Finite.of_surjective (c.subgroupMap _) (c.subgroupMap_surjective _)
  have hXC : X ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (monomialSubgroup_le_adjointGroup' (hx.1))) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix : negPhi Fr (canonicalRep (coxeterSystem τ) L w) x = x := hx.2
    rw [negPhi_apply] at hxfix
    rw [hc_apply, map_mul, map_mul, map_inv, hg0]
    calc g0 * canonicalRep (coxeterSystem τ) L w * Units.map (entrywiseHom Fr) x *
          (g0 * canonicalRep (coxeterSystem τ) L w)⁻¹ =
        g0 * (canonicalRep (coxeterSystem τ) L w * Units.map (entrywiseHom Fr) x *
          (canonicalRep (coxeterSystem τ) L w)⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  let ι : ↥(adjointGroup τ F) →* ModGL τ L :=
    (baseChangeGL (algebraMap F L)).comp (adjointGroup τ F).subtype
  have hrange : ι.range = (adjointGroup τ F).map (baseChangeGL (algebraMap F L)) := by
    change ((baseChangeGL (algebraMap F L)).comp (adjointGroup τ F).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hr1 := hrel X hXC hXF
  have hr : ((adjointGroup τ F).map (baseChangeGL (algebraMap F L))).relIndex X = 1 :=
    Nat.dvd_one.1 hr1
  have hXr : X ≤ ι.range := by
    rw [hrange]
    exact Subgroup.relIndex_eq_one.1 hr
  let φ : NFix (canonicalRep (coxeterSystem τ) L w) Fr →* ModGL τ L :=
    c.comp (NFix (canonicalRep (coxeterSystem τ) L w) Fr).subtype
  have hφ : ∀ x, φ x ∈ ι.range := fun x => hXr ⟨x, x.2, rfl⟩
  refine ⟨((MonoidHom.ofInjective hι).symm : ι.range ≃* ↥(adjointGroup τ F)).toMonoidHom.comp
    (φ.codRestrict ι.range hφ), ?_⟩
  intro x y hxy
  have h1 := ((MonoidHom.ofInjective hι).symm).injective hxy
  exact Subtype.ext (hc (Subtype.ext_iff.1 h1))

end Main

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
