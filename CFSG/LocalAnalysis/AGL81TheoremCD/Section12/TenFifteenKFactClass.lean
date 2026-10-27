module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def ParabolicClassFixed (Y : Type*) [Group Y] : Prop :=
  ∀ P : Subgroup Y, IsParabolicTwo ⊤ P → ∀ α : MulAut Y, Nat.Coprime (orderOf α) 6 →
    ∃ y : Y, P.map α.toMonoidHom = P.map (MulAut.conj y).toMonoidHom

variable {Y : Type*} [Group Y] {B₀ : Subgroup Y}

theorem exists_le_map_conj_of_isParabolicTwo [Finite Y] (U₀ : Sylow 2 Y)
    (hU₀ : Subgroup.normalizer ((U₀ : Subgroup Y) : Set Y) = B₀) {P : Subgroup Y}
    (hP : IsParabolicTwo ⊤ P) : ∃ g : Y, B₀ ≤ P.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, T, ⟨-, hT2, hTi⟩, hTP⟩ := hP
  have hidx : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hTi
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y U₀ (hT2.toSylow hidx)
  have hT : (U₀ : Subgroup Y).map (MulAut.conj g).toMonoidHom = T := by
    rw [← IsPGroup.toSylow_coe hT2 hidx, ← hg, Sylow.coe_subgroup_smul]
    rfl
  refine ⟨g⁻¹, fun x hx => ⟨MulAut.conj g x, ?_, by simp [mul_assoc]⟩⟩
  rw [top_inf_eq, ← hT, ← Subgroup.map_equiv_normalizer_eq, hU₀] at hTP
  exact hTP ⟨x, hx, rfl⟩

theorem exists_map_conj_inv_mul_eq [Finite Y] (U₀ : Sylow 2 Y) (α : MulAut Y) :
    ∃ h : Y, (U₀ : Subgroup Y).map ((MulAut.conj h)⁻¹ * α).toMonoidHom = U₀ := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq Y U₀ (α • U₀)
  refine ⟨h, ?_⟩
  have h1 : (U₀ : Subgroup Y).map (MulAut.conj h).toMonoidHom =
      (U₀ : Subgroup Y).map α.toMonoidHom :=
    congrArg (fun Q : Sylow 2 Y => (Q : Subgroup Y)) hh
  have hcomp : ((MulAut.conj h)⁻¹ * α).toMonoidHom =
      ((MulAut.conj h)⁻¹).toMonoidHom.comp α.toMonoidHom := MonoidHom.ext fun _ => rfl
  have hone : ((MulAut.conj h)⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      MonoidHom.id Y := MonoidHom.ext fun x => by simp [mul_assoc]
  rw [hcomp, ← Subgroup.map_map, ← h1, Subgroup.map_map, hone, Subgroup.map_id]

theorem pow_orderOf_mem_inner {α β : MulAut Y} (hβ : β ∈ inner Y) :
    (β * α) ^ orderOf α ∈ inner Y := by
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff β).2 hβ, one_mul, ← QuotientGroup.mk_pow, pow_orderOf_eq_one,
    QuotientGroup.mk_one]

theorem exists_map_eq_map_conj_of_map_eq {α : MulAut Y} {P : Subgroup Y} {g h : Y}
    (hfix : (P.map (MulAut.conj g).toMonoidHom).map ((MulAut.conj h)⁻¹ * α).toMonoidHom =
      P.map (MulAut.conj g).toMonoidHom) :
    ∃ y : Y, P.map α.toMonoidHom = P.map (MulAut.conj y).toMonoidHom := by
  refine ⟨(α g)⁻¹ * h * g, ?_⟩
  apply Subgroup.map_injective (f := ((MulAut.conj h)⁻¹ * MulAut.conj (α g)).toMonoidHom)
    (MulEquiv.injective _)
  have e1 : ((MulAut.conj h)⁻¹ * MulAut.conj (α g)).toMonoidHom.comp α.toMonoidHom =
      ((MulAut.conj h)⁻¹ * α).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp [mul_assoc]
  have e2 : ((MulAut.conj h)⁻¹ * MulAut.conj (α g)).toMonoidHom.comp
      (MulAut.conj ((α g)⁻¹ * h * g)).toMonoidHom = (MulAut.conj g).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [Subgroup.map_map, Subgroup.map_map, e1, e2, ← Subgroup.map_map, hfix]

theorem parabolicClassFixed_of_card_outer_le_four [Finite Y]
    (h : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) ≤ 4) :
    ParabolicClassFixed Y := by
  intro P _ α hα
  have : Finite (MulAut Y) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (inner Y))
  have h1 : orderOf (QuotientGroup.mk' (inner Y) α) ∣ orderOf α := orderOf_map_dvd _ α
  have h2 : orderOf (QuotientGroup.mk' (inner Y) α) ∣
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) := orderOf_dvd_natCard _
  have hcop := Nat.Coprime.coprime_dvd_left h1 hα
  have hle := (Nat.le_of_dvd Nat.card_pos h2).trans h
  have hpos := Nat.pos_of_dvd_of_pos h2 Nat.card_pos
  have h3 : orderOf (QuotientGroup.mk' (inner Y) α) = 1 := by
    generalize orderOf (QuotientGroup.mk' (inner Y) α) = o at hcop hle hpos ⊢
    interval_cases o
    · rfl
    all_goals exact absurd hcop (by decide)
  have h4 : (α : CFSG.ComponentClassification.OuterAutomorphisms.Outer Y) = 1 :=
    orderOf_eq_one_iff.1 h3
  obtain ⟨y, hy⟩ : α ∈ inner Y := (QuotientGroup.eq_one_iff α).1 h4
  exact ⟨y, by rw [hy]⟩

theorem parabolicClassFixed_of_forall_commute (h : ∀ a b : Y, a * b = b * a) :
    ParabolicClassFixed Y := by
  intro P hP α _
  obtain ⟨-, T, -, hT⟩ := hP
  have hN : Subgroup.normalizer (T : Set Y) = ⊤ := by
    refine eq_top_iff.2 fun g _ => Subgroup.mem_normalizer_iff.2 fun x => ?_
    rw [h g x, mul_inv_cancel_right]
  rw [hN, top_inf_eq, top_le_iff] at hT
  refine ⟨1, ?_⟩
  rw [hT, Subgroup.map_top_of_surjective _ α.surjective,
    Subgroup.map_top_of_surjective _ (MulAut.conj (1 : Y)).surjective]

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
