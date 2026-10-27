module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL5
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Surv

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem genericKill_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') (α : MulAut Y)
    (α' : MulAut Y') (hαα' : ∀ x, e (α x) = α' (e x)) (h : GenericKill Y' α') : GenericKill Y α := by
  rcases h with ⟨Q', hQp, hQ', T, _, hTs, c', hc', hns, hbad⟩ | ⟨hnotinn, E', hEc, hE2, hEcard, hEfix⟩
  · refine Or.inl ⟨Q'.map e.symm.toMonoidHom, ?_, ?_, T, ‹_›, hTs, ?_⟩
    · have hQ : ↥Q' ≃* ↥(Q'.map e.symm.toMonoidHom) :=
        Subgroup.equivMapOfInjective Q' e.symm.toMonoidHom e.symm.injective
      have : Group.IsPerfect ↥Q' := hQp
      exact Group.IsPerfect.ofSurjective (f := hQ.toMonoidHom) hQ.surjective
    · rintro _ ⟨s', hs', rfl⟩
      have h1 := hQ' s' hs'
      apply e.injective
      rw [hαα']
      simpa using h1
    · exact ⟨c'.comp (Subgroup.equivMapOfInjective Q' e.symm.toMonoidHom e.symm.injective).symm.toMonoidHom,
        hc'.comp (MulEquiv.surjective _), hns, hbad⟩
  · refine Or.inr ⟨fun s hs => hnotinn (e s) ?_, E'.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · ext y
      have h2 := hαα' (e.symm y)
      rw [MulEquiv.apply_symm_apply] at h2
      rw [← h2, hs]
      simp [MulAut.conj_apply]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hEc a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hE2 a ha, map_one]
    · rw [← Nat.card_congr (Subgroup.equivMapOfInjective E' e.symm.toMonoidHom e.symm.injective).toEquiv]
      exact hEcard
    · rintro _ ⟨a, ha, rfl⟩
      apply e.injective
      rw [hαα']
      simpa using hEfix a ha

theorem genericKill_of_sl3_block {F : Type} [Field F] [Finite F] {n p0 : ℕ} [Fact p0.Prime]
    [CharP F p0] (hp0 : p0 ≠ 2) (hodd : Odd (Nat.card F)) (h3 : 3 ≤ Nat.card F)
    (α : MulAut (projectiveSL n F)) (ρ : SpecialLinearGroup (Fin 3) F →* projectiveSL n F)
    (hρ : Function.Injective ρ) (hfix : ∀ g, α (ρ g) = ρ g) : GenericKill (projectiveSL n F) α := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
  have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  let c : ↥ρ.range →* projectiveSL 3 F :=
    (QuotientGroup.mk' (scalars 3 F)).comp (MonoidHom.ofInjective hρ).symm.toMonoidHom
  have hc : Function.Surjective c :=
    (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hρ).symm.surjective
  have hs := isSimpleGroup_projectiveSL3 F
  have hp := isPerfect_projectiveSL3 F
  have : Nontrivial (projectiveSL 3 F) := IsSimpleGroup.toNontrivial
  refine Or.inl ⟨ρ.range, ‹_›, ?_, projectiveSL 3 F, inferInstance, hs, c, hc,
    Group.IsPerfect.not_isSolvable _, fun k => not_kindFactor hp0
      (involved_qdSL_projectiveSL3 (p := p0)) (not_card_dvd_factorial_projectiveSL3 hodd h3)⟩
  rintro _ ⟨g, rfl⟩
  exact hfix g

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
