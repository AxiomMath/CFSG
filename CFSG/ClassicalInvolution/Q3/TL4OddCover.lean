module

public import CFSG.ClassicalInvolution.Q3.LieSystem

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

theorem cover_of_mulEquiv {H Q Q' : Type} [Group H] [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : ∃ ψ : H →* Q, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center _ ∧
      ∀ c ∈ Subgroup.center Q, ∃ f ∈ Subgroup.center _, ψ f = c) :
    ∃ ψ : H →* Q', Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center _ ∧
      ∀ c ∈ Subgroup.center Q', ∃ f ∈ Subgroup.center _, ψ f = c := by
  obtain ⟨ψ, hψ, hker, hcen⟩ := h
  refine ⟨e.toMonoidHom.comp ψ, e.surjective.comp hψ, fun g hg => hker ?_, fun c hc => ?_⟩
  · rw [MonoidHom.mem_ker] at hg ⊢
    exact (MulEquiv.map_eq_one_iff e).mp hg
  · have hc' : e.symm c ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro q
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hc (e q)
    obtain ⟨f, hf, hfc⟩ := hcen _ hc'
    exact ⟨f, hf, by
      show e (ψ f) = c
      rw [hfc, MulEquiv.apply_symm_apply]⟩

section Cover


@[expose] def CoverSp4 (Q : Type) [Group Q] : Prop :=
  ∃ ψ : (Q3.CompData.model .PSp 2).G →* Q, Function.Surjective ψ ∧
    ψ.ker ≤ Subgroup.center _ ∧ ∀ c ∈ Subgroup.center Q, ∃ f ∈ Subgroup.center _, ψ f = c

@[expose] def CoverSL4 (Q : Type) [Group Q] : Prop :=
  ∃ ψ : (Q3.CompData.model .PSL 4).G →* Q, Function.Surjective ψ ∧
    ψ.ker ≤ Subgroup.center _ ∧ ∀ c ∈ Subgroup.center Q, ∃ f ∈ Subgroup.center _, ψ f = c

theorem CoverSp4.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : CoverSp4 Q) : CoverSp4 Q' :=
  cover_of_mulEquiv e h

theorem CoverSL4.of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : CoverSL4 Q) : CoverSL4 Q' :=
  cover_of_mulEquiv e h

end Cover

end CFSG.ClassicalInvolution.Q3.TL4
