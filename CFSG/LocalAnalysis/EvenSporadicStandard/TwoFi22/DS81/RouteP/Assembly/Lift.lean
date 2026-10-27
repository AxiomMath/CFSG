module

public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

theorem exists_injective_lift_of_ker_le {Q S G : Type*} [Group Q] [Group S] [Group G]
    (q : Q →* S) (hq : Function.Surjective q) (hS : IsSimpleGroup S) (Φ : Q →* G)
    (hker : q.ker ≤ Φ.ker) (hΦ : Φ ≠ 1) :
    ∃ Φbar : S →* G, Function.Injective Φbar ∧ ∀ x, Φbar (q x) = Φ x := by
  let Φbar : S →* G := (q.liftOfSurjective hq) ⟨Φ, hker⟩
  have hcomp : ∀ x, Φbar (q x) = Φ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply q (Function.surjInv hq)
      (Function.rightInverse_surjInv hq) ⟨Φ, hker⟩ x
  have hkerbar : Φbar.ker = ⊥ := by
    rcases hS.eq_bot_or_eq_top_of_normal Φbar.ker with h | h
    · exact h
    · exfalso
      have hone : Φbar = 1 := (MonoidHom.ker_eq_top_iff (f := Φbar)).mp h
      apply hΦ
      ext x
      simp [← hcomp x, hone]
  exact ⟨Φbar, (MonoidHom.ker_eq_bot_iff Φbar).mp hkerbar, hcomp⟩

theorem exists_injective_lift_range_eq_of_ker_le {Q S G : Type*} [Group Q] [Group S] [Group G]
    (q : Q →* S) (hq : Function.Surjective q) (hS : IsSimpleGroup S) (Φ : Q →* G)
    (hker : q.ker ≤ Φ.ker) (hΦ : Φ ≠ 1) :
    ∃ Φbar : S →* G, Function.Injective Φbar ∧ (∀ x, Φbar (q x) = Φ x) ∧
      Φbar.range = Φ.range := by
  obtain ⟨Φbar, hinj, hcomp⟩ := exists_injective_lift_of_ker_le q hq hS Φ hker hΦ
  refine ⟨Φbar, hinj, hcomp, ?_⟩
  have hΦeq : Φ = Φbar.comp q := MonoidHom.ext fun x => (hcomp x).symm
  rw [hΦeq, MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective q hq,
    MonoidHom.range_eq_map]

theorem exists_mulEquiv_range_of_ker_le {Q S G : Type*} [Group Q] [Group S] [Group G]
    (q : Q →* S) (hq : Function.Surjective q) (hS : IsSimpleGroup S) (Φ : Q →* G)
    (hker : q.ker ≤ Φ.ker) (hΦ : Φ ≠ 1) :
    ∃ e : S ≃* Φ.range, ∀ x, ((e (q x) : Φ.range) : G) = Φ x := by
  obtain ⟨Φbar, hinj, hcomp, hrange⟩ :=
    exists_injective_lift_range_eq_of_ker_le q hq hS Φ hker hΦ
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), hcomp⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
