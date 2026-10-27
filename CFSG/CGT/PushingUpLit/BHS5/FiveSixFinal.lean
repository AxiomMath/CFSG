module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_fixed_of_orbit {T E₀ E : Subgroup (MulAut V)} {u₁ : V}
    (hN : ∀ t ∈ T, t ∈ Subgroup.normalizer (E : Set (MulAut V)) → t u₁ = u₁)
    (hmove : ∃ g ∈ E₀, g u₁ ≠ u₁)
    (horth : ∀ t ∈ T, t ∉ Subgroup.normalizer (E : Set (MulAut V)) → t u₁ ∈ fixV E₀) :
    ∃ g ∈ E₀, ∃ u ∈ fixV T, g u ≠ u := by
  classical
  obtain ⟨g, hgE₀, hgu⟩ := hmove
  set S : Set V := Set.range fun t : ↥T => (t : MulAut V) u₁ with hS
  have hSfin : S.Finite := Set.finite_range _
  set S' : Set V := {w | ∃ t ∈ T, t ∉ Subgroup.normalizer (E : Set (MulAut V)) ∧ w = t u₁}
    with hS'
  have hS'fin : S'.Finite := hSfin.subset fun w ⟨t, ht, _, hw⟩ => ⟨⟨t, ht⟩, hw.symm⟩
  have hS'fix : ∀ w ∈ S', w ∈ fixV E₀ := by
    rintro w ⟨t, ht, htn, rfl⟩
    exact horth t ht htn
  have hu₁S' : u₁ ∉ S' := by
    rintro ⟨t, ht, htn, hw⟩
    have := horth t ht htn
    rw [← hw] at this
    exact hgu (this g hgE₀)
  have hSeq : S = insert u₁ S' := by
    ext w
    constructor
    · rintro ⟨⟨t, ht⟩, rfl⟩
      by_cases htn : t ∈ Subgroup.normalizer (E : Set (MulAut V))
      · left
        exact hN t ht htn
      · right
        exact ⟨t, ht, htn, rfl⟩
    · rintro (rfl | ⟨t, ht, -, rfl⟩)
      · exact ⟨⟨1, T.one_mem⟩, rfl⟩
      · exact ⟨⟨t, ht⟩, rfl⟩
  set u : V := ∏ᶠ w ∈ S, w with hu
  have hTfix : u ∈ fixV T := by
    intro s hs
    have h1 : s u = ∏ᶠ w ∈ S, s w := by
      rw [hu]
      exact MulEquiv.map_finprod_mem s (fun w => w) hSfin
    have himg : s '' S = S := by
      ext w
      constructor
      · rintro ⟨_, ⟨⟨t, ht⟩, rfl⟩, rfl⟩
        exact ⟨⟨s * t, T.mul_mem hs ht⟩, rfl⟩
      · rintro ⟨⟨t, ht⟩, rfl⟩
        refine ⟨(s⁻¹ * t) u₁, ⟨⟨s⁻¹ * t, T.mul_mem (T.inv_mem hs) ht⟩, rfl⟩, ?_⟩
        show s ((s⁻¹ * t) u₁) = t u₁
        rw [MulAut.mul_apply]
        exact MulAut.apply_inv_self V s (t u₁)
    have h2 : ∏ᶠ w ∈ S, s w = ∏ᶠ w ∈ s '' S, w := by
      rw [finprod_mem_image (f := fun w => w) (s.injective.injOn)]
    rw [h1, h2, himg]
  refine ⟨g, hgE₀, u, hTfix, ?_⟩
  have hu' : u = u₁ * ∏ᶠ w ∈ S', w := by
    rw [hu, hSeq, finprod_mem_insert (fun w => w) hu₁S' hS'fin]
  have hc : ∏ᶠ w ∈ S', w ∈ fixV E₀ :=
    finprod_mem_induction (fun x => x ∈ fixV E₀) (fixV E₀).one_mem
      (fun x y hx hy => (fixV E₀).mul_mem hx hy) hS'fix
  intro hgfix
  apply hgu
  rw [hu', map_mul, hc g hgE₀] at hgfix
  exact mul_right_cancel hgfix

end CFSG.CGT.PushingUpLit.BHS5
