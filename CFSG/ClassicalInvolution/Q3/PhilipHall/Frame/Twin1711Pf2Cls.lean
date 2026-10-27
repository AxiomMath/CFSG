module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Top

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

namespace Twin1711

variable {G : Type} [Group G]

theorem noSandwichIn_of_ident {H : Type} [Group H] [Finite H] (R0 : Subgroup H) (x0 : H)
    (hid : ∀ (R : Subgroup H) (t : H), CoreData (⊤ : Subgroup H) R t →
      ∃ α : H ≃* H, α t = x0 ∧ R.map α.toMonoidHom = R0)
    (h4 : ∀ (B : Set (Subgroup H)) (N : Subgroup H),
      IsUniqueInvolution R0 x0 → SandwichData (⊤ : Subgroup H) R0 x0 B N → False) :
    NoSandwichIn H := by
  intro R t B N hC hS
  obtain ⟨α, hαt, hαR⟩ := hid R t hC
  let ψ : H →* H := α.symm.toMonoidHom
  have hψ : Function.Injective ψ := α.symm.injective
  have hr : ψ.range = ⊤ := MonoidHom.range_eq_top.2 α.symm.surjective
  have ht' : ψ x0 = t := by simp [ψ, ← hαt]
  rw [← hr] at hC hS
  have hC' := hC.comap hψ ht'
  have hS' := hS.comap hC.le hψ ht'
  have hRc : R.comap ψ = R0 := by
    rw [← hαR]
    ext y
    simp only [Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, by simp [ψ]⟩
    · rintro ⟨r, hr', rfl⟩
      simpa [ψ] using hr'
  rw [hRc] at hC' hS'
  exact h4 _ _ hC'.inv hS'

end Twin1711

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
