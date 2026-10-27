module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrGrp

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open CFSG.EvenSporadicStandard.M22Std

theorem wrPerm_mem (x : Wr) : wrPerm x ∈ wreathS6Z2 := by
  have h1 : ∀ a b, pairPerm a b ∈ wreathS6Z2 := fun a b _ _ => Iff.rfl
  show pairPerm x.a x.b * (if x.e then swapPerm else 1) ∈ wreathS6Z2
  refine Subgroup.mul_mem _ (h1 _ _) ?_
  split_ifs
  · exact swapPerm_mem
  · exact Subgroup.one_mem _

theorem exists_wr_hom {G : Type*} [Group G] (e : G → Bool) (N : G → Bool → Equiv.Perm (Fin 6))
    (he : ∀ g h, e (g * h) = xor (e g) (e h))
    (hN : ∀ g h i, N (g * h) i = N g (xor i (e h)) * N h i)
    (hinj : ∀ g, e g = false → N g false = 1 → N g true = 1 → g = 1) :
    ∃ f : G →* Equiv.Perm (Fin 2 × Fin 6), Function.Injective f ∧ ∀ g, f g ∈ wreathS6Z2 := by
  let F : G →* Wr := MonoidHom.mk' (fun g => ⟨N g (e g), N g (!e g), e g⟩) (by
    intro g h
    cases hg : e g <;> cases hh : e h <;> simp [he, hN, hg, hh])
  refine ⟨wrPerm.comp F, wrPerm_injective.comp ?_, fun g => wrPerm_mem _⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : (⟨N g (e g), N g (!e g), e g⟩ : Wr) = ⟨1, 1, false⟩ := hg
  have h2 := congrArg Wr.e h1
  have h3 := congrArg Wr.a h1
  have h4 := congrArg Wr.b h1
  simp only at h2 h3 h4
  apply hinj g h2
  · rw [h2] at h3
    exact h3
  · rw [h2] at h4
    exact h4

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
