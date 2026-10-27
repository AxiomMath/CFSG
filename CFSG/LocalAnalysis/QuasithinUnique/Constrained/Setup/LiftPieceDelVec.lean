module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

open CFSG.QuasithinUnique.Setup.SL2Modules

section Vec

variable {Ω : Type*} [DecidableEq Ω]

theorem pair_apply_eq_one {a b : Ω} (hab : a ≠ b) (t : Ω) :
    (delta a - delta b) t = 1 ↔ t = a ∨ t = b := by
  simp only [Pi.sub_apply, delta, Pi.single_apply]
  by_cases h1 : t = a
  · subst h1
    simp [hab]
  · by_cases h2 : t = b
    · subst h2
      have : (0 : ZMod 2) - 1 = 1 := by decide
      simp [this, h1]
    · simp [h1, h2]

omit [DecidableEq Ω] in
theorem permAct_apply (σ : Equiv.Perm Ω) (x : Ω → ZMod 2) (t : Ω) :
    permAct σ x t = x (σ.symm t) := rfl

theorem perm_fix_of_pairs {τ : Equiv.Perm Ω} {x y z : Ω} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (h1 : permAct τ (delta y - delta x) = delta y - delta x)
    (h2 : permAct τ (delta z - delta y) = delta z - delta y)
    (h3 : permAct τ (delta x - delta z) = delta x - delta z) :
    τ x = x ∧ τ y = y ∧ τ z = z := by
  have key : ∀ {a b : Ω}, a ≠ b → permAct τ (delta a - delta b) = delta a - delta b →
      ∀ t : Ω, (t = a ∨ t = b) → (τ.symm t = a ∨ τ.symm t = b) := by
    intro a b hab h t ht
    have h' := congrFun h t
    rw [permAct_apply] at h'
    have h1' : (delta a - delta b) t = 1 := (pair_apply_eq_one hab t).2 ht
    rw [h1'] at h'
    exact (pair_apply_eq_one hab (τ.symm t)).1 h'
  have hx1 := key hxy.symm h1 x (Or.inr rfl)
  have hx3 := key hxz h3 x (Or.inl rfl)
  have hy1 := key hxy.symm h1 y (Or.inl rfl)
  have hy2 := key hyz.symm h2 y (Or.inr rfl)
  have hz2 := key hyz.symm h2 z (Or.inl rfl)
  have hz3 := key hxz h3 z (Or.inr rfl)
  have ex : τ.symm x = x := by
    rcases hx1 with h | h
    · rcases hx3 with h' | h'
      · exact absurd (h.symm.trans h') hxy.symm
      · exact absurd (h.symm.trans h') hyz
    · exact h
  have ey : τ.symm y = y := by
    rcases hy1 with h | h
    · exact h
    · rcases hy2 with h' | h'
      · exact absurd (h.symm.trans h') hxz
      · exact h'
  have ez : τ.symm z = z := by
    rcases hz2 with h | h
    · exact h
    · rcases hz3 with h' | h'
      · exact absurd (h.symm.trans h') hxy.symm
      · exact absurd (h.symm.trans h') hyz
  exact ⟨(τ.symm_apply_eq.1 ex).symm, (τ.symm_apply_eq.1 ey).symm, (τ.symm_apply_eq.1 ez).symm⟩

end Vec

end CFSG.QuasithinUnique.Setup.Lift.Piece
