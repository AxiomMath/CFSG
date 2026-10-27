module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathModel

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G] {x₁ x₂ lam tau : G}

private abbrev wmodDecEq : DecidableEq WMod := WMod.equivProd.decidableEq

attribute [local instance 2000] wmodDecEq

private abbrev m12DecEq : DecidableEq M12Mod := M12Mod.equivProd.decidableEq

attribute [local instance 2000] m12DecEq

private lemma wmod_involution_cases_aux :
    ∀ m : WMod, m * m = 1 → m ≠ 1 →
      m = WMod.wx₁ ^ 2 ∨ m = WMod.wx₂ ^ 2 ∨ m = (WMod.wx₁ * WMod.wx₂) ^ 2 ∨
        ∃ a : Fin 4, m = WMod.wx₁ ^ a.val * WMod.wx₂ ^ (4 - a.val) * WMod.wlam := by
  refine (WMod.forall_iff _).mpr ?_
  decide +kernel

private lemma m12_involution_j_one :
    ∀ (a b : Fin 4) (i j : Fin 2), (⟨a, b, i, j⟩ : M12Mod) * ⟨a, b, i, j⟩ = 1 →
      j = 1 → i = 0 ∨ (i = 1 ∧ a = b) := by
  decide +kernel

private lemma map_eq_pow (φ : M12Mod →* G) (hx₁ : φ M12Mod.mx₁ = x₁)
    (hx₂ : φ M12Mod.mx₂ = x₂) (hl : φ M12Mod.mlam = lam) (ht : φ M12Mod.mtau = tau)
    (m : M12Mod) :
    φ m = x₁ ^ m.a.val * x₂ ^ m.b.val * lam ^ m.i.val * tau ^ m.j.val := by
  simpa only [map_mul, map_pow, hx₁, hx₂, hl, ht] using congrArg φ (M12Mod.eq_pow_mul m)

theorem WreathRel.involution_cases (h : WreathRel x₁ x₂ lam) {g : G}
    (hg : g ∈ wreathGrp x₁ x₂ lam) (h2 : g * g = 1) (h1 : g ≠ 1) :
    g = x₁ ^ 2 ∨ g = x₂ ^ 2 ∨ g = (x₁ * x₂) ^ 2 ∨
      ∃ a : Fin 4, g = x₁ ^ a.val * x₂ ^ (4 - a.val) * lam := by
  obtain ⟨φ, hinj, hrange, hx₁, hx₂, hl⟩ := h.exists_embedding
  rw [← hrange] at hg
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hg
  have hm2 : m * m = 1 := by
    apply hinj
    rw [map_mul, map_one]
    exact h2
  have hm1 : m ≠ 1 := fun hm => h1 (by rw [hm, map_one])
  rcases wmod_involution_cases_aux m hm2 hm1 with hm | hm | hm | ⟨a, hm⟩
  · left
    rw [hm, map_pow, hx₁]
  · right; left
    rw [hm, map_pow, hx₂]
  · right; right; left
    rw [hm, map_pow, map_mul, hx₁, hx₂]
  · right; right; right
    refine ⟨a, ?_⟩
    rw [hm, map_mul, map_mul, map_pow, map_pow, hx₁, hx₂, hl]

theorem M12Rel.outer_involution_cases (h : M12Rel x₁ x₂ lam tau) {g : G}
    (hg : g ∈ m12Grp x₁ x₂ lam tau) (hgT : g ∉ wreathGrp x₁ x₂ lam) (h2 : g * g = 1) :
    (∃ a b : Fin 4, g = x₁ ^ a.val * x₂ ^ b.val * tau) ∨
      ∃ a : Fin 4, g = x₁ ^ a.val * x₂ ^ a.val * lam * tau := by
  obtain ⟨φ, hinj, hrange, hx₁, hx₂, hl, ht⟩ := h.exists_embedding
  rw [← hrange] at hg
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hg
  have hm2 : m * m = 1 := by
    apply hinj
    rw [map_mul, map_one]
    exact h2
  have hmj : m.j = 1 := by
    have hne : m.j ≠ 0 := by
      intro hj0
      apply hgT
      rw [map_eq_pow φ hx₁ hx₂ hl ht m, hj0]
      simp only [Fin.val_zero, pow_zero, mul_one]
      rw [wreathGrp]
      exact mul_mem
        (mul_mem (pow_mem (Subgroup.subset_closure (by simp)) m.a.val)
          (pow_mem (Subgroup.subset_closure (by simp)) m.b.val))
        (pow_mem (Subgroup.subset_closure (by simp)) m.i.val)
    exact (by decide +kernel : ∀ j : Fin 2, j ≠ 0 → j = 1) m.j hne
  have hcases : m.i = 0 ∨ (m.i = 1 ∧ m.a = m.b) :=
    m12_involution_j_one m.a m.b m.i m.j hm2 hmj
  rcases hcases with hi0 | ⟨hi1, hab⟩
  · left
    refine ⟨m.a, m.b, ?_⟩
    rw [map_eq_pow φ hx₁ hx₂ hl ht m, hi0, hmj]
    simp
  · right
    refine ⟨m.a, ?_⟩
    rw [map_eq_pow φ hx₁ hx₂ hl ht m, ← hab, hi1, hmj]
    simp

end CFSG.OddStandard.SmallF3.HarrisU33
