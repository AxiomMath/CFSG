module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FT1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FYP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B P : Subgroup G}
  {x : G} {φ : (Fin 7 → ZMod 2) → G}

@[expose] def sec4FX (t : G) (φ : (Fin 7 → ZMod 2) → G) (x : G) : Set G :=
  Set.range (sec4MPt t φ) ∪ Set.range (sec4FD t φ x)

theorem Sec4FSetup.T1_invariant (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {g : G}
    (hg : g ∈ P ⊔ zpowers x) {e : G} (he : e ∈ sec4FX t φ x) : g * e * g⁻¹ ∈ sec4FX t φ x := by
  rw [sec4FX] at he ⊢
  rcases sec4F_T1_cases hT.xP hT.x2 hg with hgP | ⟨p, hp, rfl⟩
  · rcases he with ⟨a, rfl⟩ | ⟨c, rfl⟩
    · obtain ⟨σ, hσ⟩ := h.exists_realizes (hT.PM hgP)
      exact Or.inl ⟨σ a, (hσ a).symm⟩
    · have hg'P : x * g * x⁻¹ ∈ P :=
        (Subgroup.mem_set_normalizer_iff.mp hT.xP g).mp hgP
      obtain ⟨σ, hσ⟩ := h.exists_realizes (hT.PM hg'P)
      have hconj : g * (x⁻¹ * sec4MPt t φ c * x) * g⁻¹
          = x⁻¹ * sec4MPt t φ (σ c) * x := by
        rw [← hσ c]
        group
      exact Or.inr ⟨σ c, by rw [sec4FD]; exact hconj.symm⟩
  · rcases he with ⟨a, rfl⟩ | ⟨c, rfl⟩
    · obtain ⟨e', he'⟩ := h.K_to_d hT hp a
      exact Or.inr ⟨e', he'.symm⟩
    · obtain ⟨q, hq⟩ := h.K_to_pt hT hp c
      exact Or.inl ⟨q, hq.symm⟩

theorem Sec4FSetup.T1_conj_X (h : Sec4FSetup t L S z A B φ) (hT : Sec4FTwo A P x) {y : G}
    (hy : ∃ k : G, y = k⁻¹ * t * k) (hyT : y ∈ P ⊔ zpowers x) : y ∈ sec4FX t φ x := by
  rw [sec4FX]
  have hyP : y ∈ P := h.T1_conj_mem hT hy hyT
  by_cases hyA : y ∈ A
  · obtain ⟨a, ha⟩ := h.exists_pt_of_conj hy hyA
    exact Or.inl ⟨a, ha.symm⟩
  · obtain ⟨c, hc⟩ := h.YP hT hy hyP hyA
    exact Or.inr ⟨c, hc.symm⟩

end CFSG.OddStandard.SmallF3.Omega
