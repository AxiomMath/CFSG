module

public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem isSylow2Of_iff_ci [Finite G] {P A : Subgroup G} :
    IsSylow2Of P A ↔ CFSG.ClassicalInvolution.IsSylow2Of P A := by
  constructor
  · intro h
    obtain ⟨T, rfl⟩ := IsSylow2Of.exists_sylow h
    exact CFSG.ClassicalInvolution.isSylow2Of_map_subtype T
  · intro h
    obtain ⟨T, rfl⟩ := CFSG.ClassicalInvolution.IsSylow2Of.exists_sylow h
    exact isSylow2Of_map_sylow T

theorem exists_isSylow2Of_ge [Finite G] {P H : Subgroup G} (hP : IsPGroup 2 P) (hPH : P ≤ H) :
    ∃ Q : Subgroup G, IsSylow2Of Q H ∧ P ≤ Q := by
  obtain ⟨Q, hQ, hle⟩ := CFSG.ClassicalInvolution.exists_isSylow2Of_ge hP hPH
  exact ⟨Q, isSylow2Of_iff_ci.2 hQ, hle⟩

theorem exists_isSylow2Of [Finite G] (H : Subgroup G) : ∃ Q : Subgroup G, IsSylow2Of Q H := by
  obtain ⟨Q, hQ, -⟩ := exists_isSylow2Of_ge (IsPGroup.of_bot (G := G) (p := 2)) (bot_le : ⊥ ≤ H)
  exact ⟨Q, hQ⟩

theorem IsSylow2Of.eq_of_le [Finite G] {P Q H : Subgroup G} (hP : IsSylow2Of P H)
    (hQ : Q ≤ H) (hQ2 : IsPGroup 2 Q) (hle : P ≤ Q) : Q = P :=
  (isSylow2Of_iff_ci.1 hP).2.2 Q hQ hQ2 hle

theorem IsSylow2Of.exists_conj_mem [Finite G] {P Q H : Subgroup G} (hP : IsSylow2Of P H)
    (hQ : IsSylow2Of Q H) : ∃ a ∈ H, ∀ x : G, x ∈ Q ↔ a⁻¹ * x * a ∈ P := by
  obtain ⟨a, ha, hQP⟩ :=
    CFSG.ClassicalInvolution.IsSylow2Of.exists_conj (isSylow2Of_iff_ci.1 hP)
      (isSylow2Of_iff_ci.1 hQ)
  exact ⟨a, ha, fun x => by rw [hQP]; exact CFSG.ClassicalInvolution.mem_conjSubgroup_iff⟩

theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

end CFSG.OddStandard.SmallF3.Omega
