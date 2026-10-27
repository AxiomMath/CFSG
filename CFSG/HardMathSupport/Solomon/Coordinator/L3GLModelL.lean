module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaPSL
public import CFSG.HardMathSupport.Solomon.Coordinator.L3GLMatrix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts

variable {F : Type} [Field F] [Finite F]

local notation "S" => Matrix.GeneralLinearGroup.scalar (Fin 3)

theorem exists_heisenberg_pair_of_localDeltaIn_ne_bot {D H : Subgroup (MulAut (projectiveSL 3 F))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9) (hH : innerAut (projectiveSL 3 F) ≤ H)
    (hne : localDeltaIn 3 H D ≠ ⊥) :
    D ≤ linearAutGroup 3 F ∧ ∃ (A B : GL (Fin 3) F) (c : Fˣ), conjAut 3 F A ∈ D ∧
      conjAut 3 F B ∈ D ∧ c ≠ 1 ∧ A * B = B * A * S c := by
  by_cases hDl : D ≤ linearAutGroup 3 F
  swap
  · exact absurd (localDeltaIn_eq_bot_of_not_le_linearAutGroup_three hD hDl hH) hne
  refine ⟨hDl, ?_⟩
  by_cases hab : ∀ A ∈ D.comap (conjAut 3 F), ∀ B ∈ D.comap (conjAut 3 F), A * B = B * A
  · exfalso
    apply hne
    by_cases hF3 : 3 ∣ Nat.card F - 1
    · exact localDeltaIn_eq_bot_of_abelian_plane hD hcard hDl hF3 hab hH
    · exact localDeltaIn_eq_bot_of_not_dvd hD hcard hDl hF3 hH
  push Not at hab
  obtain ⟨A, hA, B, hB, hAB⟩ := hab
  have hA' : conjAut 3 F A ∈ D := hA
  have hB' : conjAut 3 F B ∈ D := hB
  have hcomm := comm_of_elemAbelian hD hA' hB'
  have h1 : conjAut 3 F (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨c, hc⟩ := (ProjectivePlane.conjAut_eq_one_iff (n := 3) le_rfl _).1 h1
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hAB
    rw [map_one] at hc
    calc A * B = (A * B * A⁻¹ * B⁻¹) * (B * A) := by group
      _ = B * A := by rw [hc, one_mul]
  refine ⟨A, B, c, hA', hB', hc1, ?_⟩
  calc A * B = (A * B * A⁻¹ * B⁻¹) * (B * A) := by group
    _ = S c * (B * A) := by rw [hc]
    _ = B * A * S c := Matrix.GeneralLinearGroup.scalar_commute c (B * A)

theorem l3gl_cube_of_localDeltaIn_ne_bot {D H : Subgroup (MulAut (projectiveSL 3 F))}
    (hD : IsElemAbelian 3 D) (hcard : Nat.card D = 9) (hH : innerAut (projectiveSL 3 F) ≤ H)
    (hne : localDeltaIn 3 H D ≠ ⊥) (s : Matrix.SpecialLinearGroup (Fin 3) F)
    (hs : ∀ d ∈ D, d * MulAut.conj (proj 3 F s) = MulAut.conj (proj 3 F s) * d) :
    (Matrix.SpecialLinearGroup.toGL s) ^ 3 = 1 := by
  obtain ⟨-, A, B, c, hA, hB, hc1, hAB⟩ :=
    exists_heisenberg_pair_of_localDeltaIn_ne_bot hD hcard hH hne
  set W : GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL s with hW
  have hconj : MulAut.conj (proj 3 F s) = conjAut 3 F W := conj_proj_eq_conjAut (n := 3) (K := F) s
  have key : ∀ X : GL (Fin 3) F, conjAut 3 F X ∈ D → ∃ d : Fˣ, W * X * W⁻¹ = X * S d := by
    intro X hX
    have h1 : conjAut 3 F (W * X * W⁻¹ * X⁻¹) = 1 := by
      have := hs _ hX
      rw [hconj] at this
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← this]
      group
    obtain ⟨d, hd⟩ := (ProjectivePlane.conjAut_eq_one_iff (n := 3) le_rfl _).1 h1
    refine ⟨d, ?_⟩
    calc W * X * W⁻¹ = (W * X * W⁻¹ * X⁻¹) * X := by group
      _ = S d * X := by rw [hd]
      _ = X * S d := Matrix.GeneralLinearGroup.scalar_commute d X
  obtain ⟨dA, hdA⟩ := key A hA
  obtain ⟨dB, hdB⟩ := key B hB
  exact l3gl_heis_cube hc1 hAB hdA hdB (by rw [hW]; exact s.2)

end CFSG.HardMathSupport.Solomon.Coordinator
