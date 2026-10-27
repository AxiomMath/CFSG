module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable def statedSLEquivProjectiveSL (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSL n K) ≃* projectiveSL n K :=
  (projectiveSpecialLinearGroupEquivStatedProj n K).symm.trans
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)

theorem even_rank_two_residual_linear {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : StatedClassicalModel X .PSL 3 2 f) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (φ : X ≃* projectiveSL 3 K),
      Nat.card K = 2 ^ f ∧ U.map φ.toMonoidHom = projUnitriangular 3 K ∧
      ResidualOvergroupsAt X U (fun j : Fin 2 =>
        (projStabilizer (flagSpace 3 K ((j : ℕ) + 1))).map φ.symm.toMonoidHom) ∧
      ∀ j : Fin 2, ((H3 K j).subgroupOf (Q3 K j)).Normal ∧ ⁅Q3 K j, Q3 K j⁆ ≤ H3 K j ∧
        ∀ A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K), unitriangular 3 K ≤ A →
          A ≤ Q3 K j → ¬ Group.IsSolvable A → H3 K j ≤ A := by
  obtain ⟨⟨-, hf, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hcard⟩
  have hB := isSolvable_upperTriangular (n := 3) (K := K) hK
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  obtain ⟨φ, hφ, hP'⟩ := (linear_three_residualOvergroupsAt hK).exists_iso_of_isSylow
    (e.trans (statedSLEquivProjectiveSL 3 K)) hU₀ hU
  exact ⟨K, hF, hFin, inferInstance, φ, hcard, hφ, hP', fun j =>
    ⟨H3_normal_in_Q3 j, commutator_Q3_le j,
      fun A hVA hAQ hAns => H3_le_of_nonsolvable hB j hVA hAQ hAns⟩⟩

theorem even_rank_two_residual_symplectic {X : Type} [Group X] [Finite X] {f : ℕ}
    (hX : StatedClassicalModel X .PSp 2 2 f) {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (φ : X ≃* StatedProj (StatedSp 2 K)),
      Nat.card K = 2 ^ f ∧ U.map φ.toMonoidHom = SymplecticFlag.projUnipotent 2 K ∧
      ResidualOvergroupsAt X U (fun j : Fin 2 =>
        (SymplecticHigher.projStabilizer 2 K (SymplecticFlag.flag 2 K ((j : ℕ) + 1))).map φ.symm.toMonoidHom) ∧
      ∀ j : Fin 2, ((H2 K j).subgroupOf (Q2 K j)).Normal ∧ ⁅Q2 K j, Q2 K j⁆ ≤ H2 K j ∧
        ∀ A : Subgroup (StatedSp 2 K), SymplecticFlag.unipotent 2 K ≤ A → A ≤ Q2 K j → ¬ Group.IsSolvable A →
          H2 K j ≤ A := by
  obtain ⟨⟨-, hf, -⟩, K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  have hK : ∃ k : ℕ, Nat.card K = 2 ^ k := ⟨f, hcard⟩
  have hB := isSolvable_borelSubgroup (r := 2) (K := K) hK
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_projUnipotent
    (K := K) 2 (r := 2) (by norm_num)
  have hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf (SymplecticFlag.projUnipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  obtain ⟨φ, hφ, hP'⟩ := (symplectic_two_residualOvergroupsAt hK).exists_iso_of_isSylow e hU₀ hU
  exact ⟨K, hF, hFin, inferInstance, φ, hcard, hφ, hP', fun j =>
    ⟨H2_normal_in_Q2 j, commutator_Q2_le j,
      fun A hVA hAQ hAns => H2_le_of_nonsolvable hB j hVA hAQ hAns⟩⟩

theorem even_rank_two_classical_proper_Sylow_overgroup_residual
    {X : Type} [Group X] [Finite X] {U : Subgroup X}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hX : (∃ f : ℕ, StatedClassicalModel X .PSL 3 2 f) ∨
      (∃ f : ℕ, StatedClassicalModel X .PSp 2 2 f)) :
    ResidualOvergroups X U := by
  rcases hX with ⟨f, hX⟩ | ⟨f, hX⟩
  · obtain ⟨_, _, _, _, _, _, _, hP, _⟩ := even_rank_two_residual_linear hX hU
    exact ⟨_, hP⟩
  · obtain ⟨_, _, _, _, _, _, _, hP, _⟩ := even_rank_two_residual_symplectic hX hU
    exact ⟨_, hP⟩

end CFSG.QuasithinUnique.Setup.X7a
