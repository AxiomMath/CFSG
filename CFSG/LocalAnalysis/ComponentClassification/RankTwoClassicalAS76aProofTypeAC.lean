module

public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSec72

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Subgroup CFSG.RankThree.OrthogonalInvolutions CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)
open scoped Matrix

theorem even_commRank_of_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [CharP K 2] (Q : QuadraticForm K (ι → K)) (hQ : Q.polarBilin.Nondegenerate) {M : GL ι K}
    (hM : M ∈ StatedOmega ⇑Q) : Even (commRank M) := by
  set φ : GL ι K ≃* ((ι → K) ≃ₗ[K] (ι → K)) := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (ι → K)) with hφdef
  have hφ : ∀ (N : GL ι K) v, φ N v = (N : Matrix ι ι K) *ᵥ v := fun _ _ => rfl
  have hC : closure {A : GL ι K | ∀ v, Q ((A : Matrix ι ι K) *ᵥ v) = Q v} ≤
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap φ.toMonoidHom := by
    rw [closure_le]
    intro A hA
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => by
      rw [MulEquiv.coe_toMonoidHom, hφ]
      exact hA v
  have hmem : φ M ∈ orthDerived Q := by
    have hmap : (StatedOmega ⇑Q).map φ.toMonoidHom ≤ orthDerived Q := by
      rw [StatedOmega, Subgroup.map_commutator]
      exact commutator_mono (map_le_iff_le_comap.mpr hC) (map_le_iff_le_comap.mpr hC)
    exact hmap ⟨M, hM, rfl⟩
  have hev := (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ hmem).2
  have hrange : commSpace (φ M) = LinearMap.range ((M : Matrix ι ι K) - 1).mulVecLin := by
    ext v
    simp [hφ]
  rw [commRank, Matrix.rank, ← hrange]
  exact hev

theorem orthTypeAC :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A),
      (D.family = .orthPlus ∨ D.family = .orthMinus) → ∀ (p : G) (ℓ : ℕ), ¬ D.SuzukiType p .b ℓ := by
  intro G _ _ A D hD p ℓ h
  cases D with
  | linear => exact h.elim
  | unitary => exact h.elim
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, ⟨-, hMH, -⟩, -, hr, hodd⟩ := h
    have hev := even_commRank_of_mem_statedOmega (CFSG.LieType.Universal.Spin.quadPlus n K)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K)
      (by rw [CFSG.LieType.Universal.Spin.coe_quadPlus]; exact hMH)
    rw [hr] at hev
    exact Nat.not_even_iff_odd.mpr hodd hev
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, ⟨-, hMH, -⟩, -, hr, hodd⟩ := h
    have hev := even_commRank_of_mem_statedOmega (CFSG.LieType.Universal.Spin.quadMinus n K b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (by rw [CFSG.LieType.Universal.Spin.coe_quadMinus]; exact hMH)
    rw [hr] at hev
    exact Nat.not_even_iff_odd.mpr hodd hev

end CFSG.ComponentClassification.RankTwoClassical
