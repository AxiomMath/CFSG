module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutOuter
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.E0

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.Monster.B.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def fiJP :
    CFSG.Sporadic.Fi22.J ≃* fi22P :=
  CFSG.Sporadic.Fi22.fi22EquivJ.symm.trans fi22PermEquiv

@[expose] noncomputable def piP :
    ↥Cd →* fi22P :=
  (fiJP : CFSG.Sporadic.Fi22.J →* fi22P).comp piC

section


theorem piP_surjective : Function.Surjective piP :=
  fiJP.surjective.comp piC_surjective

theorem ker_piP : piP.ker = Subgroup.center ↥Cd := by
  rw [← ker_piC]
  ext c
  simp [piP]

theorem card_ker_piP : Nat.card piP.ker = 2 := by
  rw [ker_piP]
  exact card_center_C

end

theorem isPerfect_Cd :
    Group.IsPerfect ↥Cd := ⟨commutator_C⟩

@[expose] def CentralizerCore (V : Subgroup fi22P) : Prop :=
  ∀ r : fi22R, (∀ e ∈ V, (r : Equiv.Perm (Fin 3510)) * e = e * r) →
    ∃ x ∈ V, (x : Equiv.Perm (Fin 3510)) = r

@[expose] def OuterRankCore : Prop :=
  ∀ A : Subgroup (Equiv.Perm (Fin 3510)), A ≤ fi22R → (∀ a ∈ A, a ^ 2 = 1) → ¬ A ≤ fi22P →
    Nat.card A ≤ 2 ^ 8

theorem Cd_aut_cent_of_core
    (hC : CentralizerCore (E0.map piP)) :
    ∀ σ : MulAut ↥Cd, (∀ e ∈ E0, σ e = e) → ∃ x ∈ E0, σ = MulAut.conj x := by
  have := isPerfect_Cd
  obtain ⟨-, -, -, -, ⟨ψ, hψ, -⟩, -⟩ := CTUC_Fi22_full_automorphism_permutation_model
  exact AutQuot.aut_cent_of_quotient piP piP_surjective ker_piP E0
    (AutOuter.aut_cent_of_centralizer ψ hψ _ hC)

theorem Cd_rank_of_core
    (hR : OuterRankCore) :
    ∀ σ : MulAut ↥Cd, σ * σ = 1 → (∀ l : ↥Cd, σ ≠ MulAut.conj l) →
      ∀ B : Subgroup ↥Cd, (∀ b ∈ B, b ^ 2 = 1) → (∀ b ∈ B, σ b = b) → Nat.card B ≤ 2 ^ 8 := by
  have := isPerfect_Cd
  obtain ⟨-, -, -, -, ⟨ψ, hψ, hinn⟩, -⟩ := CTUC_Fi22_full_automorphism_permutation_model
  exact AutQuot.rank_of_quotient piP piP_surjective ker_piP card_ker_piP
    (AutOuter.rank_of_outer (n := 7) ψ hψ fi22P_le_R hinn hR)

end CFSG.EvenSporadicStandard.TwoFi22.DS81
