module

public import CFSG.ClassicalInvolution.Q3.Tight


public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

@[expose] def TightHasMember3Large : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R),
    (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) →
    ∀ t : G, t ∈ (S : Subgroup R).map R.subtype → orderOf t = 2 →
    R ≤ Subgroup.centralizer ({t} : Set G) →
    (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal →
    IsPGroup 2 (R ⧸ classicalInvolutionOddCore R) →
    ∃ (z : G) (J : Subgroup G), IsClassicalMember3 J z

theorem tightHasMember3Large_of_tightLift3 (h : TightLift3) : TightHasMember3Large := by
  intro G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
  obtain ⟨J, -, hJ⟩ := h G hnab hlarge R S hS t ht hto hRC hRn h2
  exact ⟨t, J, hJ⟩

theorem normalOddByQuaternionLarge_of_tightHasMember3Large (h : CIT3Inductive)
    (h0 : ModelClauseZero) (hM : M11Facts) (hlift : TightHasMember3Large) :
    NormalOddByQuaternionLarge := by
  intro G _ _ _ hFnonab R S hS t ht hto hRC hRn h2 hlarge
  obtain ⟨z, J, hJ⟩ := hlift G hFnonab hlarge R S hS t ht hto hRC hRn h2
  obtain ⟨hC, hO⟩ := centralizer_fstar_eq_bot_and_oddCore_eq_bot hFnonab
  have : (genFittingFStar G).Normal := genFittingFStar_normal G
  have := oddLieType_or_isSporadic_of_aschbacherCIT3 (aschbacherCIT3_of_cit3Inductive h h0 hM)
    (genFittingFStar G) hFnonab hC hO hJ.orderOf_eq_two hJ.mem hJ.subnormal hJ.isSolvable
    hJ.witness
  exact this.elim Or.inl fun h => Or.inr (Or.inl h)

end CFSG.ClassicalInvolution.Q3
