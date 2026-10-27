module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2GlobalMismatch
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainSylow

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Steinberg

theorem map_conj_eq_self_of_le_centralizer {M : Type*} [Group M] {U : Subgroup M} {c : M}
    (hc : c ∈ centralizer (U : Set M)) : U.map (MulAut.conj c).toMonoidHom = U := by
  have hfix : ∀ y ∈ U, (MulAut.conj c).toMonoidHom y = y := by
    intro y hy
    have h := (mem_centralizer_iff.1 hc) y hy
    change c * y * c⁻¹ = y
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hfix y hy]
    exact hy
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

theorem psiF4_v0110 : psiF4 v0110 = v0120 := by
  decide +kernel

section Roots

theorem isRoot_v0110 : IsRoot .F4 v0110 :=
  mem_rootFinset.1 (by decide +kernel)

theorem v0120_mem_b2LeviRoots : v0120 ∈ b2LeviRoots :=
  mem_b2LeviRoots.2 ⟨mem_rootFinset.1 (by decide +kernel), rfl, rfl⟩

end Roots

section Model

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem exists_overlapInv_model (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) :
    ∃ m : adjointGroup .F4 K,
      (X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom =
          (X₀ ⊔ stdX K).map (MulAut.conj m).toMonoidHom ∧
        ((Adjoint.f4Datum K).rootGroup v0110).map (graphAutF4 K).toMonoidHom =
          ((Adjoint.f4Datum K).rootGroup v0120).map (MulAut.conj m).toMonoidHom := by
  obtain ⟨c, hcB, hc⟩ := exists_conj_std hK hXJ hcyc hX₀
  refine ⟨c⁻¹, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have h1 : c * x * c⁻¹ ∈ X₀ ⊔ stdX K := by
        rw [← hc]
        exact ⟨x, hx, rfl⟩
      refine ⟨c * x * c⁻¹, h1, ?_⟩
      change c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x
      group
    · rintro ⟨y, hy, rfl⟩
      rw [← hc] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      change c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ ∈ _
      have : c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ = z := by group
      rw [this]
      exact hz
  · rw [map_graphAutF4_rootGroup isRoot_v0110, psiF4_v0110]
    have hc' : c⁻¹ ∈ centralizer (((Adjoint.f4Datum K).rootGroup v0120 :
        Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) :=
      centralizer_le (rootGroup_le_B2Levi v0120_mem_b2LeviRoots)
        (inv_mem (B12_le_centralizer_B2Levi hcB))
    exact (map_conj_eq_self_of_le_centralizer hc').symm

end Model

@[expose] def TwoOverlapInvKindInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
    ∀ X₀ : Subgroup (adjointGroup .F4 K),
      X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K) → IsCyclic X₀ →
      Nat.card X₀ = 3 →
      ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (e : L ≃* adjointGroup .F4 K) (t : G),
        F4Work L K t 1 → ∀ κ : Sp6Kind, TwoKindAt e t X₀ κ →
          Nat.card (centralizerPerfectCore (subgroupToG e (X₀ ⊔ stdX K))) =
              twoDiagPieceOrder κ ∧
            (κ.IsGraphKind →
              coreCentCard e (X₀ ⊔ stdX K) ((Adjoint.f4Datum K).rootGroup v0120) =
                twoOverlapInvOrderL κ ∧
              coreCentCard e (X₀ ⊔ stdX K) ((Adjoint.f4Datum K).rootGroup v0110) =
                twoOverlapInvOrderS κ)

theorem twoOverlapInvInput_of_kindInput (h : TwoOverlapInvKindInput) : TwoOverlapInvInput := by
  intro K _ _ _ hK X₀ hXJ hcyc hX₀
  obtain ⟨m, hT, hU⟩ := exists_overlapInv_model hK hXJ hcyc hX₀
  exact ⟨X₀ ⊔ stdX K, (Adjoint.f4Datum K).rootGroup v0120, (Adjoint.f4Datum K).rootGroup v0110,
    m, hT, hU, h K hK X₀ hXJ hcyc hX₀⟩

theorem twoRowsCatInput_of_overlapInvKindInput (h : TwoOverlapInvKindInput)
    (hF : TwoFieldPairInput) (hS : TwoSwapPairInput) (hE : TwoE6PairInput)
    (hT : TwoTwistedE6PairInput) : TwoRowsCatInput :=
  twoRowsCatInput_of_overlapInvInput (twoOverlapInvInput_of_kindInput h) hF hS hE hT

end CFSG.SeitzReduction.F4Pilot
