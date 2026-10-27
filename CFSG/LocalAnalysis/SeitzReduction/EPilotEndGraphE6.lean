module

public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTransfer

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LieType.Chevalley.E6GraphFullCoset (IsOrdinaryDiagGraph)

theorem exists_E6_graphCoordinate (K : Type) [Field K] [Finite K] :
    ∃ χ : MulAut (adjointGroup Tag.E6 K) →* Multiplicative (ZMod 2),
      (∀ x : adjointGroup Tag.E6 K, χ (MulAut.conj x) = 1) ∧
      ∀ (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) (σ : K ≃+* K) {ε : ℕ}, ε < 2 →
        χ (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) =
          Multiplicative.ofAdd (ε : ZMod 2) := by
  obtain ⟨Θ, -, hΘ, hker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  refine ⟨(MonoidHom.snd _ _).comp Θ, fun x => ?_, fun g a σ ε hε => ?_⟩
  · have h : Θ (MulAut.conj x) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      refine ⟨x, 1, fun h => ?_⟩
      rw [rootDiagUnit_one, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, inv_one, mul_one, mul_one]
    show (Θ (MulAut.conj x)).2 = 1
    rw [h]
    rfl
  · have h := hΘ (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) g a σ ⟨ε, hε⟩ fun h => by
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, coe_exactNormalAut]
      simp only [mul_assoc]
    show (Θ (MulAut.conj g * exactNormalAut Tag.E6 K a σ ε)).2 = _
    rw [h]
    rfl

variable {G : Type*} [Group G] [Finite G] {G₀ : Subgroup G}

end CFSG.SeitzReduction.EPilot
