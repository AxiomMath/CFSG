module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossOrthBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthPlane

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Module
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem isLocallyBalancedAbs_two_projOrth (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hpl : p ≠ ringChar K)
    (hCL : CommonLayerCentralizerTrivial (ProjOrthDerived Q) p)
    {P : Type*} [Group P] (Ψ : ProjOrthDerived Q ≃* P)
    (hP : ∀ [Finite P], Function.Injective (MulAut.conj : P →* MulAut P) → OuterFields p P) :
    IsLocallyBalancedAbs p 2 (ProjOrthDerived Q) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  have hcenter : Subgroup.center (ProjOrthDerived Q) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (ProjOrthDerived Q)) with
      h | h
    · exact h
    · exfalso
      obtain ⟨c, d, hcd⟩ := hnonab
      exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)
  have hinj := conj_injective_of_center_eq_bot_orth hcenter
  have : Finite P := Finite.of_equiv _ Ψ.toEquiv
  refine isLocallyBalancedAbs_two_of_planes_and_fields hp hinj ?_
    ((hP (conj_injective_of_mulEquiv Ψ hinj)).of_mulEquiv Ψ)
  intro E hEin hE hEc H hH
  set E₁ : Subgroup (ProjOrthDerived Q) :=
    E.comap (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) with hE₁
  have hmap : E₁.map (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)) = E :=
    Subgroup.map_comap_eq_self hEin
  have hE₁el : IsElemAbelian p E₁ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · have h2 : MulAut.conj (a : ProjOrthDerived Q) * MulAut.conj (b : ProjOrthDerived Q) =
          MulAut.conj (b : ProjOrthDerived Q) * MulAut.conj (a : ProjOrthDerived Q) :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact h2
    · rw [map_pow, map_one]
      exact hE.2 _ hx
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hEc]
  have hbot := localDeltaIn_eq_bot_projOrth hQ hT hp (by omega) hpl hCL E₁ hE₁el hE₁c hH
  rwa [hmap] at hbot

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
