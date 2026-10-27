module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def rationalCommutant (T : Module.End K V) : Subalgebra K (Module.End K V) :=
  Subalgebra.centralizer K ({T} : Set (Module.End K V))

theorem mem_rationalCommutant_iff (T S : Module.End K V) :
    S ∈ rationalCommutant T ↔ T * S = S * T := by
  simp only [rationalCommutant, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq]

theorem irreducible_commuting_map_injective (T S : Module.End K V)
    (hirr : ∀ U : Submodule K V, (∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hS : S ∈ rationalCommutant T) (hSne : S ≠ 0) :
    Function.Injective S := by
  have hcomm : T * S = S * T := (mem_rationalCommutant_iff T S).mp hS
  have hkerinv : ∀ v ∈ S.ker, T v ∈ S.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have h := congrArg (fun f : Module.End K V => f v) hcomm
    simpa only [Module.End.mul_apply, hv, map_zero] using h.symm
  apply LinearMap.ker_eq_bot.mp
  rcases hirr S.ker hkerinv with hbot | htop
  · exact hbot
  · exact False.elim (hSne (LinearMap.ker_eq_top.mp htop))

theorem rationalCommutant_evaluation_injective (T : Module.End K V)
    (hirr : ∀ U : Submodule K V, (∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = ⊤)
    (v : V) (hv : v ≠ 0) :
    Function.Injective (fun S : rationalCommutant T => (S : Module.End K V) v) := by
  intro S R heq
  apply Subtype.ext
  by_contra hne
  have hSR : (S : Module.End K V) - R ≠ 0 := sub_ne_zero.mpr hne
  have hinj := irreducible_commuting_map_injective T (S - R)
    hirr ((rationalCommutant T).sub_mem S.property R.property) hSR
  have hz : ((S : Module.End K V) - R) v =
      ((S : Module.End K V) - R) 0 := by simp only [LinearMap.sub_apply, heq, sub_self, map_zero]
  exact hv (hinj hz)

theorem rationalCommutant_isField [Finite K] [FiniteDimensional K V] [Nontrivial V]
    (T : Module.End K V)
    (hirr : ∀ U : Submodule K V, (∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = ⊤) :
    IsField (rationalCommutant T) := by
  classical
  let : Finite V := Module.finite_of_finite K
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let : Finite (rationalCommutant T) := Finite.of_injective
    (fun S : rationalCommutant T => (S : Module.End K V) v)
    (rationalCommutant_evaluation_injective T hirr v hv)
  let : Nontrivial (rationalCommutant T) :=
    nontrivial_of_ne (0 : rationalCommutant T) 1
      (fun h => zero_ne_one (congrArg Subtype.val h))
  let : NoZeroDivisors (rationalCommutant T) :=
    { eq_zero_or_eq_zero_of_mul_eq_zero := by
        intro S R hSR
        by_cases hS : S = 0
        · exact Or.inl hS
        · right
          apply Subtype.ext
          apply LinearMap.ext
          intro w
          have hSne : (S : Module.End K V) ≠ 0 := fun h => hS (Subtype.ext h)
          have hinj := irreducible_commuting_map_injective T S hirr S.property hSne
          apply hinj
          have h := congrArg (fun Q : rationalCommutant T => (Q : Module.End K V) w) hSR
          simpa only [Subalgebra.coe_mul, Module.End.mul_apply, ZeroMemClass.coe_zero,
            LinearMap.zero_apply, map_zero] using h }
  let : IsDomain (rationalCommutant T) := NoZeroDivisors.to_isDomain _
  exact Finite.isDomain_to_isField _

theorem rationalCommutant_finrank_le [FiniteDimensional K V]
    (T : Module.End K V)
    (hirr : ∀ U : Submodule K V, (∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = ⊤)
    (v : V) (hv : v ≠ 0) :
    Module.finrank K (rationalCommutant T) ≤ Module.finrank K V := by
  let ev : rationalCommutant T →ₗ[K] V :=
    { toFun S := (S : Module.End K V) v
      map_add' S R := rfl
      map_smul' a S := rfl }
  exact LinearMap.finrank_le_finrank_of_injective (f := ev)
    (rationalCommutant_evaluation_injective T hirr v hv : Function.Injective ev)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
