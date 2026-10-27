module

public import CFSG.LieType.SeitzGeneration.InnerOrthogonal
public import CFSG.RankThree.PartOne.CTP.SeitzLift
public import CFSG.RankThree.PartOne.CTP.SeitzOrthKernel

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def OrthPlaneGen {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p : ℕ) : Prop :=
  ∀ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) →
    Nat.card E = p ^ 2 →
      Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤

@[expose] def OrthMaster : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) → 7 ≤ finrank K V →
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ ringChar K → OrthPlaneGen Q p

section Lift

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem closure_centralizers_statedProj_of_gen (hQ : ⇑Q = Q₀)
    (hE : orthDerived Q = elementaryGroup Q) (hnd : (polarBilin Q).Nondegenerate)
    [Nontrivial (ι → K)] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hgen : OrthPlaneGen Q p)
    (E : Subgroup (StatedProj (StatedOmega Q₀)))
    (hEab : CFSG.Open.IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega Q₀) | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ι → K) := inferInstance
  have : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun g => (g : (ι → K) → (ι → K))) DFunLike.coe_injective
  let ψ : StatedOmega Q₀ ≃* orthDerived Q :=
    (statedOmegaEquiv hQ hE).trans (MulEquiv.subgroupCongr hE).symm
  have hψ : ∀ y : StatedOmega Q₀,
      ((ψ y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) =
        toLinEquiv ι K (y : GL ι K) := fun y => rfl
  let π : orthDerived Q →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))).comp
      ψ.symm.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp ψ.symm.surjective
  have hker : π.ker = (scalars K (ι → K)).subgroupOf (orthDerived Q) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk (ψ.symm x) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    have := hψ (ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    have h := (scalarKernel_data hnd hp hp2).2
    rw [QuotientGroup.ker_mk'] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h.symm
  have : IsMulCommutative E := hEab.1
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  exact closure_centralizers_of_lift π hπ hker' E hcomm hEab.2 fun E' hc he hcd _ =>
    hgen E' hc he (hcd.trans hcard)

end Lift

theorem ne_ringChar_of_not_dvd_card {K : Type} [Field K] [Finite K] {p : ℕ}
    (h : ¬ p ∣ Nat.card K) : p ≠ ringChar K := by
  rintro rfl
  apply h
  have := Fintype.ofFinite K
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self _ n.pos.ne'

theorem orthogonalOddPlanes_of_master (hM : OrthMaster) : OrthogonalOddPlanes := by
  intro r p K _ _ hr hp hp5 hpK h2 E hE hcard
  have hreg := regular_quadOdd (K := K) h2 hr
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r ⊕ Unit → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_gen (coe_quadOdd r K)
    (commutator_orthogonalGroup_quadOdd h2 hr) hreg.1 hp (by omega)
    (hM K _ (quadOdd r K) hreg.1 hreg.2 hdim p hp hp5 (ne_ringChar_of_not_dvd_card hpK)) E hE hcard

theorem orthogonalPlusPlanes_of_master (hM : OrthMaster) : OrthogonalPlusPlanes := by
  intro r p K _ _ hr hp hp5 hpK E hE hcard
  have hreg := regular_quadPlus (K := K) (n := r) (by omega)
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_gen (coe_quadPlus r K)
    (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1 hp (by omega)
    (hM K _ (quadPlus r K) hreg.1 hreg.2 hdim p hp hp5 (ne_ringChar_of_not_dvd_card hpK)) E hE hcard

theorem orthogonalMinusPlanes_of_master (hM : OrthMaster) : OrthogonalMinusPlanes := by
  intro r p K _ _ b c hr hirr hp hp5 hpK E hE hcard
  have hreg := regular_quadMinus (K := K) (n := r) hr hirr
  have : Nonempty (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hdim : 7 ≤ finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_gen (coe_quadMinus r K b c)
    (commutator_orthogonalGroup_quadMinus hr hirr) hreg.1 hp (by omega)
    (hM K _ (quadMinus r K b c) hreg.1 hreg.2 hdim p hp hp5 (ne_ringChar_of_not_dvd_card hpK))
    E hE hcard

end CFSG.LieType.SeitzGeneration
