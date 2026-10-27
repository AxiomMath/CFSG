module

public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] (K : Subgroup L) {k : ℕ}

theorem pow_mem_iff_of_coprime_natCard (hk : (Nat.card L).Coprime k) (z : L) :
    z ^ k ∈ K ↔ z ∈ K := by
  refine ⟨fun h => ?_, fun h => K.pow_mem h k⟩
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard z) hk.symm)
  exact hm ▸ K.pow_mem h m

private theorem dite_pow_mem_eq (hk : (Nat.card L).Coprime k) (θ : K → ℂ) (z : L)
    [Decidable (z ∈ K)] [Decidable (z ^ k ∈ K)] :
    (if h : z ^ k ∈ K then θ ⟨z ^ k, h⟩ else 0) =
      if h : z ∈ K then powOp k θ ⟨z, h⟩ else 0 := by
  by_cases hz : z ∈ K
  · rw [dif_pos hz, dif_pos (K.pow_mem hz k), powOp_apply]
    exact congrArg θ (Subtype.ext (SubmonoidClass.coe_pow ⟨z, hz⟩ k).symm)
  · rw [dif_neg hz, dif_neg fun h => hz ((pow_mem_iff_of_coprime_natCard K hk z).1 h)]

variable [Fintype L]

theorem powOp_indClassFun (hk : (Nat.card L).Coprime k) (θ : K → ℂ) :
    powOp k (indClassFun K θ) = indClassFun K (powOp k θ) := by
  classical
  funext g
  rw [powOp_apply, indClassFun_apply, indClassFun_apply]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have hconj : t⁻¹ * g ^ k * t = (t⁻¹ * g * t) ^ k := by
    have h := conj_pow (i := k) (a := t⁻¹) (b := g)
    rw [inv_inv] at h
    exact h.symm
  rw [hconj]
  exact dite_pow_mem_eq K hk θ _

theorem indClassFun_pow (hk : (Nat.card L).Coprime k) (θ : K → ℂ) (g : L) :
    indClassFun K θ (g ^ k) = indClassFun K (powOp k θ) g := by
  rw [← powOp_apply k (indClassFun K θ) g, powOp_indClassFun K hk θ]

theorem isClassFun_indClassFun (θ : K → ℂ) : IsClassFun (indClassFun K θ) :=
  isClassFun_iff.2 (indClassFun_conj K θ)

theorem indClassFun_mem_classFunctions (θ : K → ℂ) :
    indClassFun K θ ∈ classFunctions ℂ ℂ L :=
  mem_classFunctions.2 (isClassFun_indClassFun K θ)

theorem coe_powOpₗ_indClassFun (hk : (Nat.card L).Coprime k) (θ : K → ℂ) :
    (powOpₗ ℂ ℂ L k ⟨indClassFun K θ, indClassFun_mem_classFunctions K θ⟩ : L → ℂ) =
      indClassFun K (powOp k θ) := by
  rw [coe_powOpₗ_apply, powOp_indClassFun K hk θ]

end CFSG.FeitThompson
