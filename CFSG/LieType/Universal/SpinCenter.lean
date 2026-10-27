module

public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LieType.Universal.Spin.Action
public import TauCeti.RepresentationTheory.Spin.Structure

public section

namespace CFSG.LieType.Universal.Spin

open Module CliffordAlgebra TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem finrank_cliffordAlgebra' [FiniteDimensional K V] (Q : QuadraticForm K V) :
    finrank K (CliffordAlgebra Q) = 2 ^ finrank K V := by
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (0 - Q)
  rw [(changeFormEquiv hB).finrank_eq]
  exact TauCeti.ExteriorAlgebra.finrank_eq_two_pow

theorem finiteDimensional_cliffordAlgebra' [FiniteDimensional K V] (Q : QuadraticForm K V) :
    FiniteDimensional K (CliffordAlgebra Q) := by
  obtain ⟨B, hB⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (0 - Q)
  exact LinearEquiv.finiteDimensional (changeFormEquiv hB).symm

section Generic

variable {Q : QuadraticForm K V}

theorem exists_eq_algebraMap_of_commute [Algebra.IsCentral K (CliffordAlgebra Q)]
    {x : CliffordAlgebra Q} (hx : ∀ v, Commute x (ι Q v)) :
    ∃ c : K, x = algebraMap K (CliffordAlgebra Q) c := by
  have hcen : x ∈ Subalgebra.center K (CliffordAlgebra Q) := by
    rw [Subalgebra.mem_center_iff]
    intro y
    induction y using CliffordAlgebra.induction with
    | algebraMap r => exact Algebra.commutes r x
    | ι v => exact (hx v).symm.eq
    | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  rw [Algebra.IsCentral.center_eq_bot] at hcen
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hcen
  exact ⟨c, hc.symm⟩

theorem eq_one_or_eq_neg_one_of_commute [Algebra.IsCentral K (CliffordAlgebra Q)]
    {x : spinGroup Q} (hx : ∀ v, Commute (x : CliffordAlgebra Q) (ι Q v)) :
    (x : CliffordAlgebra Q) = 1 ∨ (x : CliffordAlgebra Q) = -1 := by
  obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_commute hx
  have hstar : star (x : CliffordAlgebra Q) * x = 1 := spinGroup.star_mul_self_of_mem x.2
  rw [hc, star_algebraMap, ← map_mul] at hstar
  have hc2 : c * c = 1 := algebraMap_injective' Q (by rw [hstar, map_one])
  rcases mul_self_eq_one_iff.mp hc2 with rfl | rfl
  · left; rw [hc, map_one]
  · right; rw [hc, map_neg, map_one]

end Generic

variable {Q : QuadraticForm K V} (P : SpinPolarizationData Q) [FiniteDimensional K V]

theorem spinAction_injective' (h : Even (finrank K V)) :
    Function.Injective (TauCeti.spinAction Q P) := by
  obtain ⟨l, hl⟩ := h
  have hS : finrank K (ExteriorAlgebra K P.W) = 2 ^ l :=
    P.finrank_exteriorAlgebra_W_of_finrank_eq_two_mul (by omega)
  have := finiteDimensional_cliffordAlgebra' Q
  have hdim : finrank K (CliffordAlgebra Q) = finrank K (Module.End K (ExteriorAlgebra K P.W)) := by
    rw [Module.finrank_linearMap, finrank_cliffordAlgebra', hS, hl, pow_add]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (TauCeti.spinAction Q P).toLinearMap) hdim).2 (spinAction_surjective P)

noncomputable def cliffordEquivEnd' (h : Even (finrank K V)) :
    CliffordAlgebra Q ≃ₐ[K] Module.End K (ExteriorAlgebra K P.W) :=
  AlgEquiv.ofBijective (TauCeti.spinAction Q P) ⟨spinAction_injective' P h, spinAction_surjective P⟩

include P in
theorem isCentral_cliffordAlgebra' (h : Even (finrank K V)) :
    Algebra.IsCentral K (CliffordAlgebra Q) :=
  Algebra.IsCentral.of_algEquiv K _ _ (cliffordEquivEnd' P h).symm

variable (n : ℕ) (K)

noncomputable def quadPlusIsometry :
    (quadPlus n K).IsometryEquiv (splitEvenForm K n) where
  toFun v := (∑ i, v (.inl i) • LinearMap.proj i, fun i => v (.inr i))
  invFun x := Sum.elim (fun i => x.1 (Pi.single i 1)) x.2
  left_inv v := by
    funext j
    rcases j with i | i
    · simp [Pi.single_apply]
    · simp
  right_inv x := by
    obtain ⟨g, y⟩ := x
    refine Prod.ext (LinearMap.ext fun w => ?_) rfl
    simp only [Sum.elim_inl, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    rw [LinearMap.pi_apply_eq_sum_univ g w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, smul_eq_mul]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  map_add' v w := by
    ext <;> simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext <;> simp [mul_smul, Finset.smul_sum]
  map_app' v := by
    simp [quadPlus_apply]

theorem isCentral_cliffordAlgebra_quadPlus : Algebra.IsCentral K (CliffordAlgebra (quadPlus n K)) := by
  have : Algebra.IsCentral K (CliffordAlgebra (splitEvenForm K n)) :=
    isCentral_cliffordAlgebra' (splitEvenPolarization K n) (by
      rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Subspace.dual_finrank_eq,
        Module.finrank_fintype_fun_eq_card]
      exact ⟨_, rfl⟩)
  exact Algebra.IsCentral.of_algEquiv K _ _ (equivOfIsometry (quadPlusIsometry K n)).symm

end CFSG.LieType.Universal.Spin
