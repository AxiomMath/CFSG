module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjoint

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData

variable {τ : Tag} {D : MinData τ} (R : Type*) [CommRing R]

theorem yOp_hVec' (i j : Fin τ.rank) (c : R) :
    yOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1) := by
  change yOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

theorem yOp_rootVec_neg_single' (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (-Pi.single i 1)) = rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_eq_single R (isRoot_neg_single τ i), yOp, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

theorem yOp_rootVec_single' (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (Pi.single i 1)) =
      rootVec τ R (Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_eq_single R (IsRoot.basis i), yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

theorem yOp_rootVec_of_ne' (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringDown τ i α + 1),
        (((stringUp τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α - (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_eq_single R hα, yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₂).trans (ite_eq_right h₁)

variable (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef)

include hpd in
theorem string_of_sub
    {α : Fin τ.rank → ℤ} {i : Fin τ.rank} (hα : IsRoot τ α)
    (hr : IsRoot τ (α - Pi.single i 1)) :
    toWeight (α - Pi.single i 1) i = -1 ∧ ¬ IsRoot τ (α + Pi.single i 1) ∧
      ¬ IsRoot τ (α - Pi.single i 1 - Pi.single i 1) := by
  have h := string_of_add hpd hr (i := i) (by rwa [sub_add_cancel])
  refine ⟨h.1, fun h' => h.2.2 ?_, h.2.1⟩
  convert h' using 1
  rw [two_smul]
  abel

include hpd in
theorem yOp_rootVec_of_sub
    (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) (hr : IsRoot τ (α - Pi.single i 1)) :
    yOp τ R i c (rootVec τ R α) = rootVec τ R α + c • rootVec τ R (α - Pi.single i 1) := by
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  obtain ⟨-, hup, hdown⟩ := string_of_sub hpd hα hr
  have e1 : α + (-1 : ℤ) • Pi.single i 1 = α - Pi.single i 1 := by rw [neg_smul, one_smul]; abel
  have e2 : α + (-2 : ℤ) • Pi.single i 1 = α - Pi.single i 1 - Pi.single i 1 := by
    rw [neg_smul, two_smul]
    abel
  have h1 := (hint (-1)).1 (by rwa [e1])
  have hp : stringUp τ i α = 0 := by
    by_contra h
    exact hup (by simpa using (hint 1).2 ⟨by omega, by omega⟩)
  have hq : stringDown τ i α = 1 := by
    have := h1.1
    by_contra h
    exact hdown (by rw [← e2]; exact (hint (-2)).2 ⟨by omega, by omega⟩)
  rw [yOp_rootVec_of_ne' R i c hα h₁ h₂, hp, hq, Finset.sum_range_succ, Finset.sum_range_one]
  simp

theorem yOp_rootVec_of_not_sub
    (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1)
    (hr : ¬ IsRoot τ (α - Pi.single i 1)) : yOp τ R i c (rootVec τ R α) = rootVec τ R α := by
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have hq : stringDown τ i α = 0 := by
    by_contra h
    refine hr ?_
    have := (hint (-1)).2 ⟨by omega, by omega⟩
    rwa [neg_smul, one_smul, ← sub_eq_add_neg] at this
  rw [yOp_rootVec_of_ne' R i c hα h₁ h₂, hq, Finset.sum_range_one]
  simp

theorem comm_eq_of_jacobi {M : Type*} [AddCommGroup M] [Module R M]
    (E F H X Y : Module.End R M) (c : R) (hc : c * c = 1) (hFX : F * X = X * F)
    (hEF : E * F - F * E = H) (hHX : H * X - X * H = -X) (hEX : E * X - X * E = c • Y) :
    F * Y - Y * F = c • X := by
  have hY : Y = c • (E * X - X * E) := by rw [hEX, smul_smul, hc, one_smul]
  have key : F * (E * X - X * E) - (E * X - X * E) * F +
      ((E * F - F * E) * X - X * (E * F - F * E)) =
        (X * F - F * X) * E + E * (F * X - X * F) := by noncomm_ring
  rw [hFX, sub_self, zero_mul, mul_zero, add_zero, hEF, hHX] at key
  rw [hY, mul_smul_comm, smul_mul_assoc, ← smul_sub, eq_neg_of_add_eq_zero_left key, neg_neg]

variable {S : AdjSigns τ} (hV : D.Valid) (hS : S.check D = true)

include hpd hV hS in
theorem rootOp_neg_single_comm
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (i : Fin τ.rank)
    (hr : IsRoot τ (α - Pi.single i 1)) :
    D.rootOp R (-Pi.single i 1) * D.rootOp R α - D.rootOp R α * D.rootOp R (-Pi.single i 1) =
      ((S.sRoot (α - Pi.single i 1) * S.sRoot α : ℤ) : R) • D.rootOp R (α - Pi.single i 1) := by
  obtain ⟨hw, -, hdown⟩ := string_of_sub hpd hα hr
  have hsum : Pi.single i 1 + (α - Pi.single i 1) = α := by abel
  have hEβ := AdjSigns.rootOp_single_comm hS hV R hr i (by rwa [hsum])
  rw [hsum] at hEβ
  have hne : -Pi.single i 1 + (α - Pi.single i 1) ≠ 0 := by
    intro h
    rw [← neg_add_eq_zero.1 h, toWeight_single, τ.cartan_self] at hw
    norm_num at hw
  have hFβ := (hV.pairRel (R := R) (isRoot_neg_single τ i) hr hne).2 (by
    rwa [show -Pi.single i 1 + (α - Pi.single i 1) = α - Pi.single i 1 - Pi.single i 1 by abel])
  have hH := cartanOp_comm_rootOp hV R hr i
  rw [hw, Int.cast_neg, Int.cast_one, neg_one_smul] at hH
  have hc : ((S.sRoot α * S.sRoot (α - Pi.single i 1) : ℤ) : R) *
      ((S.sRoot α * S.sRoot (α - Pi.single i 1) : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, mul_mul_mul_comm, S.sRoot_mul_self, S.sRoot_mul_self, mul_one,
      Int.cast_one]
  rw [mul_comm (S.sRoot (α - Pi.single i 1))]
  exact comm_eq_of_jacobi R _ _ _ _ _ _ hc hFβ (rootOp_single_comm_neg_single hV R i) hH hEβ

include hV in
theorem rootOp_neg_single_comm_single
    (i : Fin τ.rank) :
    D.rootOp R (-Pi.single i 1) * D.rootOp R (Pi.single i 1) -
      D.rootOp R (Pi.single i 1) * D.rootOp R (-Pi.single i 1) = -cartanOp R D i := by
  rw [← rootOp_single_comm_neg_single hV R i, neg_sub]

include hV in
theorem rootOp_neg_single_mul_cartanOp_mul
    (i j : Fin τ.rank) :
    D.rootOp R (-Pi.single i 1) * cartanOp R D j * D.rootOp R (-Pi.single i 1) = 0 := by
  have h := cartanOp_comm_rootOp hV R (isRoot_neg_single τ i) j
  have e : cartanOp R D j * D.rootOp R (-Pi.single i 1) = D.rootOp R (-Pi.single i 1) *
      cartanOp R D j + ((toWeight (-Pi.single i 1) j : ℤ) : R) • D.rootOp R (-Pi.single i 1) := by
    rw [← h]
    abel
  rw [mul_assoc, e, mul_add, ← mul_assoc, hV.rootOp_mul_self, zero_mul, mul_smul_comm,
    hV.rootOp_mul_self, smul_zero, add_zero]

include hV hS hpd in
theorem rootUnit_neg_conj_adjMap_single
    (i : Fin τ.rank) (c : R) (l : Label τ) :
    (rootUnit hV R (-Pi.single i 1) c : Module.End R (Fin D.d →₀ R)) *
        adjMap R S D (Finsupp.single l 1) *
          (((rootUnit hV R (-Pi.single i 1) c)⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) :
            Module.End R (Fin D.d →₀ R)) =
      adjMap R S D (yOp τ R i c (Finsupp.single l 1)) := by
  rw [coe_rootUnit, coe_rootUnit_inv, one_add_smul_mul_mul_one_sub_smul]
  rcases l with j | ⟨α, hα⟩
  · change _ = adjMap R S D (yOp τ R i c (hVec τ R j))
    rw [yOp_hVec', map_add, map_smul, adjMap_hVec, adjMap_rootVec, AdjSigns.sRoot_neg_single hS,
      show (Finsupp.single (Sum.inl j) 1 : RootModule τ R) = hVec τ R j from rfl, adjMap_hVec]
    have hc := cartanOp_comm_rootOp hV R (isRoot_neg_single τ i) j
    rw [toWeight_neg, Pi.neg_apply, toWeight_single] at hc
    have h1 : D.rootOp R (-Pi.single i 1) * (((S.epsZ j : ℤ) : R) • cartanOp R D j) -
        (((S.epsZ j : ℤ) : R) • cartanOp R D j) * D.rootOp R (-Pi.single i 1) =
          ((S.epsZ j * τ.cartan j i : ℤ) : R) • D.rootOp R (-Pi.single i 1) := by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, ← neg_sub, hc, smul_neg, smul_smul,
        ← neg_smul]
      congr 1
      push_cast
      ring
    have h2 : D.rootOp R (-Pi.single i 1) * (((S.epsZ j : ℤ) : R) • cartanOp R D j) *
        D.rootOp R (-Pi.single i 1) = 0 := by
      rw [mul_smul_comm, smul_mul_assoc, rootOp_neg_single_mul_cartanOp_mul R hV, smul_zero]
    rw [h1, h2, smul_zero, sub_zero, smul_smul, smul_smul]
    congr 2
    rcases AdjSigns.cartan_cases hS j i with rfl | h0 | ⟨h0, he⟩
    · rw [τ.cartan_self]
      push_cast
      ring
    · rw [h0]
      push_cast
      ring
    · rw [h0, he]
      push_cast
      ring
  · rw [← rootVec_eq_single R hα, adjMap_rootVec]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [yOp_rootVec_neg_single', adjMap_rootVec, mul_smul_comm, smul_mul_assoc, sub_self,
        smul_zero, add_zero, smul_mul_assoc, mul_assoc, hV.rootOp_mul_self, mul_zero, smul_zero,
        smul_zero, sub_zero]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [yOp_rootVec_single', map_add, map_add, map_smul, map_smul, adjMap_rootVec,
        adjMap_hVec, adjMap_rootVec, AdjSigns.sRoot_single hS, AdjSigns.sRoot_neg_single hS,
        mul_smul_comm, smul_mul_assoc, ← smul_sub, rootOp_neg_single_comm_single R hV i,
        smul_mul_assoc, rootOp_neg_single_mul_single_mul_neg_single hV R i]
      push_cast
      simp only [neg_smul, smul_neg, neg_neg, sub_neg_eq_add, pow_two]
    by_cases hr : IsRoot τ (α - Pi.single i 1)
    · have hne : -Pi.single i 1 + α ≠ 0 := fun h => h₁ (neg_add_eq_zero.1 h).symm
      rw [yOp_rootVec_of_sub R hpd i c hα h₁ h₂ hr, map_add, map_smul, adjMap_rootVec,
        adjMap_rootVec, mul_smul_comm, smul_mul_assoc, ← smul_sub,
        rootOp_neg_single_comm R hpd hV hS hα i hr, smul_mul_assoc,
        rootOp_neg_single_mul_mul_neg_single hV R hα i hne, smul_zero, smul_zero, sub_zero]
      simp only [smul_smul]
      congr 2
      have h' : ((S.sRoot α : ℤ) : R) * (S.sRoot α : R) = 1 := by
        rw [← Int.cast_mul, S.sRoot_mul_self, Int.cast_one]
      push_cast
      linear_combination (c * (S.sRoot (α - Pi.single i 1) : R)) * h'
    · have hne : -Pi.single i 1 + α ≠ 0 := fun h => h₁ (neg_add_eq_zero.1 h).symm
      have hr' : ¬ IsRoot τ (-Pi.single i 1 + α) := by rwa [neg_add_eq_sub]
      have hcomm := (hV.pairRel (R := R) (isRoot_neg_single τ i) hα hne).2 hr'
      rw [yOp_rootVec_of_not_sub R i c hα h₁ h₂ hr, adjMap_rootVec, mul_smul_comm,
        smul_mul_assoc, hcomm, sub_self, smul_zero, add_zero, smul_mul_assoc, mul_assoc,
        hV.rootOp_mul_self, mul_zero, smul_zero, smul_zero, sub_zero]

include hV hS hpd in
theorem rootUnit_neg_conj_adjMap
    (i : Fin τ.rank) (c : R) (v : RootModule τ R) :
    (rootUnit hV R (-Pi.single i 1) c : Module.End R (Fin D.d →₀ R)) * adjMap R S D v *
        (((rootUnit hV R (-Pi.single i 1) c)⁻¹ : (Module.End R (Fin D.d →₀ R))ˣ) :
          Module.End R (Fin D.d →₀ R)) =
      adjMap R S D (yOp τ R i c v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp only [map_zero, mul_zero, zero_mul]
  | add v w hv hw => rw [map_add, map_add, map_add, mul_add, add_mul, hv, hw]
  | single l b =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, mul_smul_comm, smul_mul_assoc,
      rootUnit_neg_conj_adjMap_single R hpd hV hS i c l]

end CFSG.TauCetiBridge.Minuscule
