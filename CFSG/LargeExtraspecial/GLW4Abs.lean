module

public import CFSG.LargeExtraspecial.O62Normalizer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.O62
open CFSG.ClassicalGroups.Orthogonal (eichler)

theorem mem_span_model (minus : Bool) (x : V₀) :
    x ∈ Submodule.span (ZMod 2) {w : V₀ | (if minus then qMinus else qPlus) w = 0} := by
  set P := Submodule.span (ZMod 2) {w : V₀ | (if minus then qMinus else qPlus) w = 0}
  have hs : ∀ w : V₀, (if minus then qMinus else qPlus) w = 0 → w ∈ P :=
    fun w hw => Submodule.subset_span hw
  have hval : ∀ w : V₀, (if minus then qMinus else qPlus) w =
      if minus then w 0 * w 1 + w 2 * w 3 + w 4 * w 4 + w 4 * w 5 + w 5 * w 5
      else w 0 * w 1 + w 2 * w 3 + w 4 * w 5 := fun w => by
    cases minus
    · simp [qPlus_apply]
    · simp [qMinus_apply]
  have he : ∀ i : Fin 6, (Pi.single i 1 : V₀) ∈ P := by
    have h03 : ∀ i : Fin 6, i.val < 4 → (Pi.single i 1 : V₀) ∈ P := fun i hi =>
      hs _ (by rw [hval]; revert hi; revert i; cases minus <;> decide)
    have h45 : ∀ i : Fin 6, 4 ≤ i.val → (Pi.single i 1 : V₀) ∈ P := by
      intro i hi
      cases minus
      · exact hs _ (by rw [hval]; revert hi; revert i; decide)
      · have h1 := hs (Pi.single 0 1 + Pi.single 1 1 + Pi.single i 1)
          (by rw [hval]; revert hi; revert i; decide)
        have h2 := P.sub_mem (P.sub_mem h1 (h03 0 (by decide))) (h03 1 (by decide))
        convert h2 using 1
        abel
    intro i
    by_cases hi : i.val < 4
    · exact h03 i hi
    · exact h45 i (by omega)
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => P.smul_mem _ ?_
  convert he i using 1
  ext j
  simp [Pi.single_apply, eq_comm]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem mem_span_singular (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate)
    (v : V) : v ∈ Submodule.span (ZMod 2) {w : V | Q w = 0} := by
  obtain ⟨L, hL⟩ := exists_linearEquiv_model hV hQ
  obtain ⟨minus, hm⟩ : ∃ minus : Bool, ∀ v, (if minus then qMinus else qPlus) (L v) = Q v := by
    rcases hL with h | h
    exacts [⟨false, h⟩, ⟨true, h⟩]
  have hmap : (Submodule.span (ZMod 2) {w : V₀ | (if minus then qMinus else qPlus) w = 0}).map
      (L.symm : V₀ →ₗ[ZMod 2] V) ≤ Submodule.span (ZMod 2) {w : V | Q w = 0} := by
    rw [Submodule.map_span_le]
    intro w hw
    refine Submodule.subset_span ?_
    change Q (L.symm w) = 0
    rw [← hm, LinearEquiv.apply_symm_apply]
    exact hw
  exact hmap (Submodule.mem_map.mpr ⟨L v, mem_span_model minus (L v), by simp⟩)

theorem eq_zero_or_eq_id_of_commute_omega (hV : finrank (ZMod 2) V = 6)
    (hQ : Q.polarBilin.Nondegenerate) (f : V →ₗ[ZMod 2] V)
    (hf : ∀ g ∈ omegaGroup Q hQ, ∀ v, f (g v) = g (f v)) : f = 0 ∨ f = LinearMap.id := by
  obtain ⟨L, hL⟩ := exists_linearEquiv_model hV hQ
  obtain ⟨qM, hm, hpol', hq0⟩ : ∃ qM : QuadraticForm (ZMod 2) V₀, (∀ v, qM (L v) = Q v) ∧
      (∀ x y : V₀, polar qM x y =
        x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 + x 4 * y 5 + x 5 * y 4) ∧
      qM (Pi.single 0 1) = 0 := by
    rcases hL with h | h
    · exact ⟨qPlus, h, polar_qPlus, by simp [qPlus_apply]⟩
    · exact ⟨qMinus, h, polar_qMinus, by simp [qMinus_apply]⟩
  have hQs : ∀ x : V₀, Q (L.symm x) = qM x := fun x => by
    rw [← hm, LinearEquiv.apply_symm_apply]
  have hpol : ∀ x y : V₀, polar Q (L.symm x) (L.symm y) = polar qM x y := fun x y => by
    simp only [polar, ← map_add, hQs]
  set a₀ := L.symm (Pi.single 0 1)
  have hqa : Q a₀ = 0 := by rw [hQs, hq0]
  have hne : ∀ i j : Fin 6, i ≠ j → L.symm (Pi.single i 1) ≠ L.symm (Pi.single j 1) :=
    fun i j hij h => by
      have := congrFun (L.symm.injective h) i
      simp [hij] at this
  have hne0 : ∀ i : Fin 6, L.symm (Pi.single i 1) ≠ 0 := fun i h => by
    have := congrFun ((LinearEquiv.map_eq_zero_iff L.symm).mp h) i
    simp at this
  have hcomm : ∀ g ∈ omegaGroup Q hQ, ∀ w ∈ commSpace g, f w ∈ commSpace g := by
    intro g hg w hw
    obtain ⟨x, rfl⟩ := mem_commSpace.mp hw
    exact mem_commSpace.mpr ⟨f x, by rw [map_sub, hf g hg x]⟩
  have hspan : ∀ j : Fin 6, j = 2 ∨ j = 3 →
      f a₀ ∈ Submodule.span (ZMod 2) {a₀, L.symm (Pi.single j 1)} := by
    intro j hj
    have hp : polar Q a₀ (L.symm (Pi.single j 1)) = 0 := by
      rw [hpol, hpol']
      rcases hj with rfl | rfl <;> simp
    have hli : LinearIndependent (ZMod 2) ![a₀, L.symm (Pi.single j 1)] :=
      OrthoF2.linearIndependent_pair_iff.mpr ⟨hne0 0, hne0 j, hne 0 j (by
        rcases hj with rfl | rfl <;> decide)⟩
    have hE := commSpace_eichler hQ hqa hp hli
    rw [← hE]
    exact hcomm _ (eichler_mem_omegaGroup hQ _ _) _ (hE ▸ Submodule.subset_span (by simp))
  obtain ⟨α, β, h1⟩ := Submodule.mem_span_pair.mp (hspan 2 (Or.inl rfl))
  obtain ⟨γ, δ, h2⟩ := Submodule.mem_span_pair.mp (hspan 3 (Or.inr rfl))
  have hβ : β = 0 := by
    have := congrArg (fun v => L v 2) (h1.trans h2.symm)
    simpa [a₀, Pi.single_apply] using this
  have hfa : f a₀ = α • a₀ := by rw [← h1, hβ, zero_smul, add_zero]
  have hsing : ∀ a : V, Q a = 0 → f a = α • a := by
    intro a ha
    by_cases ha0 : a = 0
    · rw [ha0, map_zero, smul_zero]
    obtain ⟨g, hg, hga⟩ := exists_mem_omegaGroup_apply_eq hQ (by omega) (hne0 0) ha0
      (hqa.trans ha.symm)
    rw [← hga, hf g hg, hfa, map_smul]
  have hall : ∀ v : V, f v = α • v := fun v => by
    induction mem_span_singular hV hQ v using Submodule.span_induction with
    | mem x hx => exact hsing x hx
    | zero => rw [map_zero, smul_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
    | smul c x _ hx => rw [map_smul, hx, smul_comm]
  rcases zmod2_eq_zero_or_eq_one α with rfl | rfl
  · exact Or.inl (LinearMap.ext fun v => by rw [hall, zero_smul, LinearMap.zero_apply])
  · exact Or.inr (LinearMap.ext fun v => by rw [hall, one_smul, LinearMap.id_apply])

end CFSG.LargeExtraspecial.GLW4
