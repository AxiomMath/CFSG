module

public import CFSG.LieType.Chevalley.LangG2Tangent

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley


theorem linearIndependent_pinnedE_tangentH_of_two_ne_zero {τ : Tag} {F : Type} [Field F]
    (h2 : (2 : F) ≠ 0) (hdet : (τ.cartan.map (Int.cast : ℤ → F)).det ≠ 0) :
    LinearIndependent F (Sum.elim (fun α : {α // IsRoot τ α} => pinnedE τ F α.1)
      (tangentH τ F)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have hEwt : ∀ β : {α // IsRoot τ α}, MapsLabelWt (pinnedE τ F β.1) (· + β.1) := by
    intro β
    rw [(rootOperatorFamily τ).pinnedE_eq_smul_D F β.2]
    exact (((rootOperatorFamily τ).mapsLabelWt_D (R := F) β (k := 1) le_rfl).smul
      _).congr fun μ => by simp
  have hHdiag : ∀ (i : Fin τ.rank) (a b : Label τ),
      tangentH τ F i (Finsupp.single b 1) a ≠ 0 → a = b := by
    intro i a b h
    rcases b with j | β
    · rw [tangentH, Finsupp.linearCombination_single, one_smul] at h
      simp at h
    · rw [tangentH, Finsupp.linearCombination_single, one_smul, Finsupp.smul_apply,
        smul_eq_mul] at h
      exact (Finsupp.single_apply_ne_zero.1 (right_ne_zero_of_mul h)).1
  have hEne : ∀ β : {α // IsRoot τ α}, pinnedE τ F β.1 ≠ 0 := by
    intro β h
    have hε : ((pinnedData τ β.1).2.2 : F) ≠ 0 := by
      rcases pinnedSign_eq τ β.1 with h1 | h1 <;> simp [h1]
    rw [pinnedE] at h
    have hconj : (pinnedWeyl τ F β.1 : Module.End F (RootModule τ F)) *
        infE τ F (pinnedData τ β.1).1 *
        ((pinnedWeyl τ F β.1)⁻¹).val = 0 :=
      (smul_eq_zero.1 h).resolve_left hε
    have hWW : ((pinnedWeyl τ F β.1)⁻¹).val *
        ((pinnedWeyl τ F β.1 : Module.End F (RootModule τ F)) *
          infE τ F (pinnedData τ β.1).1 *
          ((pinnedWeyl τ F β.1)⁻¹).val) *
        (pinnedWeyl τ F β.1 : Module.End F (RootModule τ F)) =
        infE τ F (pinnedData τ β.1).1 := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul,
        mul_one]
    have hzero : ((pinnedWeyl τ F β.1)⁻¹).val *
        ((pinnedWeyl τ F β.1 : Module.End F (RootModule τ F)) *
          infE τ F (pinnedData τ β.1).1 *
          ((pinnedWeyl τ F β.1)⁻¹).val) *
        (pinnedWeyl τ F β.1 : Module.End F (RootModule τ F)) = 0 := by
      rw [hconj, mul_zero, zero_mul]
    have hinf : infE τ F (pinnedData τ β.1).1 = 0 := by
      rw [← hWW]
      exact hzero
    set j := (pinnedData τ β.1).1 with hj
    have hval := congrArg (fun e : Module.End F (RootModule τ F) => e (hVec τ F j)) hinf
    simp only [LinearMap.zero_apply] at hval
    have hcart : (τ.cartan j j).natAbs = 2 := by
      rw [τ.cartan_self]
      norm_num
    have hroot1 : rootVec τ F (Pi.single j 1)
        (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩) = 1 := by
      have h := rootVec_apply_inr (τ := τ) (R := F) (β := Pi.single j 1)
        ⟨Pi.single j 1, isRoot_single τ j⟩
      simpa using h
    rw [infE_hVec, hcart] at hval
    have hc := congrArg (fun x : RootModule τ F =>
      x (Sum.inr ⟨Pi.single j 1, isRoot_single τ j⟩)) hval
    simp [hroot1] at hc
    exact h2 hc
  have hroot : ∀ β : {α // IsRoot τ α}, g (Sum.inl β) = 0 := by
    intro β
    have hzero : g (Sum.inl β) • pinnedE τ F β.1 = 0 := by
      refine (Finsupp.basisSingleOne (R := F) (ι := Label τ)).ext fun b => ?_
      rw [LinearMap.smul_apply, LinearMap.zero_apply, Finsupp.coe_basisSingleOne]
      refine Finsupp.ext fun a => ?_
      rw [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, smul_eq_mul]
      by_cases hw : labelWt τ a = labelWt τ b + β.1
      · have h := LinearMap.congr_fun hg (Finsupp.single b 1)
        have h2 := congrArg (fun x : RootModule τ F => x a) h
        simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
          Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at h2
        have hsumE : (∑ γ : {α // IsRoot τ α},
            g (Sum.inl γ) * (pinnedE τ F γ.1 (Finsupp.single b 1) a)) =
            g (Sum.inl β) * (pinnedE τ F β.1 (Finsupp.single b 1) a) := by
          refine Finset.sum_eq_single β ?_ ?_
          · intro γ _ hγ
            have hz : pinnedE τ F γ.1 (Finsupp.single b 1) a = 0 := by
              by_contra hne
              have hwt := hEwt γ a b hne
              rw [hwt] at hw
              exact hγ (Subtype.ext (add_left_cancel hw))
            rw [hz, mul_zero]
          · intro hnot
            exact absurd (Finset.mem_univ β) hnot
        have hsumH : (∑ i : Fin τ.rank,
            g (Sum.inr i) * (tangentH τ F i (Finsupp.single b 1) a)) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          have hz : tangentH τ F i (Finsupp.single b 1) a = 0 := by
            by_contra hne
            have hab : a = b := hHdiag i a b hne
            rw [hab] at hw
            have hβ0 : β.1 = 0 := by
              have h' : labelWt τ b + (0 : Fin τ.rank → ℤ) = labelWt τ b + β.1 := by
                rw [add_zero]
                exact hw
              exact (add_left_cancel h').symm
            exact β.2.ne_zero hβ0
          rw [hz, mul_zero]
        rw [hsumE, hsumH, add_zero] at h2
        exact h2
      · have hz : pinnedE τ F β.1 (Finsupp.single b 1) a = 0 := by
          by_contra hne
          exact hw (hEwt β a b hne)
        rw [hz, mul_zero]
    exact (smul_eq_zero.1 hzero).resolve_right (hEne β)
  have hg' : (∑ i : Fin τ.rank, g (Sum.inr i) • tangentH τ F i) = 0 := by
    simpa [hroot] using hg
  have h3 : ∀ k : Fin τ.rank,
      ∑ i : Fin τ.rank, g (Sum.inr i) * ((τ.cartan i k : ℤ) : F) = 0 := by
    intro k
    have h := LinearMap.congr_fun hg' (rootVec τ F (Pi.single k 1))
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.zero_apply] at h
    have h2 := congrArg
      (fun x : RootModule τ F => x (Sum.inr ⟨Pi.single k 1, isRoot_single τ k⟩)) h
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      smul_eq_mul] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tangentH_rootVec i (isRoot_single τ k), Finsupp.smul_apply]
    have h5 : rootVec τ F (Pi.single k 1)
        (Sum.inr ⟨Pi.single k 1, isRoot_single τ k⟩) = 1 := by
      have := rootVec_apply_inr (τ := τ) (R := F) (β := Pi.single k 1)
        ⟨Pi.single k 1, isRoot_single τ k⟩
      simpa using this
    rw [h5, smul_eq_mul, mul_one]
    have h6 : (∑ j, τ.cartan i j * (Pi.single k 1 : Fin τ.rank → ℤ) j) = τ.cartan i k := by
      simp [Pi.single_apply]
    rw [h6]
  have h4 : (fun i => g (Sum.inr i)) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    funext k
    simpa [Matrix.vecMul, dotProduct] using h3 k
  rintro (β | i)
  · exact hroot β
  · exact congrFun h4 i

theorem linearIndependent_pinnedE_tangentH_E7 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    LinearIndependent F (Sum.elim (fun α : {α // IsRoot Tag.E7 α} => pinnedE Tag.E7 F α.1)
      (tangentH Tag.E7 F)) := by
  refine linearIndependent_pinnedE_tangentH_of_two_ne_zero (τ := Tag.E7) h2 ?_
  have h := RingHom.map_det (Int.castRingHom F) Tag.E7.cartan
  rw [det_cartan_E7] at h
  intro h0
  exact h2 (by simpa using h.trans h0)

end CFSG.LieType.Chevalley

end
