module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.MonomialTwo

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}


theorem rootCharStabilizerSubgroup_le_kernelReflectionGroup_two
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (ha : ∀ i, a i ^ 2 = 1) : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  have hpm : ∀ i, a i = 1 ∨ a i = -1 := fun i => by
    have h : ((a i : L) - 1) * ((a i : L) + 1) = 0 := by
      have := congrArg (fun u : Lˣ => (u : L)) (ha i)
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
      linear_combination this
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (Units.ext (by simpa [sub_eq_zero] using h))
    · exact Or.inr (Units.ext (by simpa [add_eq_zero_iff_eq_neg] using h))
  by_cases hL : ringChar L = 2
  ·
    have ha1 : ∀ i, a i = 1 := fun i => by
      rcases hpm i with h | h
      · exact h
      · have : CharP L 2 := ringChar.of_eq hL
        rw [h]
        exact Units.ext (by simp [CharTwo.neg_eq])
    intro w _
    have hle : Subgroup.closure (Set.range (simple τ)) ≤ kernelReflectionGroup a := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine Subgroup.subset_closure ⟨1, i, ⟨by simpa using isRoot_single τ i, ?_⟩, by group⟩
      simp [rootChar, ha1]
    rw [(coxeterSystem τ).subgroup_closure_range_simple] at hle
    exact hle (Subgroup.mem_top w)
  · intro w hw
    have h1 := (mem_rootCharStabilizer_iff hL hpm).1 hw
    obtain ⟨-, -, heq, -, -⟩ := sign_character_Weyl_stabilizer_quotients τ
      (maskChar (signTupleBits a))
    rw [kernelReflectionGroup_eq_kernelWeylGroup hL hpm, ← heq hτ]
    exact h1

theorem planesToralBar_two
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) : Torality.PlanesToralBar τ 2 :=
  planesToralBar_of_monomialToral Nat.prime_two (monomialToralAt_two τ)
    fun _ _ a ha => rootCharStabilizerSubgroup_le_kernelReflectionGroup_two hτ a ha

theorem langToralPlane_two
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) : LangToralPlane τ 2 :=
  Torality.langToralPlane_of_bar Nat.prime_two (planesToralBar_two hτ)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
