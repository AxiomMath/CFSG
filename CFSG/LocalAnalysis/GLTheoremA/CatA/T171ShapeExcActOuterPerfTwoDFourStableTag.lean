module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourStable

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.RankThree.Lattice

theorem rootChar_eq_one_of_mem_charStabilizer_neg {τ : Tag} {L : Type} [Field L] [CharP L 2]
    {a : Fin τ.rank → Lˣ} {w : WeylGroup τ}
    (hw : w ∈ charStabilizer (rootCharHom a))
    (hneg : ∀ γ : Fin τ.rank → ℤ, w • γ = -γ) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = 1 := by
  have h1 : rootChar a (-γ) = rootChar a γ := by
    rw [← hneg γ]
    exact hw γ
  have hneg' : rootChar a (-γ) = (rootChar a γ)⁻¹ := by
    have e : -γ = (-1 : ℤ) • γ := by simp
    rw [e, rootChar_zsmul, zpow_neg_one]
  have h3 : rootChar a γ = (rootChar a γ)⁻¹ := h1.symm.trans hneg'
  have hsq : (rootChar a γ : L) ^ 2 = (1 : L) ^ 2 := by
    have h : rootChar a γ * rootChar a γ = 1 := by
      nth_rewrite 2 [h3]
      exact mul_inv_cancel _
    simpa [pow_two] using congrArg Units.val h
  refine Units.ext ?_
  exact (CharTwo.sq_inj (x := (rootChar a γ : L)) (y := 1)).1 hsq


theorem tag_simplyLaced_of_twistKind_twoD_rank_four {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .twoD)
    (h4 : compRank (componentRoots (rootCharHom a) i) = 4) :
    τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
  classical
  have hle : 4 ≤ τ.rank := h4 ▸ compRank_le (componentRoots (rootCharHom a) i)
  rcases τ with _ | _ | _ | _ | _ | _
  · exact absurd hle (by norm_num [Tag.rank])
  ·
    exfalso
    set Ψ := componentRoots (rootCharHom a) i with hΨdef
    have hΨ : IsRootComponent Ψ := isRootComponent_componentRoots i
    have hcard : Ψ.ncard = 24 := by
      obtain ⟨-, hc⟩ := shape_of_twistKind_twoD hkind
      rw [hc, h4]
    obtain ⟨w, hwW, hwneg⟩ :=
      exists_neg_mem_of_twistKind_twoD_rank_four (τ := .F4) S hT i hkind h4
    have hcardΔ : (simpleRoots Ψ).card = 4 := by
      rw [← compRank_eq_card hΨ, h4]
    have hcardF : Fintype.card (simpleRoots Ψ) = 4 := by
      rw [Fintype.card_coe]
      exact hcardΔ
    let e : simpleRoots Ψ ≃ Fin 4 := Fintype.equivFinOfCardEq hcardF
    let e' : simpleRoots Ψ ≃ Fin Tag.F4.rank :=
      e.trans (finCongr (by decide : 4 = Tag.F4.rank))
    let b : Fin Tag.F4.rank → (Fin Tag.F4.rank → ℤ) :=
      fun j => (e'.symm j : Fin Tag.F4.rank → ℤ)
    have hbasis : LinearIndependent ℚ (fun j => fun k => (b j k : ℚ)) := by
      have h := (linearIndependent_toRat hΨ).comp e'.symm e'.symm.injective
      have h' : LinearIndependent ℚ (fun j : Fin Tag.F4.rank =>
          fun k => ((e'.symm j : Fin Tag.F4.rank → ℤ) k : ℚ)) := h
      simpa [b] using h'
    have hbneg : ∀ j, w • b j = -b j := fun j =>
      hwneg (e'.symm j) (simpleRoots_subset (e'.symm j).2)
    have hneg_all : ∀ γ : Fin Tag.F4.rank → ℤ, w • γ = -γ := by
      intro γ
      exact smul_eq_neg_of_basis b hbasis hbneg γ
    have hwmem : w ∈ charStabilizer (rootCharHom a) := by
      refine (Subgroup.closure_le _).2 ?_ (componentWeylGroup_le Ψ hwW)
      rintro _ ⟨γ, hγ, rfl⟩
      exact rootReflection_mem_charStabilizer hγ.1
    have hχ : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → rootChar a γ = 1 :=
      fun γ _ => rootChar_eq_one_of_mem_charStabilizer_neg hwmem hneg_all γ
    have hker : kernelRoots (rootCharHom a) = {γ | IsRoot Tag.F4 γ} := by
      ext γ
      constructor
      · exact fun h => h.1
      · intro hγ
        exact ⟨hγ, hχ γ hγ⟩
    have hroots_card : {γ : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 γ}.ncard = 48 := by
      have hset : {γ : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 γ} =
          (rootFinset Tag.F4 : Set (Fin Tag.F4.rank → ℤ)) := by
        ext γ
        rw [Set.mem_setOf_eq, Finset.mem_coe, mem_rootFinset]
      rw [hset, Set.ncard_coe_finset, card_rootFinset]
      rfl
    have hsubset : Ψ ⊂ {γ : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 γ} := by
      refine Set.ssubset_iff_subset_ne.2 ⟨fun γ hγ => hΨ.isRoot γ hγ, ?_⟩
      intro heq
      have hc := congrArg Set.ncard heq
      rw [hcard, hroots_card] at hc
      norm_num at hc
    obtain ⟨δ, hδroot, hδΨ⟩ := Set.exists_of_ssubset hsubset
    have hδker : δ ∈ kernelRoots (rootCharHom a) := by rw [hker]; exact hδroot
    let j : KernelComponent (rootCharHom a) := Quotient.mk _ ⟨δ, hδker⟩
    have hδj : δ ∈ componentRoots (rootCharHom a) j := ⟨hδker, rfl⟩
    have hjne : j ≠ i := by
      intro hji
      rw [hji] at hδj
      exact hδΨ hδj
    have horth : ∀ γ ∈ Ψ, iform δ γ = 0 := fun γ hγ =>
      iform_eq_zero_of_mem_componentRoots hjne hδj hγ
    obtain ⟨m, hm, c, hc⟩ :=
      exists_zsmul_eq_sum_of_basis b hbasis δ
    have hsum : iform δ (∑ j, c j • b j) = 0 := by
      rw [iform_finset_sum_right]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [iform_smul_right, horth (e'.symm k) (simpleRoots_subset (e'.symm k).2), mul_zero]
    have hmul : iform δ (m • δ) = m * iform δ δ := iform_smul_right m δ δ
    rw [hc] at hmul
    have hmzero : m * iform δ δ = 0 := hmul.symm.trans hsum
    have hδδ : iform δ δ = 0 := (mul_eq_zero.1 hmzero).resolve_left hm
    exact hδroot.ne_zero (eq_zero_of_iform_self_eq_zero hδδ)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
