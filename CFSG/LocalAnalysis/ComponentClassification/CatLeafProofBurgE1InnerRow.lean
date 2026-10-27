module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Glue
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1InnerConj
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.RankThree.Chevalley.SteinbergCFERootSL2Traces
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Torus

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {τ : Tag} {K : Type} [Field K]

theorem exists_mem_rootCharKernel_of_isRoot_add {b : Fin τ.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) {i j : Fin τ.rank}
    (hij : IsRoot τ (Pi.single i 1 + Pi.single j 1)) : ∃ γ, γ ∈ rootCharKernel b := by
  rcases hb i with hi | hi
  · exact ⟨_, isRoot_single τ i, by rw [rootChar_single', hi]⟩
  rcases hb j with hj | hj
  · exact ⟨_, isRoot_single τ j, by rw [rootChar_single', hj]⟩
  exact ⟨_, hij, by rw [rootChar_add, rootChar_single', rootChar_single', hi, hj]; simp⟩

theorem conjGL_one_eq {M : Type*} [Field M] (Z : Matrix.SpecialLinearGroup (Fin 2) M) :
    conjGL (1 : GL (Fin 2) M) Z = Z :=
  Subtype.ext (by simp [conjGL])

@[expose] def pointwiseStab {L : Type*} [Group L] (H : Subgroup L) : Subgroup (MulAut L) where
  carrier := {η | ∀ x ∈ H, η x = x}
  mul_mem' {η η'} hη hη' x hx := by
    change η (η' x) = x
    rw [hη' x hx, hη x hx]
  one_mem' x _ := rfl
  inv_mem' {η} hη x hx := by
    change η.symm x = x
    rw [MulEquiv.symm_apply_eq, hη x hx]

theorem burgOddCoreFor_innerDiagonal
    [Finite K] (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E8) (hK2 : ringChar K ≠ 2)
    (S : Fin τ.rank → Prop)
    (hγ : ∀ b : Fin τ.rank → Kˣ, (∀ i, b i = 1 ∨ b i = -1) → ∃ γ ∈ rootCharKernel b,
      ∀ (w : WeylGroup τ) (k : Fin τ.rank), w • (Pi.single k 1 : Fin τ.rank → ℤ) = γ → S k)
    (hcore : ∀ b : Fin τ.rank → Kˣ, (∀ i, b i = 1 ∨ b i = -1) → b ≠ 1 →
      pPrimeCore 2 (toralCentralizer τ K b) = ⊥)
    (hpw : ∀ (k : Fin τ.rank), S k → ∀ h : ModGL τ (AlgebraicClosure K),
      (∀ B : Matrix.SpecialLinearGroup (Fin 2) K,
        h * simpleRootSL2 τ (AlgebraicClosure K) k (conjGL 1
          (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) B)) * h⁻¹ ∈
            (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) →
      ∀ Z : Subgroup (MulAut (adjointGroup τ K)),
      (∀ η ∈ Z, ∀ (u : adjointGroup τ K) (B : Matrix.SpecialLinearGroup (Fin 2) K),
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL τ K) =
          h * simpleRootSL2 τ (AlgebraicClosure K) k (conjGL 1
            (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) B)) * h⁻¹ →
          η u = u) →
      ∀ η ∈ Z, Odd (orderOf η) →
        η ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹)
    (hα : orderOf α = 2) : BurgOddCoreFor α := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hKodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK2
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8 := by
    rcases hτ with h | h | h
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inr h))]
  have : Finite (ModGL τ K) := finite_modGL
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hα
    exact absurd hα (by decide)
  refine burgOddCoreFor_of_inner (center_adjointGroup_eq_bot_field τ K) ?_ ?_
  ·
    obtain ⟨b, hb, hb1, ⟨e⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag hτ' hKodd hαg hα2
    have h1 := pPrimeCore_map_iso 2 e.symm
    rw [hcore b hb (hb1 hα1), Subgroup.map_bot] at h1
    exact h1.symm
  · intro β hβ _ hfix
    obtain ⟨b, hb, h, hconj⟩ := exists_conj_toralCentralizer_of_innerDiagonal hτ' hKodd hαg hα2
    obtain ⟨γ, hγ, hγS⟩ := hγ b hb
    obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 hγ.1
    set n := canonicalRep (coxeterSystem τ) K w
    obtain ⟨-, -, hQ, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK2 hγ.1
    have hQmap := (hQ w k hwk).1
    have hγ' : -γ ∈ rootCharKernel b :=
      ⟨IsRoot.neg hγ.1, by rw [rootChar_neg', hγ.2, inv_one]⟩
    have hQX : rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) ≤ toralCentralizer τ K b :=
      le_trans (sup_le (le_iSup₂ (f := fun β (_ : β ∈ rootCharKernel b) => rootSubgroup τ K β)
        γ hγ) (le_iSup₂ (f := fun β (_ : β ∈ rootCharKernel b) => rootSubgroup τ K β) (-γ) hγ'))
        (rootSpan_rootCharKernel_le_toralCentralizer b)
    have hu : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K,
        n * simpleRootSL2 τ K k B * n⁻¹ ∈ toralCentralizer τ K b := by
      intro B
      refine hQX ?_
      rw [← hQmap]
      refine ⟨simpleRootSL2 τ K k B, ?_, rfl⟩
      rw [← range_simpleRootSL2]
      exact ⟨B, rfl⟩
    have hc : ∀ B : Matrix.SpecialLinearGroup (Fin 2) K, ∃ c : adjointGroup τ K,
        c ∈ fixedSubgroup α ∧ baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) =
          (h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) n) *
            simpleRootSL2 τ (AlgebraicClosure K) k (conjGL 1
              (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) B)) *
            (h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) n)⁻¹ := by
      intro B
      obtain ⟨c, hcα, hcι⟩ := hconj _ (hu B)
      refine ⟨c, hcα, ?_⟩
      rw [hcι, conjGL_one_eq, ← baseChangeGL_simpleRootSL2, map_mul,
        map_mul, map_inv]
      group
    refine hpw k (hγS w k hwk) (h⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) n)
      (fun B => ?_)
      (pointwiseStab (fixedSubgroup α))
      (fun η hη u B hB => ?_) β hfix hβ
    · obtain ⟨c, -, hcι⟩ := hc B
      exact ⟨c, c.2, hcι⟩
    · obtain ⟨c, hcα, hcι⟩ := hc B
      have huc : u = c :=
        Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) (hB.trans hcι.symm))
      rw [huc]
      exact hη c hcα

end CFSG.ComponentClassification.CatLeafProof
