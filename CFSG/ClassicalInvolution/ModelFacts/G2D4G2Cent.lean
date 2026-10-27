module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairG2

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups

section Generic

variable {τ : Tag} {K : Type} [Field K]

@[expose] def rootPair (τ : Tag) (K : Type) [Field K] (γ : Fin τ.rank → ℤ) :
    Subgroup (ModGL τ K) :=
  rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)

theorem rootPair_neg (γ : Fin τ.rank → ℤ) : rootPair τ K (-γ) = rootPair τ K γ := by
  rw [rootPair, rootPair, neg_neg, sup_comm]

theorem rootPair_eq_rootSpan (γ : Fin τ.rank → ℤ) :
    rootPair τ K γ = rootSpan τ K {γ, -γ} := by
  rw [rootPair, rootSpan, iSup_insert, iSup_singleton]

theorem canonicalRep_mem_normalizer_rootPair {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {w : WeylGroup τ} (hw : w • γ = γ ∨ w • γ = -γ) :
    canonicalRep (coxeterSystem τ) K w ∈
      Subgroup.normalizer (rootPair τ K γ : Set (ModGL τ K)) := by
  apply mem_normalizer_of_map_eq
  have h1 := (canonical_weyl_root_transport τ K).2.1 w γ hγ
  have h2 := (canonical_weyl_root_transport τ K).2.1 w (-γ) (IsRoot.neg hγ)
  rw [rootPair, Subgroup.map_sup, h1, h2, smul_neg]
  rcases hw with h | h
  · rw [h]
  · rw [h, neg_neg, sup_comm]

theorem le_normalizer_of_commutator_eq_bot {G : Type*} [Group G] {A B : Subgroup G}
    (h : ⁅A, B⁆ = ⊥) : A ≤ Subgroup.normalizer (B : Set G) :=
  (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans (Subgroup.centralizer_le_normalizer _)

end Generic

section G2

variable {K : Type} [Field K]

theorem iform_ne_g2 {α β : Fin Tag.G2.rank → ℤ} {a : Fin Tag.G2.rank → Kˣ}
    (h : (a = ![-1, 1] ∧ α = ![0, 1] ∧ β = ![2, 3]) ∨ (a = ![1, -1] ∧ α = ![1, 0] ∧
      β = ![1, 2]) ∨ (a = ![-1, -1] ∧ α = ![1, 1] ∧ β = ![1, 3])) :
    iform α α ≠ iform β β := by
  rcases h with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
    simp [iform, Tag.symmetrizedCartan] <;> decide

theorem iform_neg_self {τ : Tag} (x : Fin τ.rank → ℤ) : iform (-x) (-x) = iform x x := by
  rw [← neg_one_smul ℤ x, iform_smul_left, iform_smul_right]
  ring

theorem eq_or_eq_neg_of_iform_eq {τ : Tag} {α β x y : Fin τ.rank → ℤ}
    (hne : iform α α ≠ iform β β) (hx : x = α ∨ x = -α ∨ x = β ∨ x = -β)
    (hy : y = α ∨ y = -α ∨ y = β ∨ y = -β) (h : iform y y = iform x x) : y = x ∨ y = -x := by
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
    rw [hx, hy] at h ⊢ <;>
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact Or.inr (neg_neg _).symm
    | (exfalso
       try simp only [iform_neg_self] at h
       first
       | exact hne h
       | exact hne h.symm)

theorem toralCentralizer_le_normalizer_rootPair [Finite K] (hK : Odd (Nat.card K))
    {a : Fin Tag.G2.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) (hne : a ≠ 1)
    {γ : Fin Tag.G2.rank → ℤ} (hγ : γ ∈ rootCharKernel a) :
    toralCentralizer Tag.G2 K a ≤
      Subgroup.normalizer (rootPair Tag.G2 K γ : Set (ModGL Tag.G2 K)) := by
  obtain ⟨α, β, hcases, hker, hspan, hcomm, -⟩ := g2_toral_data hK ha hne
  have hlen := iform_ne_g2 (K := K) hcases
  have hγmem : γ = α ∨ γ = -α ∨ γ = β ∨ γ = -β := by
    have := hγ
    rw [hker] at this
    simpa using this
  rw [(Chevalley_toral_centralizer_Bruhat_factors Tag.G2 K a).2.2.2]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [rootPair_eq_rootSpan]
    exact torusGroup_le_normalizer_rootSpan (by
      intro x hx
      rcases hx with rfl | rfl
      · exact hγ.1
      · exact IsRoot.neg hγ.1)
  · rw [hspan]
    have hcomm' : ⁅rootPair Tag.G2 K α, rootPair Tag.G2 K β⁆ = ⊥ := hcomm
    have hαβ : rootSubgroup Tag.G2 K α ⊔ rootSubgroup Tag.G2 K (-α) ⊔
        (rootSubgroup Tag.G2 K β ⊔ rootSubgroup Tag.G2 K (-β)) =
        rootPair Tag.G2 K α ⊔ rootPair Tag.G2 K β := rfl
    rw [hαβ]
    have hβα : ⁅rootPair Tag.G2 K β, rootPair Tag.G2 K α⁆ = ⊥ := by
      rw [← Subgroup.commutator_comm]
      exact hcomm'
    rcases hγmem with rfl | rfl | rfl | rfl
    · exact sup_le Subgroup.le_normalizer (le_normalizer_of_commutator_eq_bot hβα)
    · rw [rootPair_neg]
      exact sup_le Subgroup.le_normalizer (le_normalizer_of_commutator_eq_bot hβα)
    · exact sup_le (le_normalizer_of_commutator_eq_bot hcomm') Subgroup.le_normalizer
    · rw [rootPair_neg]
      exact sup_le (le_normalizer_of_commutator_eq_bot hcomm') Subgroup.le_normalizer
  · rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    have hwγ : w • γ ∈ rootCharKernel a := ⟨IsRoot.smul hγ.1 w, by rw [hw γ]; exact hγ.2⟩
    have hwγ' : w • γ = α ∨ w • γ = -α ∨ w • γ = β ∨ w • γ = -β := by
      have := hwγ
      rw [hker] at this
      simpa using this
    have hiw : iform (w • γ) (w • γ) = iform γ γ := iform_smul w γ γ
    exact canonicalRep_mem_normalizer_rootPair hγ.1
      (eq_or_eq_neg_of_iform_eq hlen hγmem hwγ' hiw)

theorem exists_signKernel_g2 (hK : ringChar K ≠ 2) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot Tag.G2 γ) :
    ∃ a : Fin Tag.G2.rank → Kˣ, (∀ i, a i = 1 ∨ a i = -1) ∧ a ≠ 1 ∧ γ ∈ rootCharKernel a := by
  obtain ⟨w, i, hw⟩ := isRoot_iff_exists_smul_single.mp hγ
  set b : Fin Tag.G2.rank → Kˣ := fun j => (-1 : Kˣ) ^ Tag.G2.cartan i j with hb
  have hbsq : ∀ j, b j ^ 2 = 1 := fun j => by
    simp only [hb]
    rcases Int.even_or_odd (Tag.G2.cartan i j) with h | h
    · simp [Even.neg_one_zpow h]
    · simp [Odd.neg_one_zpow h]
  set c := weylTuple w b with hc
  have hcsign : ∀ j, c j = 1 ∨ c j = -1 := fun j =>
    unit_eq_one_or_neg_one_of_sq_eq_one (weylTuple_sq_eq_one hbsq w j)
  have hcχ : rootChar c γ = 1 := by
    rw [hc, rootChar_weylTuple, ← hw, inv_smul_smul]
    have h2 := rootChar_nsmul_single b i 1
    rw [one_smul, pow_one] at h2
    rw [h2]
    simp [hb, Tag.cartan_self]
  have hcne : c ≠ 1 := by
    intro hc1
    have h2 : canonicalRep (coxeterSystem Tag.G2) K w * rootDiagUnit Tag.G2 b *
        (canonicalRep (coxeterSystem Tag.G2) K w)⁻¹ = 1 := by
      rw [canonicalRep_conj_rootDiagUnit, ← hc, hc1, rootDiagUnit_one]
    have h3 : rootDiagUnit Tag.G2 b = (1 : ModGL Tag.G2 K) := by
      rwa [mul_inv_eq_one, mul_eq_left] at h2
    have h1 : torusElt Tag.G2 K i (-1) = rootDiagUnit Tag.G2 b := torusElt_eq_rootDiagUnit i (-1)
    have h4 : simpleRootSL2 Tag.G2 K i (-1) = simpleRootSL2 Tag.G2 K i 1 := by
      rw [neg_one_eq_HSL, simpleRootSL2_HSL, h1, h3, map_one]
    have h5 := simpleRootSL2_injective hK i h4
    have h6 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h5
    exact Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using h6)
  exact ⟨c, hcsign, hcne, hγ, hcχ⟩

end G2

end CFSG.ClassicalInvolution.G2D4Models
