module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPair
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortSp
public import CFSG.ClassicalInvolution.ModelFacts.CommutingFundamentalSymplectic

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open Matrix CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

section SignGroup

variable {F : Type} [Field F] {n : ℕ}

def signTuples (F : Type) [Field F] (n : ℕ) : Subgroup (Fin n → Fˣ) where
  carrier := {ε | ∀ j, ε j = 1 ∨ ε j = -1}
  mul_mem' := by
    intro a b ha hb j
    rcases ha j with h | h <;> rcases hb j with h' | h' <;> simp [h, h']
  one_mem' := fun _ => Or.inl rfl
  inv_mem' := by
    intro a ha j
    rcases ha j with h | h <;> simp [h]

@[expose] noncomputable def spSignGroup (F : Type) [Field F] (n : ℕ) : Subgroup (StatedSp n F) :=
  (signTuples F n).map
    ((equivStatedSp n F).toMonoidHom.comp (TauCeti.GLSymplecticFin.diagonal (m := n) (R := F)))

theorem mem_spSignGroup_iff {z : StatedSp n F} :
    z ∈ spSignGroup F n ↔ z ∈ spSignDiag F n := by
  constructor
  · rintro ⟨ε, hε, rfl⟩
    exact ⟨ε, hε, rfl⟩
  · rintro ⟨ε, hε, rfl⟩
    exact ⟨ε, hε, rfl⟩

theorem coe_spSignGroup : (spSignGroup F n : Set (StatedSp n F)) = spSignDiag F n :=
  Set.ext fun _ => mem_spSignGroup_iff

theorem longInv_mem_spSignGroup (h2 : (2 : F) ≠ 0) (k : Fin n) :
    longInv F n k ∈ spSignGroup F n := by
  classical
  rw [mem_spSignGroup_iff]
  refine ⟨fun j => if j = k then -1 else 1, fun j => ?_, ?_⟩
  · by_cases hj : j = k <;> simp [hj]
  · rw [equivStatedSp_diagonal_eq_stdInv _ (fun j => by by_cases hj : j = k <;> simp [hj]),
      ← stdInv_singleton]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hj : j = k
    · simp [hj]
    · have : (1 : Fˣ) ≠ -1 := fun h => h2 (by
        have := congrArg Units.val h
        simp only [Units.val_one, Units.val_neg] at this
        linear_combination this)
      simp [hj, this]

end SignGroup

section Frame

variable {p : ℕ} [Fact p.Prime] {n e : ℕ}

theorem pairFrame_psp (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSp n p e) :
    PairFrame (spSignGroup (GaloisField p e) n)
      (fundamentalSubgroups .PSp (modelUniv .PSp n p e Fact.out).D) := by
  have hn : 2 ≤ n := hadm.2.2.1
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ hx₂₁ hx₁₂
  obtain ⟨i₁, hi₁⟩ := (fund_iff_isLongRootSp2 hadm h2 R₁).1 hR₁
  obtain ⟨i₂, hi₂⟩ := (fund_iff_isLongRootSp2 hadm h2 R₂).1 hR₂
  have hone : ∀ g : StatedSp n (GaloisField p e),
      g⁻¹ * 1 * g ∈ spSignGroup (GaloisField p e) n := fun g => by
    rw [mul_one, inv_mul_cancel]
    exact (spSignGroup (GaloisField p e) n).one_mem
  have htoral : ∀ {R : Subgroup (StatedSp n (GaloisField p e))} {i : StatedSp n (GaloisField p e)},
      IsLongRootSp2 R i → ∃ g : StatedSp n (GaloisField p e),
        g⁻¹ * i * g ∈ spSignGroup (GaloisField p e) n := by
    rintro R i ⟨k, g, -, rfl⟩
    refine ⟨g, ?_⟩
    have : g⁻¹ * (g * longInv (GaloisField p e) n k * g⁻¹) * g =
        longInv (GaloisField p e) n k := by group
    rw [this]
    exact longInv_mem_spSignGroup h2 k
  rcases eq_one_or_eq_of_mem_center h2 hi₁ hc₁ hz₁ with h1 | h1
  · subst h1
    rcases eq_one_or_eq_of_mem_center h2 hi₂ hc₂ hz₂ with h1' | h1'
    · subst h1'
      exact ⟨1, hone 1, hone 1⟩
    · subst h1'
      obtain ⟨g, hg⟩ := htoral hi₂
      exact ⟨g, hone g, hg⟩
  rcases eq_one_or_eq_of_mem_center h2 hi₂ hc₂ hz₂ with h1' | h1'
  · subst h1'
    obtain ⟨g, hg⟩ := htoral hi₁
    rw [h1]
    exact ⟨g, hg, hone g⟩
  by_cases hii : i₁ = i₂
  · obtain ⟨g, hg⟩ := htoral hi₁
    rw [h1, h1', ← hii]
    exact ⟨g, hg, hg⟩
  have hcomm : Commute i₁ i₂ := by
    have hi₁mem : i₁ ∈ R₁ := (hi₁.isClassicalSL2 h2).mem
    rw [h1'] at hx₂₁
    exact (hx₂₁ i₁ hi₁mem).symm
  have horth : ∀ u ∈ minusSpace i₁, ∀ v ∈ minusSpace i₂, form u v = 0 := by
    rcases (hi₁.commute_iff_minusSpace h2 hi₂).1 hcomm with h | h
    · exact absurd (hi₁.eq_of_minusSpace_eq h2 hi₂ h) hii
    · exact h
  obtain ⟨u₁, w₁, huw₁, hP₁⟩ := hi₁.isHyperbolicPlane h2
  obtain ⟨u₂, w₂, huw₂, hP₂⟩ := hi₂.isHyperbolicPlane h2
  have hmem₁ : ∀ x ∈ ({u₁, w₁} : Set (Fin n ⊕ Fin n → GaloisField p e)), x ∈ minusSpace i₁ := by
    intro x hx
    rw [hP₁]
    exact Submodule.subset_span hx
  have hmem₂ : ∀ x ∈ ({u₂, w₂} : Set (Fin n ⊕ Fin n → GaloisField p e)), x ∈ minusSpace i₂ := by
    intro x hx
    rw [hP₂]
    exact Submodule.subset_span hx
  let k₀ : Fin n := ⟨0, by omega⟩
  let k₁ : Fin n := ⟨1, by omega⟩
  have hk : k₀ ≠ k₁ := fun h => by simpa [k₀, k₁] using congrArg Fin.val h
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := exists_sp_apply_eq_two_at hk u₁ w₁ u₂ w₂ huw₁ huw₂
    (horth _ (hmem₁ _ (by simp)) _ (hmem₂ _ (by simp)))
    (horth _ (hmem₁ _ (by simp)) _ (hmem₂ _ (by simp)))
    (horth _ (hmem₁ _ (by simp)) _ (hmem₂ _ (by simp)))
    (horth _ (hmem₁ _ (by simp)) _ (hmem₂ _ (by simp)))
  have e₁ : i₁ = g * longInv (GaloisField p e) n k₀ * g⁻¹ :=
    hi₁.eq_of_minusSpace_eq h2 ((isLongRootSp2_standard (K := GaloisField p e) k₀).conj g)
      (by rw [minusSpace_conj_eq h2 g k₀, hg₁, hg₂, hP₁])
  have e₂ : i₂ = g * longInv (GaloisField p e) n k₁ * g⁻¹ :=
    hi₂.eq_of_minusSpace_eq h2 ((isLongRootSp2_standard (K := GaloisField p e) k₁).conj g)
      (by rw [minusSpace_conj_eq h2 g k₁, hg₃, hg₄, hP₂])
  refine ⟨g, ?_, ?_⟩
  · rw [h1, e₁]
    have : g⁻¹ * (g * longInv (GaloisField p e) n k₀ * g⁻¹) * g =
        longInv (GaloisField p e) n k₀ := by group
    rw [this]
    exact longInv_mem_spSignGroup h2 k₀
  · rw [h1', e₂]
    have : g⁻¹ * (g * longInv (GaloisField p e) n k₁ * g⁻¹) * g =
        longInv (GaloisField p e) n k₁ := by group
    rw [this]
    exact longInv_mem_spSignGroup h2 k₁

end Frame

section Main

variable {p : ℕ} [Fact p.Prime] {n e : ℕ}

theorem simpleParam_sp (hn : 2 ≤ n) (F : Type) [Field F] :
    SimpleParam (Symplectic.rootDatum n F) F (Sp.x n F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Symplectic.rootDatum n F).isFiniteType rfl
  exact SimpleParam.of_chevalleyExtras (Sp.chevalleyExtras hn O _
    (Sp.commutatorFormula O))

theorem toralShortRootFact_spSignGroup (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) :
    ToralShortRootFact (Symplectic.rootDatum n (GaloisField p e)) (Sp.x n (GaloisField p e))
      (spSignGroup (GaloisField p e) n : Set (StatedSp n (GaloisField p e))) := by
  rw [coe_spSignGroup]
  exact toralShortRootFact_sp hp2 h5

theorem layerGenerationPairAt_psp (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp n p e) : LayerGenerationPairAt .PSp n p e Fact.out :=
  layerGenerationPairAt_of_toral (t := .PSp) trivial hadm hp2 h5
    (x := Sp.x n (GaloisField p e)) (simpleParam_sp hadm.2.2.1 (GaloisField p e))
    (spSignGroup (GaloisField p e) n)
    (toralShortRootFact_spSignGroup hp2 h5) (pairFrame_psp hp2 hadm)

end Main

end CFSG.ClassicalInvolution.Balance.Bootstrap
