module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.ChevalleyRootGroupsTorus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjRank
public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LieType.Steinberg.Minuscule.CertInputs

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg Module

section Weyl

variable {τ : Tag} {K : Type*} [Field K] [CharP K 2]

theorem weylElt_one_rootVec_char2 (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (weylElt τ K i 1 : Module.End K (RootModule τ K)) (rootVec τ K α) =
      rootVec τ K (reflect τ i α) := by
  rw [weylElt_rootVec i 1 hα]
  simp [CharTwo.neg_eq]

theorem wordReflect_isRoot (w : List ℕ) : ∀ {ν : Fin τ.rank → ℤ}, IsRoot τ ν →
    IsRoot τ (wordReflect τ w ν) := by
  induction w with
  | nil => intro ν h; exact h
  | cons i w ih => intro ν h; exact ih (IsRoot.reflect _ h)

theorem wordReflectInv_isRoot (w : List ℕ) : ∀ {ν : Fin τ.rank → ℤ}, IsRoot τ ν →
    IsRoot τ (wordReflectInv τ w ν) := by
  induction w with
  | nil => intro ν h; exact h
  | cons i w ih => intro ν h; exact IsRoot.reflect _ (ih h)

theorem wordReflectInv_wordReflect (w : List ℕ) :
    ∀ v : Fin τ.rank → ℤ, wordReflectInv τ w (wordReflect τ w v) = v := by
  induction w with
  | nil => intro v; rfl
  | cons i w ih =>
    intro v
    rw [wordReflect_cons, wordReflectInv_cons, ih, reflect_reflect]

theorem prodWeyl_rootVec (w : List ℕ) : ∀ {ν : Fin τ.rank → ℤ}, IsRoot τ ν →
    ((((w.map fun i => weylElt τ K (τ.idx i) 1).reverse).prod : (Module.End K (RootModule τ K))ˣ) :
        Module.End K (RootModule τ K)) (rootVec τ K ν) = rootVec τ K (wordReflect τ w ν) := by
  induction w with
  | nil => intro ν h; simp [wordReflect]
  | cons i w ih =>
    intro ν h
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, Units.val_mul,
      Module.End.mul_apply, weylElt_one_rootVec_char2 _ h, ih (IsRoot.reflect _ h), wordReflect_cons]

end Weyl

section Act

variable {K : Type*} [Field K] [CharP K 2] {τ : Tag}

theorem pinnedE_apply_weyl (γ : Fin τ.rank → ℤ) (x : RootModule τ K) :
    pinnedE τ K γ ((pinnedWeyl τ K γ : Module.End K (RootModule τ K)) x) =
      ((pinnedData τ γ).2.2 : K) • (pinnedWeyl τ K γ : Module.End K (RootModule τ K))
        (infE τ K (pinnedData τ γ).1 x) := by
  have h : ((pinnedWeyl τ K γ)⁻¹ : (Module.End K (RootModule τ K))ˣ).val
      ((pinnedWeyl τ K γ : Module.End K (RootModule τ K)) x) = x := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  unfold pinnedE
  simp only [LinearMap.smul_apply, Module.End.mul_apply]
  rw [h]

end Act

section StringsE6

theorem e6_two_aux : ∀ j : Fin Tag.E6.rank,
    List.zipWith (· + ·) (eL .E6 j) (eL .E6 j) ∉ Tag.E6.artifactRoots := by decide +kernel

theorem not_isRoot_two_single (j : Fin Tag.E6.rank) :
    ¬ IsRoot .E6 (Pi.single j 1 + Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  intro h
  rw [isRoot_iff_mem_artifactRoots, ← zipWith_add_ofFn'] at h
  exact e6_two_aux j h

theorem e6_sub_aux : ∀ j : Fin Tag.E6.rank, ∀ l ∈ Tag.E6.artifactRoots, l ≠ eL .E6 j →
    l ≠ nL .E6 j → List.zipWith (· + ·) l (eL .E6 j) ∈ Tag.E6.artifactRoots →
      List.zipWith (· - ·) l (eL .E6 j) ∉ Tag.E6.artifactRoots := by decide +kernel

theorem not_isRoot_sub_of_add (j : Fin Tag.E6.rank) {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (h1 : β ≠ Pi.single j 1) (h2 : β ≠ -Pi.single j 1) (h3 : IsRoot .E6 (β + Pi.single j 1)) :
    ¬ IsRoot .E6 (β - Pi.single j 1) := by
  intro h
  rw [isRoot_iff_mem_artifactRoots] at hβ h3 h
  rw [← zipWith_add_ofFn' (a := β) (b := Pi.single j 1)] at h3
  rw [← zipWith_sub_ofFn' (a := β) (b := Pi.single j 1)] at h
  exact e6_sub_aux j _ hβ (fun e => h1 (List.ofFn_injective e)) (fun e => h2 (List.ofFn_injective e))
    h3 h

end StringsE6

section SimpleOp

variable {K : Type*} [Field K] [CharP K 2]

theorem rootVec_ne_zero {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ K β ≠ 0 := by
  rw [rootVec_eq_single' hβ]
  exact Finsupp.single_ne_zero.2 one_ne_zero

theorem infE_rootVec_of_add_root (j : Fin Tag.E6.rank) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot .E6 β) (h3 : IsRoot .E6 (β + Pi.single j 1)) :
    infE .E6 K j (rootVec .E6 K β) = rootVec .E6 K (β + Pi.single j 1) := by
  have h1 : β ≠ Pi.single j 1 := by
    rintro rfl; exact not_isRoot_two_single j h3
  have h2 : β ≠ -Pi.single j 1 := by
    rintro rfl
    rw [neg_add_cancel] at h3
    exact h3.ne_zero rfl
  rw [infE_rootVec_of_ne j hβ h1 h2, stringDown_eq_zero hβ j h1 h2
    (not_isRoot_sub_of_add j hβ h1 h2 h3)]
  simp

theorem infE_rootVec_of_not (j : Fin Tag.E6.rank) {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot .E6 β) (h3 : ¬ IsRoot .E6 (β + Pi.single j 1))
    (h4 : β ≠ -Pi.single j 1) : infE .E6 K j (rootVec .E6 K β) = 0 := by
  by_cases h1 : β = Pi.single j 1
  · subst h1; exact infE_rootVec_single j
  · have h0 : rootVec .E6 K (β + Pi.single j 1) = 0 := by
      unfold rootVec; exact dite_eq_right h3
    rw [infE_rootVec_of_ne j hβ h1 h4, h0, smul_zero]

end SimpleOp

section ActE6

variable {K : Type*} [Field K] [CharP K 2]

theorem wordReflect_zero {τ : Tag} (w : List ℕ) : wordReflect τ w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [wordReflect_cons, ← reflectHom_apply, map_zero, ih]

theorem wordReflectInv_zero {τ : Tag} (w : List ℕ) : wordReflectInv τ w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wordReflectInv_cons, ih, ← reflectHom_apply, map_zero]

theorem pinned_sign_ne_zero (γ : Fin Tag.E6.rank → ℤ) :
    (((pinnedData .E6 γ).2.2 : ℤ) : K) ≠ 0 := by
  rcases pinnedSign_eq .E6 γ with h | h <;> rw [h] <;> simp

theorem pinnedE_rootVec_eq (γ μ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ) (hμ : IsRoot .E6 μ) :
    ∃ μ' : Fin Tag.E6.rank → ℤ, IsRoot .E6 μ' ∧
      wordReflect .E6 (pinnedData .E6 γ).2.1 (μ' + Pi.single (pinnedData .E6 γ).1 1) = μ + γ ∧
      pinnedE .E6 K γ (rootVec .E6 K μ) =
        (((pinnedData .E6 γ).2.2 : ℤ) : K) • (pinnedWeyl .E6 K γ : Module.End K (RootModule .E6 K))
          (infE .E6 K (pinnedData .E6 γ).1 (rootVec .E6 K μ')) := by
  set w := (pinnedData .E6 γ).2.1 with hw
  set j := (pinnedData .E6 γ).1 with hj
  have hfold : wordReflect .E6 w (Pi.single j 1) = γ := foldl_reflect_pinnedData hγ
  refine ⟨wordReflectInv .E6 w μ, wordReflectInv_isRoot w hμ, ?_, ?_⟩
  · rw [wordReflect_add, wordReflect_wordReflectInv, hfold]
  · have hW : (pinnedWeyl .E6 K γ : Module.End K (RootModule .E6 K))
        (rootVec .E6 K (wordReflectInv .E6 w μ)) = rootVec .E6 K μ := by
      have := prodWeyl_rootVec (K := K) w (wordReflectInv_isRoot w hμ)
      rw [wordReflect_wordReflectInv] at this
      exact this
    conv_lhs => rw [← hW]
    exact pinnedE_apply_weyl γ _

theorem pinnedE_rootVec_of_add_root (γ μ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ)
    (hμ : IsRoot .E6 μ) (h : IsRoot .E6 (γ + μ)) :
    ∃ s : K, s ≠ 0 ∧ pinnedE .E6 K γ (rootVec .E6 K μ) = s • rootVec .E6 K (γ + μ) := by
  obtain ⟨μ', hμ', hsum, he⟩ := pinnedE_rootVec_eq (K := K) γ μ hγ hμ
  set w := (pinnedData .E6 γ).2.1 with hw
  set j := (pinnedData .E6 γ).1 with hj
  have hroot : IsRoot .E6 (μ' + Pi.single j 1) := by
    have e : μ' + Pi.single j 1 = wordReflectInv .E6 w (μ + γ) := by
      rw [← hsum, wordReflectInv_wordReflect]
    rw [e]
    exact wordReflectInv_isRoot w (by rwa [add_comm])
  refine ⟨((pinnedData .E6 γ).2.2 : ℤ), pinned_sign_ne_zero γ, ?_⟩
  have hWp : (pinnedWeyl .E6 K γ : Module.End K (RootModule .E6 K))
      (rootVec .E6 K (μ' + Pi.single j 1)) =
        rootVec .E6 K (wordReflect .E6 w (μ' + Pi.single j 1)) := prodWeyl_rootVec w hroot
  rw [he, infE_rootVec_of_add_root j hμ' hroot, hWp, hsum, add_comm]

theorem pinnedE_rootVec_ne_zero_of_add_zero (γ μ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ)
    (hμ : IsRoot .E6 μ) (h : γ + μ = 0) : pinnedE .E6 K γ (rootVec .E6 K μ) ≠ 0 := by
  obtain ⟨μ', hμ', hsum, he⟩ := pinnedE_rootVec_eq (K := K) γ μ hγ hμ
  set w := (pinnedData .E6 γ).2.1 with hw
  set j := (pinnedData .E6 γ).1 with hj
  have h0 : μ' + Pi.single j 1 = 0 := by
    have e : μ' + Pi.single j 1 = wordReflectInv .E6 w (μ + γ) := by
      rw [← hsum, wordReflectInv_wordReflect]
    rw [e, add_comm, h, wordReflectInv_zero]
  have hneg : μ' = -Pi.single j 1 := eq_neg_of_add_eq_zero_left h0
  rw [he, hneg, infE_rootVec_neg_single]
  intro hz
  have h1 := (smul_eq_zero.1 hz).resolve_left (pinned_sign_ne_zero γ)
  have h2 : hVec .E6 K j = 0 := by
    have := congrArg (fun x => ((pinnedWeyl .E6 K γ)⁻¹ : (Module.End K (RootModule .E6 K))ˣ).val x) h1
    simp only [map_zero] at this
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel] at this
    exact this
  exact (Finsupp.single_ne_zero.2 (one_ne_zero (α := K))) h2

theorem pinnedE_rootVec_of_not (γ μ : Fin Tag.E6.rank → ℤ) (hγ : IsRoot .E6 γ)
    (hμ : IsRoot .E6 μ) (h1 : ¬ IsRoot .E6 (γ + μ)) (h2 : γ + μ ≠ 0) :
    pinnedE .E6 K γ (rootVec .E6 K μ) = 0 := by
  obtain ⟨μ', hμ', hsum, he⟩ := pinnedE_rootVec_eq (K := K) γ μ hγ hμ
  set w := (pinnedData .E6 γ).2.1 with hw
  set j := (pinnedData .E6 γ).1 with hj
  have hnr : ¬ IsRoot .E6 (μ' + Pi.single j 1) := fun hr => h1 (by
    rw [add_comm, ← hsum]; exact wordReflect_isRoot w hr)
  have hne : μ' ≠ -Pi.single j 1 := by
    rintro rfl
    apply h2
    rw [add_comm, ← hsum, neg_add_cancel, wordReflect_zero]
  rw [he, infE_rootVec_of_not j hμ' hnr hne, map_zero, smul_zero]

end ActE6

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
