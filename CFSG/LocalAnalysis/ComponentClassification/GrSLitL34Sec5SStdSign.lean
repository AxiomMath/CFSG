module

public import CFSG.GH74.Generic.S45.LDiagPerm

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

attribute [local instance] Classical.decEq Fintype.ofFinite

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.Generic.S45
open scoped commutatorElement Pointwise

theorem sign_compPermHom_eq_neg_one {X : Type} [Group X] [Finite X] {t : X} (ht : t * t = 1)
    {A : Subgroup X} (hA : IsComponent A) (hne : conjSub t A ≠ A)
    (hfix : ∀ B : Subgroup X, IsComponent B → B ≠ A → B ≠ conjSub t A → conjSub t B = B) :
    Equiv.Perm.sign (compPermHom t) = -1 := by
  let a : Comp X := ⟨A, hA⟩
  let b : Comp X := ⟨conjSub t A, isComponent_conjSub hA t⟩
  have hab : a ≠ b := fun h => hne (by simpa using (congrArg Subtype.val h).symm)
  have hperm : compPermHom t = Equiv.swap a b := by
    refine Equiv.ext fun m => ?_
    by_cases hma : m = a
    · rw [hma, Equiv.swap_apply_left]
      apply Subtype.ext
      rfl
    · by_cases hmb : m = b
      · rw [hmb, Equiv.swap_apply_right]
        apply Subtype.ext
        show conjSub t (conjSub t A) = A
        rw [← conjSub_mul_comp, ht, conjSub_one_comp]
      · rw [Equiv.swap_apply_of_ne_of_ne hma hmb]
        apply Subtype.ext
        exact hfix m.1 m.2 (fun h => hma (Subtype.ext h))
          (fun h => hmb (Subtype.ext h))
  rw [hperm, Equiv.Perm.sign_swap hab]

theorem conjSub_eq_of_perfect_le_sup {X : Type} [Group X] [Finite X] {t : X} (ht : t * t = 1)
    {A K : Subgroup X} (hA : IsComponent A) (hne : conjSub t A ≠ A) (hKA : K ≤ A ⊔ conjSub t A)
    (hperf : ∀ L : Subgroup X, L ≤ centralizer ({t} : Set X) → ⁅L, L⁆ = L → L ≤ K)
    {B : Subgroup X} (hB : IsComponent B) (hBA : B ≠ A) (hBA' : B ≠ conjSub t A) :
    conjSub t B = B := by
  classical
  by_contra hBt
  have comm_of_isComponent_ne : ∀ {M N : Subgroup X}, IsComponent M → IsComponent N → M ≠ N →
      ∀ m ∈ M, ∀ n ∈ N, m * n = n * m := by
    intro M N hM hN hne m hm n hn
    rcases CFSG.LocalCores.distinct_components_commute hM hN with h | h
    · exact absurd h hne
    · have hc : ⁅m, n⁆ ∈ ⁅M, N⁆ := Subgroup.commutator_mem_commutator hm hn
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hinvol : ∀ M : Subgroup X, conjSub t (conjSub t M) = M := fun M => by
    rw [← conjSub_mul_comp, ht, conjSub_one_comp]
  have hBtA : conjSub t B ≠ A := by
    intro h
    apply hBA'
    have h2 := congrArg (conjSub t) h
    rwa [hinvol B] at h2
  have hBtAt : conjSub t B ≠ conjSub t A := by
    intro h
    apply hBA
    have h2 := congrArg (conjSub t) h
    rwa [hinvol B, hinvol A] at h2
  have hBne : conjSub t⁻¹ B ≠ B := by rw [htinv]; exact hBt
  have hAB : ⁅B, conjSub t⁻¹ B⁆ = ⊥ := commutator_conjSub_eq_bot (a := t) hB hBne
  have hcommBA := comm_of_isComponent_ne hB hA hBA
  have hcommBAt := comm_of_isComponent_ne hB (isComponent_conjSub hA t) hBA'
  have hcommBtA := comm_of_isComponent_ne (isComponent_conjSub hB t) hA hBtA
  have hcommBtAt :=
    comm_of_isComponent_ne (isComponent_conjSub hB t) (isComponent_conjSub hA t) hBtAt
  have hneA : conjSub t⁻¹ A ≠ A := by rw [htinv]; exact hne
  have hAB_A : ⁅A, conjSub t⁻¹ A⁆ = ⊥ := commutator_conjSub_eq_bot (a := t) hA hneA
  have hEcoe : ((A ⊔ conjSub t A : Subgroup X) : Set X) =
      (A : Set X) * (conjSub t A : Set X) := by
    have h := coe_sup_conjSub (A := A) (t := t) hAB_A
    rwa [htinv] at h
  let D : Subgroup X := (swapDiag (A := B) (t := t) hAB).range
  have hBq : CFSG.Assembly.IsQuasisimple B := assembly_isQuasisimple_of_isComponent hB
  have hDq : CFSG.Assembly.IsQuasisimple D :=
    isQuasisimple_range_swapDiag (A := B) (t := t) hAB hBq
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 ⟨hDq.1⟩
  have hDcent : D ≤ centralizer ({t} : Set X) := by
    intro d hd
    obtain ⟨b, rfl⟩ := hd
    exact swapDiag_mem_centralizer (A := B) (t := t) hAB htinv b
  have hDK : D ≤ K := hperf D hDcent hDperf
  have hDE : D ≤ A ⊔ conjSub t A := hDK.trans hKA
  have hDcommE : ∀ d ∈ D, ∀ e ∈ A ⊔ conjSub t A, d * e = e * d := by
    intro d hd e he
    obtain ⟨b, rfl⟩ := hd
    rw [← SetLike.mem_coe, hEcoe] at he
    obtain ⟨a, ha, a', ha', rfl⟩ := he
    rw [swapDiag_apply]
    have hb' : t⁻¹ * (b : X) * t ∈ conjSub t B := by simp [htinv]
    have h1 : Commute (b : X) a := hcommBA b b.2 a ha
    have h2 : Commute (b : X) a' := hcommBAt b b.2 a' ha'
    have h3 : Commute (t⁻¹ * (b : X) * t) a := hcommBtA _ hb' a ha
    have h4 : Commute (t⁻¹ * (b : X) * t) a' := hcommBtAt _ hb' a' ha'
    exact ((h1.mul_left h3).mul_right (h2.mul_left h4)).eq
  have hDcenE : D ≤ centralizer ((A ⊔ conjSub t A : Subgroup X) : Set X) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (hDcommE d hd e he).symm
  have hDab : ⁅D, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact mem_centralizer_iff.mp (hDcenE hx) y (hDE hy)
  have hDbot : D = ⊥ := by rw [← hDperf, hDab]
  have hDnt : Nontrivial D :=
    CFSG.LocalCores.isQuasisimple_nontrivial
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native D).1 hDq)
  exact (Subgroup.nontrivial_iff_ne_bot D).1 hDnt hDbot

end CFSG.ComponentClassification.GrSLit.L34Sec5S
