module

public import CFSG.LieType.Steinberg.GradedUnipotent

public section

namespace CFSG.LieType.Universal.Spin.Twisted

open Matrix CFSG.LieType.Steinberg.Graded

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {R : Type*} [Field R] {ι : Type*}
  {Λ : Type*} (wt : κ → ι → ℤ) (f : (ι → ℤ) →+ ℤ) (root : Λ → ι → ℤ)
  (P : Λ → Matrix κ κ R → Prop)

omit [Fintype κ] in
theorem idBelow_of_shift
    (hshift : ∀ γ M, P γ M → ∀ a b, a ≠ b → M a b ≠ 0 →
      wt a - wt b = root γ ∨ wt a - wt b = 2 • root γ)
    (hdiag : ∀ γ M, P γ M → ∀ a, M a a = 1) {γ : Λ} (hpos : 0 < f (root γ)) {M : Matrix κ κ R}
    (hM : P γ M) : IdBelow (fun a => f (wt a)) (f (root γ)) M := by
  intro a b hab
  by_cases hab' : a = b
  · subst hab'
    rw [hdiag γ M hM, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hab']
    by_contra hne
    have hlev : f (wt a) - f (wt b) = f (wt a - wt b) := (map_sub f _ _).symm
    rcases hshift γ M hM a b hab' hne with h | h
    · simp only at hab
      rw [hlev, h] at hab
      exact lt_irrefl _ hab
    · simp only at hab
      rw [hlev, h, map_nsmul, two_nsmul] at hab
      omega

theorem eq_of_list_prod_eq_of_shift
    (hshift : ∀ γ M, P γ M → ∀ a b, a ≠ b → M a b ≠ 0 →
      wt a - wt b = root γ ∨ wt a - wt b = 2 • root γ)
    (hdiag : ∀ γ M, P γ M → ∀ a, M a a = 1)
    (hinj : ∀ γ M M', P γ M → P γ M' → (∀ a b, wt a - wt b = root γ → M a b = M' a b) → M = M')
    (hunit : ∀ γ M, P γ M → IsUnit M) :
    ∀ (L : List Λ), L.Nodup → (∀ γ ∈ L, ∀ δ ∈ L, root γ = root δ → γ = δ) →
      (∀ γ ∈ L, 0 < f (root γ)) → L.Pairwise (fun γ δ => f (root γ) ≤ f (root δ)) →
      ∀ M M' : Λ → Matrix κ κ R, (∀ γ ∈ L, P γ (M γ)) → (∀ γ ∈ L, P γ (M' γ)) →
      (L.map M).prod = (L.map M').prod → ∀ γ ∈ L, M γ = M' γ
  | [], _, _, _, _, _, _, _, _, _ => by simp
  | γ₀ :: L, hnd, hinjL, hpos, hsort, M, M', hM, hM', h => by
    rw [List.pairwise_cons] at hsort
    rw [List.nodup_cons] at hnd
    have h₀ := hpos γ₀ List.mem_cons_self
    have hall : ∀ N : Λ → Matrix κ κ R, (∀ γ ∈ γ₀ :: L, P γ (N γ)) →
        ∀ X ∈ ((γ₀ :: L).map N), IdBelow (fun a => f (wt a)) (f (root γ₀)) X := by
      intro N hN X hX
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hX
      refine (idBelow_of_shift wt f root P hshift hdiag (hpos γ hγ) (hN γ hγ)).mono ?_
      rcases List.mem_cons.1 hγ with rfl | hγ
      · exact le_rfl
      · exact hsort.1 γ hγ
    have hentry : ∀ N : Λ → Matrix κ κ R, (∀ γ ∈ γ₀ :: L, P γ (N γ)) →
        ∀ a b, wt a - wt b = root γ₀ → ((γ₀ :: L).map N).prod a b = N γ₀ a b := by
      intro N hN a b hab
      have hlev : f (wt a) - f (wt b) = f (root γ₀) := by rw [← map_sub, hab]
      have hne : a ≠ b := by
        rintro rfl
        rw [sub_self] at hlev
        omega
      rw [list_prod_apply_of_idBelow h₀ hne hlev.le (hall N hN), List.map_cons, List.map_cons,
        List.sum_cons, List.map_map, List.sum_eq_zero, add_zero]
      intro x hx
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hx
      by_contra hx0
      rcases hshift γ (N γ) (hN γ (List.mem_cons_of_mem _ hγ)) a b hne hx0 with h1 | h1
      · rw [hab] at h1
        exact hnd.1 ((hinjL γ₀ List.mem_cons_self γ (List.mem_cons_of_mem _ hγ) h1) ▸ hγ)
      · rw [hab] at h1
        have hγpos := hpos γ (List.mem_cons_of_mem _ hγ)
        have hle := hsort.1 γ hγ
        have : f (root γ₀) = f (root γ) + f (root γ) := by rw [h1, map_nsmul, two_nsmul]
        omega
    have heq : M γ₀ = M' γ₀ := hinj γ₀ _ _ (hM γ₀ List.mem_cons_self) (hM' γ₀ List.mem_cons_self)
      fun a b hab => (hentry M hM a b hab).symm.trans
        ((congrArg (fun X => X a b) h).trans (hentry M' hM' a b hab))
    intro γ hγ
    rcases List.mem_cons.1 hγ with rfl | hγ
    · exact heq
    · refine eq_of_list_prod_eq_of_shift hshift hdiag hinj hunit L hnd.2
        (fun γ hγ δ hδ => hinjL γ (List.mem_cons_of_mem _ hγ) δ (List.mem_cons_of_mem _ hδ))
        (fun γ hγ => hpos γ (List.mem_cons_of_mem _ hγ)) hsort.2 M M'
        (fun γ hγ => hM γ (List.mem_cons_of_mem _ hγ))
        (fun γ hγ => hM' γ (List.mem_cons_of_mem _ hγ)) ?_ γ hγ
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, heq] at h
      exact (hunit γ₀ _ (hM' γ₀ List.mem_cons_self)).mul_left_cancel h

end CFSG.LieType.Universal.Spin.Twisted
