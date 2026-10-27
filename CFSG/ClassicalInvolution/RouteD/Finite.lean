module

public import CFSG.ClassicalInvolution.RouteD.Perp

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti CFSG.LieType.RootSystem

section Transport

variable {ι κ : Type}

theorem LeafPairM.of_equiv (e : ι ≃ κ) {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ}
    (hMN : ∀ x y, M x y = N (e x) (e y)) {ℓ b : ι} (h : LeafPairM M ℓ b) :
    LeafPairM N (e ℓ) (e b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun h => h1 (e.injective h), fun x hxℓ hxb => ?_, by rw [← hMN]; exact h3,
    by rw [← hMN]; exact h4⟩
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy1 : y ≠ ℓ := fun h => hxℓ (by rw [h])
  have hy2 : y ≠ b := fun h => hxb (by rw [h])
  have := h2 y hy1 hy2
  rw [hMN, hMN] at this
  exact this

theorem IsLongM.of_equiv (e : ι ≃ κ) {M : Matrix ι ι ℤ} {N : Matrix κ κ ℤ}
    (hMN : ∀ x y, M x y = N (e x) (e y)) {ℓ : ι} (h : IsLongM M ℓ) : IsLongM N (e ℓ) := by
  obtain ⟨d, hd0, hd, hmax⟩ := h
  refine ⟨fun z => d (e.symm z), fun z => hd0 _, fun z w => ?_, fun z => ?_⟩
  · have := hd (e.symm z) (e.symm w)
    rw [hMN, hMN] at this
    simpa using this
  · simpa using hmax (e.symm z)

end Transport

section Main

variable {B : Type} [Fintype B] [DecidableEq B]

theorem exists_perp_root_of_witness {Γ : Matrix B B ℤ} (hΓ : IsFiniteType Γ) {t : DynkinType}
    (e : B ≃ Fin t.rank) (he : ∀ x y, Γ x y = stdCartan t (e x) (e y)) {k β : B}
    (hw : PerpWitnessM (stdCartan t) (e k) (e β)) :
    ∃ r ∈ roots hΓ ∅, coroot Γ k r = 0 ∧ r β ≠ 0 := by
  obtain ⟨r, hr, h0, hne⟩ := hw
  refine ⟨r ∘ e, (RRoot.comp_equiv e he hr).mem_roots hΓ, ?_, hne⟩
  rw [coroot_apply, ← h0, ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [he]

theorem reverse_A (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n (Fin.rev i) (Fin.rev j) = CartanMatrix.A n i j := by
  unfold CartanMatrix.A
  simp only [Matrix.of_apply, Fin.val_rev, Fin.ext_iff]
  have hi := i.isLt
  have hj := j.isLt
  split_ifs <;> omega

theorem completion_finite {Γ : Matrix B B ℤ} (hΓ : IsFiniteType Γ)
    (hc : (diagramGraph Γ).Connected) {k β : B} (hleaf : LeafPairM Γ k β) (hlong : IsLongM Γ k)
    (hperp : ∀ r ∈ roots hΓ ∅, coroot Γ k r = 0 → r β = 0) :
    ∃ (m : ℕ) (e : B ≃ Fin (m + 2)), (∀ x y, Γ x y = CartanMatrix.A (m + 2) (e x) (e y)) ∧
      (e k).val = 0 ∧ (e β).val = 1 := by
  obtain ⟨t, ht, e, he⟩ := classify hΓ hc
  have hleaf' : LeafPair t (e k) (e β) := hleaf.of_equiv e he
  have hlong' : IsLongStd t (e k) := hlong.of_equiv e he
  have hcase := leafCase_of_leafPair hleaf' hlong'
  by_cases hA : ∀ n, t ≠ .A n
  · exfalso
    obtain ⟨r, hr, h0, hne⟩ :=
      exists_perp_root_of_witness hΓ e he (perpWitness_of_leafCase ht hA hcase)
    exact hne (hperp r hr h0)
  · push Not at hA
    obtain ⟨n, rfl⟩ := hA
    have hΓA : ∀ x y, Γ x y = CartanMatrix.A n (e x) (e y) := by
      intro x y
      rw [he x y, stdCartan_A n (e x) (e y)]
      exact congrFun (congrFun (CartanMatrix.A_transpose n) (e x)) (e y)
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h3 : (e β).val < n := (e β).isLt
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      exact ⟨m, e, hΓA, h1, h2⟩
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      refine ⟨m, e.trans Fin.revPerm, fun x y => ?_, ?_, ?_⟩
      · have h := hΓA x y
        rw [← reverse_A (m + 2) (e x) (e y)] at h
        exact h
      · have hr : (DynkinType.A (m + 2)).rank = m + 2 := rfl
        show (Fin.rev (e k)).val = 0
        rw [Fin.val_rev]
        omega
      · have hr : (DynkinType.A (m + 2)).rank = m + 2 := rfl
        show (Fin.rev (e β)).val = 1
        rw [Fin.val_rev]
        omega

end Main

end CFSG.ClassicalInvolution.RouteD
