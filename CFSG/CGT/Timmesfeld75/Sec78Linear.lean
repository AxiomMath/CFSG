module

public import CFSG.CGT.Timmesfeld75.Sec77Transv

public section

namespace CFSG.CGT.Timmesfeld75

open Module Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F] {n : ℕ}

theorem exists_dual_indep_two {f : Dual F (Fin n → F)} {v ξ : Fin n → F} (hf : f ≠ 0)
    (hfv : f v = 0) (hfξ : f ξ = 0) (hvξ : ∀ r s : F, r • v + s • ξ = 0 → r = 0 ∧ s = 0)
    (hn : 4 ≤ n) :
    ∃ g : Dual F (Fin n → F), g v = 0 ∧ g ξ = 0 ∧
      ∀ r s : F, r • f + s • g = 0 → r = 0 ∧ s = 0 := by
  have hli : LinearIndependent F ![v, ξ] := LinearIndependent.pair_iff.2 hvξ
  have hS : finrank F (Submodule.span F (Set.range ![v, ξ])) = 2 := by
    simpa using finrank_span_eq_card hli
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span F (Set.range ![v, ξ]))
  have h3 : finrank F (Fin n → F) = n := by simp
  have hK : 2 ≤ finrank F (Submodule.span F (Set.range ![v, ξ])).dualAnnihilator := by omega
  have hfK : f ∈ (Submodule.span F (Set.range ![v, ξ])).dualAnnihilator := by
    have hle : Submodule.span F (Set.range ![v, ξ]) ≤ LinearMap.ker f := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · simpa using hfv
      · simpa using hfξ
    exact (Submodule.mem_dualAnnihilator f).2 fun w hw => by simpa using hle hw
  have hnot : ¬ (Submodule.span F (Set.range ![v, ξ])).dualAnnihilator ≤ Submodule.span F {f} := by
    intro hle
    have h4 := Submodule.finrank_mono hle
    have h5 : finrank F (Submodule.span F {f}) = 1 := finrank_span_singleton hf
    omega
  obtain ⟨g, hgK, hg⟩ := Set.not_subset.1 hnot
  have hgv : g v = 0 :=
    (Submodule.mem_dualAnnihilator _).1 hgK v (Submodule.subset_span ⟨0, by simp⟩)
  have hgξ : g ξ = 0 :=
    (Submodule.mem_dualAnnihilator _).1 hgK ξ (Submodule.subset_span ⟨1, by simp⟩)
  refine ⟨g, hgv, hgξ, fun r s hrs => ?_⟩
  by_cases hs : s = 0
  · subst hs
    rw [zero_smul, add_zero] at hrs
    exact ⟨(smul_eq_zero.1 hrs).resolve_right hf, rfl⟩
  · exfalso
    apply hg
    have : g = (-(s⁻¹ * r)) • f := by
      have h6 : s • g = -(r • f) := eq_neg_of_add_eq_zero_right hrs
      calc g = s⁻¹ • (s • g) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
        _ = s⁻¹ • (-(r • f)) := by rw [h6]
        _ = (-(s⁻¹ * r)) • f := by rw [smul_neg, smul_smul]; exact (neg_smul _ _).symm
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)

theorem exists_vec_eq_one_zero {V : Type*} [AddCommGroup V] [Module F V] {f f' : Dual F V}
    (hind : ∀ r s : F, r • f + s • f' = 0 → r = 0 ∧ s = 0) : ∃ p : V, f p = 1 ∧ f' p = 0 := by
  have hind' : ∀ r s : F, r • f + s • (f + f') = 0 → r = 0 ∧ s = 0 := by
    intro r s h
    have h2 : (r + s) • f + s • f' = 0 := by rw [add_smul, add_assoc, ← smul_add]; exact h
    obtain ⟨h3, h4⟩ := hind _ _ h2
    exact ⟨by rw [h4, add_zero] at h3; exact h3, h4⟩
  obtain ⟨p, hp1, hp2⟩ := exists_vec_eq_one hind'
  refine ⟨p, hp1, ?_⟩
  rw [LinearMap.add_apply, hp1] at hp2
  linear_combination hp2

theorem natCard_ker_pair [Finite F] {f f' : Dual F (Fin n → F)}
    (hind : ∀ r s : F, r • f + s • f' = 0 → r = 0 ∧ s = 0) :
    Nat.card {a : Fin n → F // f a = 0 ∧ f' a = 0} = Nat.card F ^ (n - 2) := by
  let φ : (Fin n → F) →ₗ[F] F × F := LinearMap.prod f f'
  have hind' : ∀ r s : F, r • f' + s • f = 0 → r = 0 ∧ s = 0 := by
    intro r s h
    have := hind s r (by rw [add_comm]; exact h)
    exact ⟨this.2, this.1⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨s, t⟩
    obtain ⟨p, hp1, hp2⟩ := exists_vec_eq_one_zero hind
    obtain ⟨p', hp1', hp2'⟩ := exists_vec_eq_one_zero hind'
    refine ⟨s • p + t • p', ?_⟩
    simp [φ, hp1, hp2, hp1', hp2']
  have hrk : finrank F (LinearMap.range φ) = 2 := by
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top]
    simp
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have h3 : finrank F (Fin n → F) = n := by simp
  have hker : finrank F (LinearMap.ker φ) = n - 2 := by omega
  have hcard : Nat.card (LinearMap.ker φ) = Nat.card F ^ (n - 2) := by
    rw [Module.natCard_eq_pow_finrank (K := F), hker]
  have e : {a : Fin n → F // f a = 0 ∧ f' a = 0} ≃ LinearMap.ker φ :=
    Equiv.subtypeEquivRight fun a => by simp [φ, LinearMap.mem_ker]
  rw [Nat.card_congr e]
  exact hcard

theorem apply_eq_mul_of_ker_le {V : Type*} [AddCommGroup V] [Module F V] {f f' : Dual F V}
    (hker : ∀ w, f w = 0 → f' w = 0) {w₀ : V} (hw₀ : f w₀ = 1) (w : V) :
    f' w = f w * f' w₀ := by
  have h1 : f (w - f w • w₀) = 0 := by
    rw [map_sub, map_smul, hw₀, smul_eq_mul, mul_one, sub_self]
  have h2 := hker _ h1
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h2
  exact h2

section Transv

variable {u₁ u₂ : SL(n, F)} {f₁ f₂ : Dual F (Fin n → F)} {a₁ a₂ : Fin n → F}

theorem transvection_comm_rel (h₁ : ∀ w, sact u₁ w = w + f₁ w • a₁)
    (h₂ : ∀ w, sact u₂ w = w + f₂ w • a₂) (hc : u₁ * u₂ = u₂ * u₁) (w : Fin n → F) :
    (f₂ w * f₁ a₂) • a₁ = (f₁ w * f₂ a₁) • a₂ := by
  have h := congrArg (fun g => sact g w) hc
  simp only [sact_mul] at h
  rw [h₂ w, h₁ (w + f₂ w • a₂), h₁ w, h₂ (w + f₁ w • a₁)] at h
  simp only [map_add, map_smul, smul_eq_mul] at h
  have key : (f₂ w * f₁ a₂) • a₁ + (w + f₂ w • a₂ + f₁ w • a₁) =
      (f₁ w * f₂ a₁) • a₂ + (w + f₂ w • a₂ + f₁ w • a₁) := by
    calc (f₂ w * f₁ a₂) • a₁ + (w + f₂ w • a₂ + f₁ w • a₁)
        = w + f₂ w • a₂ + (f₁ w + f₂ w * f₁ a₂) • a₁ := by rw [add_smul]; abel
      _ = w + f₁ w • a₁ + (f₂ w + f₁ w * f₂ a₁) • a₂ := h
      _ = (f₁ w * f₂ a₁) • a₂ + (w + f₂ w • a₂ + f₁ w • a₁) := by rw [add_smul]; abel
  exact add_right_cancel key

end Transv

end CFSG.CGT.Timmesfeld75
