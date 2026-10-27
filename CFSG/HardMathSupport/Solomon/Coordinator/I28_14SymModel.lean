module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymComb
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
public import Mathlib.Algebra.Module.StablyFree.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.ComponentClassification.OutcomeLocal Module

structure SymModel (m : ℕ) (H : Type) [AddCommGroup H] [Module (ZMod 2) H] where
  ψ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) H
  γ : sumZero m →ₗ[ZMod 2] H
  surj : Function.Surjective γ
  equivariant : ∀ (σ : Equiv.Perm (Fin m)) (y : sumZero m),
    (ψ σ : H →ₗ[ZMod 2] H) (γ y) = γ (sumZeroEquiv σ y)
  ker_const : ∀ y : sumZero m, γ y = 0 → ∃ c : ZMod 2, (y : Fin m → ZMod 2) = fun _ => c
  inj : Function.Injective ψ

variable {m : ℕ} {H : Type} [AddCommGroup H] [Module (ZMod 2) H]

@[expose] def SymModel.full (hm : 5 ≤ m) : SymModel m (sumZero m) where
  ψ := sumZeroRep m
  γ := LinearMap.id
  surj := Function.surjective_id
  equivariant _ _ := rfl
  ker_const y hy := ⟨0, by
    have : y = 0 := hy
    rw [this]; rfl⟩
  inj := mclt_sumZeroRep_injective hm

@[expose] def SymModel.heart (hm : 5 ≤ m) : SymModel m (sumZero m ⧸ onesLine m) where
  ψ := heartRep m
  γ := (onesLine m).mkQ
  surj := Submodule.mkQ_surjective _
  equivariant _ _ := rfl
  ker_const _ hy := mem_onesLine.mp ((Submodule.Quotient.mk_eq_zero _).mp hy)
  inj := mclt_heartRep_injective hm

variable (M : SymModel m H)

theorem SymModel.apply_gamma (σ : Equiv.Perm (Fin m)) (y : sumZero m) :
    (M.ψ σ : H →ₗ[ZMod 2] H) (M.γ y) = M.γ (sumZeroEquiv σ y) :=
  M.equivariant σ y

theorem i28_14_symModel_center_ne (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    M.γ (pairVec i j) ≠ 0 := by
  intro h
  obtain ⟨c, hc⟩ := M.ker_const _ h
  obtain ⟨k, hk⟩ := mclt_exists_notMem {i, j} (lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have h1 := congrFun hc i
  have h2 := congrFun hc k
  simp [coe_pairVec, hij, hk.1, hk.2] at h1 h2
  rw [← h1] at h2
  exact absurd h2 (by decide)

theorem i28_14_symModel_swap_apply (i j : Fin m) (y : sumZero m) :
    sumZeroEquiv (Equiv.swap i j) y =
      y + ((y : Fin m → ZMod 2) i + (y : Fin m → ZMod 2) j) • pairVec i j :=
  Subtype.ext (by
    rw [coe_sumZeroEquiv, permCoord_swap]
    rfl)

theorem i28_14_symModel_swap_tv (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    ∃ (φ : Dual (ZMod 2) H) (h : φ (M.γ (pairVec i j)) = 0), φ ≠ 0 ∧
      (∀ y : sumZero m, φ (M.γ y) = (y : Fin m → ZMod 2) i + (y : Fin m → ZMod 2) j) ∧
      M.ψ (Equiv.swap i j) = tv φ (M.γ (pairVec i j)) h := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective M.γ
    (LinearMap.range_eq_top.mpr M.surj)
  let ℓ : sumZero m →ₗ[ZMod 2] ZMod 2 :=
    ((LinearMap.proj i : (Fin m → ZMod 2) →ₗ[ZMod 2] ZMod 2) + LinearMap.proj j) ∘ₗ (sumZero m).subtype
  have hℓ : ∀ y : sumZero m, ℓ y = (y : Fin m → ZMod 2) i + (y : Fin m → ZMod 2) j := fun y => rfl
  let φ : Dual (ZMod 2) H := ℓ ∘ₗ s
  have hφ : ∀ y : sumZero m, φ (M.γ y) = (y : Fin m → ZMod 2) i + (y : Fin m → ZMod 2) j := by
    intro y
    have h0 : M.γ (s (M.γ y) + y) = 0 := by
      rw [map_add]
      have : M.γ (s (M.γ y)) = M.γ y := by
        have := congrArg (fun f : H →ₗ[ZMod 2] H => f (M.γ y)) hs
        exact this
      rw [this, zmod2_add_self]
    obtain ⟨c, hc⟩ := M.ker_const _ h0
    have h1 := congrFun hc i
    have h2 := congrFun hc j
    simp only [Submodule.coe_add, Pi.add_apply] at h1 h2
    change ℓ (s (M.γ y)) = _
    rw [hℓ]
    have key : ∀ a b c d e : ZMod 2, a + c = e → b + d = e → a + b = c + d := by decide
    exact key _ _ _ _ _ h1 h2
  have ha : φ (M.γ (pairVec i j)) = 0 := by
    rw [hφ]
    simp [coe_pairVec, hij]
    decide
  refine ⟨φ, ha, ?_, hφ, ?_⟩
  · obtain ⟨k, hk⟩ := mclt_exists_notMem {i, j} (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    intro h0
    have := hφ (pairVec i k)
    rw [h0] at this
    simp [coe_pairVec, hij, hk.2, Ne.symm hk.1] at this
  · apply tv_ext
    intro v
    obtain ⟨y, rfl⟩ := M.surj v
    rw [tv_apply, hφ, M.apply_gamma, i28_14_symModel_swap_apply, map_add, map_smul]

theorem i28_14_symModel_swap_isTv (hm : 3 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    IsF2Transvection (M.ψ (Equiv.swap i j)) := by
  obtain ⟨φ, h, hφ, -, heq⟩ := i28_14_symModel_swap_tv M hm hij
  exact (isF2Transvection_iff _).mpr ⟨φ, _, h, hφ, i28_14_symModel_center_ne M hm hij, heq⟩

theorem i28_14_symModel_swap_of_transv (hm : 5 ≤ m) {σ : Equiv.Perm (Fin m)}
    (h : IsF2Transvection (M.ψ σ)) : ∃ i j : Fin m, i ≠ j ∧ σ = Equiv.swap i j := by
  have hσ : σ ≠ 1 := fun h1 => h.1 (by rw [h1, map_one])
  obtain ⟨φ, a, ha, -, -, hts⟩ := (isF2Transvection_iff _).mp h
  apply i28_14_sym_swap_of_Q hm hσ
  have hw : ∀ y : sumZero m, M.γ (sumZeroEquiv σ y + y) = φ (M.γ y) • a := by
    intro y
    rw [map_add, ← M.apply_gamma, hts, tv_apply, add_right_comm, zmod2_add_self, zero_add]
  have toC : ∀ y : sumZero m, φ (M.γ y) = 0 →
      ∃ c : ZMod 2, permCoord σ (y : Fin m → ZMod 2) + (y : Fin m → ZMod 2) = fun _ => c := by
    intro y hy
    obtain ⟨c, hc⟩ := M.ker_const _ (by rw [hw, hy, zero_smul])
    exact ⟨c, by simpa [coe_sumZeroEquiv] using hc⟩
  intro y₁ y₂
  rcases zmod2_eq_zero_or_one (φ (M.γ y₁)) with h1 | h1
  · exact Or.inl (toC y₁ h1)
  rcases zmod2_eq_zero_or_one (φ (M.γ y₂)) with h2 | h2
  · exact Or.inr (Or.inl (toC y₂ h2))
  refine Or.inr (Or.inr ?_)
  obtain ⟨c, hc⟩ := M.ker_const (sumZeroEquiv σ y₁ + y₁ + (sumZeroEquiv σ y₂ + y₂)) (by
    rw [map_add, hw, hw, h1, h2, one_smul, zmod2_add_self])
  exact ⟨c, by simpa [coe_sumZeroEquiv] using hc⟩

end CFSG.HardMathSupport.Solomon.Coordinator
