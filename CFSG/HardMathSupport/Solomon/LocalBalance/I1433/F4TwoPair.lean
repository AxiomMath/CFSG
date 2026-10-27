module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

structure A2Pair (σ τ : Fin 3 → Fin 3 → V4) (κ κ' : ℤ) : Prop where
  kappa : (κ = 1 ∧ κ' = 2) ∨ (κ = 2 ∧ κ' = 1)
  σ_root : ∀ x y, x ≠ y → IsRoot Tag.F4 (σ x y)
  τ_root : ∀ x y, x ≠ y → IsRoot Tag.F4 (τ x y)
  σ_add : ∀ x y z, σ x y + σ y z = σ x z
  τ_add : ∀ x y z, τ x y + τ y z = τ x z
  σ_norm : ∀ x y, x ≠ y → ipF4 (σ x y) (σ x y) = 2 * κ
  τ_norm : ∀ x y, x ≠ y → ipF4 (τ x y) (τ x y) = 2 * κ'
  orth : ∀ x y x' y', x ≠ y → x' ≠ y' → ipF4 (σ x y) (τ x' y') = 0

namespace A2Pair

variable {σ τ : Fin 3 → Fin 3 → V4} {κ κ' : ℤ}

theorem symm (h : A2Pair σ τ κ κ') : A2Pair τ σ κ' κ where
  kappa := h.kappa.symm.imp (fun ⟨a, b⟩ => ⟨b, a⟩) (fun ⟨a, b⟩ => ⟨b, a⟩)
  σ_root := h.τ_root
  τ_root := h.σ_root
  σ_add := h.τ_add
  τ_add := h.σ_add
  σ_norm := h.τ_norm
  τ_norm := h.σ_norm
  orth x y x' y' hxy hxy' := by rw [ipF4_comm]; exact h.orth x' y' x y hxy' hxy

theorem σ_inner (h : A2Pair σ τ κ κ') : ipF4 (σ 0 1) (σ 1 2) = -κ := by
  have h02 := h.σ_norm 0 2 (by decide)
  have h01 := h.σ_norm 0 1 (by decide)
  have h12 := h.σ_norm 1 2 (by decide)
  rw [← h.σ_add 0 1 2, ipF4_add_left, ipF4_add_right, ipF4_add_right, ipF4_comm (σ 1 2) (σ 0 1),
    h01, h12] at h02
  linarith

theorem σ_self (h : A2Pair σ τ κ κ') (x : Fin 3) : σ x x = 0 := by
  have := h.σ_add x x x
  exact add_eq_right.1 this

theorem σ_neg (h : A2Pair σ τ κ κ') (x y : Fin 3) : σ y x = -σ x y := by
  have := h.σ_add x y x
  rw [h.σ_self] at this
  exact eq_neg_of_add_eq_zero_right this

end A2Pair


namespace A2Pair

variable {σ τ : Fin 3 → Fin 3 → V4} {κ κ' : ℤ}

theorem κ_ne_zero (h : A2Pair σ τ κ κ') : κ ≠ 0 := by
  rcases h.kappa with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

theorem comm (h : A2Pair σ τ κ κ') {L : Type} [Field L] :
    ∀ t ∈ frameRoots τ, ∀ x y : Fin 3, x ≠ y → ∀ c c' : L,
      Commute (pinnedX Tag.F4 L t c) (pinnedX Tag.F4 L (σ x y) c') := by
  rintro t ⟨i, j, hij, rfl⟩ x y hxy c c'
  refine commute_of_orth_diff (h.τ_root i j hij) (h.σ_root x y hxy) ?_ ?_ L _
    (Subgroup.subset_closure ⟨c, rfl⟩) _ (Subgroup.subset_closure ⟨c', rfl⟩)
  · rw [h.τ_norm i j hij, h.σ_norm x y hxy]
    rcases h.kappa with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  · rw [ipF4_comm]
    exact h.orth x y i j hxy hij

theorem exists_dec (h : A2Pair σ τ κ κ') (v : V4) :
    ∃ a b a' b' : ℤ, ipF4 v (σ 0 1) = κ * a ∧ ipF4 v (σ 1 2) = κ * b ∧
      ipF4 v (τ 0 1) = κ' * a' ∧ ipF4 v (τ 1 2) = κ' * b' ∧
      (3 : ℤ) • v = (2 * a + b) • σ 0 1 + (a + 2 * b) • σ 1 2 + (2 * a' + b') • τ 0 1 +
        (a' + 2 * b') • τ 1 2 :=
  exists_decomposition (h.kappa.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
    (h.kappa.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2))
    (h.σ_root 0 1 (by decide)) (h.σ_root 1 2 (by decide)) (h.τ_root 0 1 (by decide))
    (h.τ_root 1 2 (by decide)) (h.σ_norm 0 1 (by decide)) (h.σ_norm 1 2 (by decide)) h.σ_inner
    (h.τ_norm 0 1 (by decide)) (h.orth 0 1 0 1 (by decide) (by decide))
    (h.orth 1 2 0 1 (by decide) (by decide)) (h.τ_norm 1 2 (by decide)) h.symm.σ_inner
    (h.orth 0 1 1 2 (by decide) (by decide)) (h.orth 1 2 1 2 (by decide) (by decide)) v

theorem dvd01 (h : A2Pair σ τ κ κ') (v : V4) : ipF4 v (σ 0 1) = κ * lab1 σ κ v := by
  obtain ⟨a, b, a', b', h1, -, -, -, -⟩ := h.exists_dec v
  rw [lab1, h1, Int.mul_ediv_cancel_left _ h.κ_ne_zero]

theorem dvd12 (h : A2Pair σ τ κ κ') (v : V4) : ipF4 v (σ 1 2) = κ * lab2 σ κ v := by
  obtain ⟨a, b, a', b', -, h1, -, -, -⟩ := h.exists_dec v
  rw [lab2, h1, Int.mul_ediv_cancel_left _ h.κ_ne_zero]

theorem hdec (h : A2Pair σ τ κ κ') (v : V4) :
    ∃ t ∈ AddSubgroup.closure (frameRoots τ), (3 : ℤ) • v =
      (2 * lab1 σ κ v + lab2 σ κ v) • σ 0 1 + (lab1 σ κ v + 2 * lab2 σ κ v) • σ 1 2 + t := by
  obtain ⟨a, b, a', b', h1, h2, -, -, h5⟩ := h.exists_dec v
  have e1 : lab1 σ κ v = a := by rw [lab1, h1, Int.mul_ediv_cancel_left _ h.κ_ne_zero]
  have e2 : lab2 σ κ v = b := by rw [lab2, h2, Int.mul_ediv_cancel_left _ h.κ_ne_zero]
  refine ⟨(2 * a' + b') • τ 0 1 + (a' + 2 * b') • τ 1 2, ?_, ?_⟩
  · exact AddSubgroup.add_mem _
      (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure
        (show τ 0 1 ∈ frameRoots τ from ⟨0, 1, by decide, rfl⟩)) _)
      (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure
        (show τ 1 2 ∈ frameRoots τ from ⟨1, 2, by decide, rfl⟩)) _)
  · rw [e1, e2, h5]
    abel

theorem diag_chars {L : Type} [Field L] [IsAlgClosed L] {ψ : SL(3, L) →* ModGL Tag.F4 L}
    (h : A2Pair σ τ κ κ') (hψ : IsA2Frame ψ σ) {l : Fin 3 → Lˣ} {hl : l 0 * l 1 * l 2 = 1}
    {b : Fin Tag.F4.rank → Lˣ} (hb : ψ (diagSL3 l hl) = rootDiagUnit Tag.F4 b) (v : V4) :
    rootChar b v = l 0 ^ (lab1 σ κ v + lab2 σ κ v) * l 1 ^ lab2 σ κ v :=
  frame_diag_chars hψ (T := frameRoots τ)
    (fun t ⟨i, j, hij, ht⟩ => ht ▸ h.τ_root i j hij) h.comm h.hdec hb v

theorem commute_frames {L : Type} [Field L] (h : A2Pair σ τ κ κ')
    {ψ ψ' : SL(3, L) →* ModGL Tag.F4 L} (hψ : IsA2Frame ψ σ) (hψ' : IsA2Frame ψ' τ)
    (X Y : SL(3, L)) : ψ X * ψ' Y = ψ' Y * ψ X := by
  have hX : ψ X ∈ rootSpan Tag.F4 L (frameRoots σ) := by
    have h0 : ψ X ∈ ψ.range := ⟨X, rfl⟩
    rw [hψ.range] at h0
    exact h0
  have hY : ψ' Y ∈ rootSpan Tag.F4 L (frameRoots τ) := by
    have h0 : ψ' Y ∈ ψ'.range := ⟨Y, rfl⟩
    rw [hψ'.range] at h0
    exact h0
  refine (rootSpan_commute_of_orth_diff (S₁ := frameRoots σ) (S₂ := frameRoots τ)
    (fun γ ⟨i, j, hij, hγ⟩ => hγ ▸ h.σ_root i j hij) (fun γ ⟨i, j, hij, hγ⟩ => hγ ▸ h.τ_root i j hij)
    ?_ ?_ L (ψ X) hX (ψ' Y) hY).eq
  · rintro _ ⟨i, j, hij, rfl⟩ _ ⟨i', j', hij', rfl⟩
    rw [h.σ_norm i j hij, h.τ_norm i' j' hij']
    rcases h.kappa with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  · rintro _ ⟨i, j, hij, rfl⟩ _ ⟨i', j', hij', rfl⟩
    exact h.orth i j i' j' hij hij'

end A2Pair

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
