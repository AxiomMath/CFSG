module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverAlg

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.RankThree.Asc83Table Subgroup

@[expose] def F0 {X : Type*} [Group X] (k : Fin 6 → X) : Subgroup X :=
  Subgroup.closure (Set.range (xB k))

section F0

variable {X : Type*} [Group X] {k : Fin 6 → X}

theorem evalW_conj (t : X) (u : List (Fin 6 × Bool)) :
    evalW (fun i => t * k i * t⁻¹) u = t * evalW k u * t⁻¹ := by
  have := map_evalW (MulAut.conj t) k u
  simpa [MulAut.conj_apply] using this.symm

theorem J3Pkg.conj (h : J3Pkg k) (t : X) : J3Pkg (fun i => t * k i * t⁻¹) where
  eqs u hu := by rw [evalW_conj, h.eqs u hu]; group
  moves u hu h1 := by
    rw [evalW_conj] at h1
    exact h.moves u hu (by
      have : t * evalW k u * t⁻¹ = t * 1 * t⁻¹ := by rw [h1]; group
      simpa using this)
  zc := by
    rw [evalW_conj]
    have := h.comm_zeta t
    rw [this, mul_inv_cancel_right]
    exact h.zc

theorem xB_conj (t : X) (i : Fin 4) :
    xB (fun j => t * k j * t⁻¹) i = t * xB k i * t⁻¹ := by
  fin_cases i <;> simp [xB, evalW_conj]

theorem F0_conj (t : X) : F0 (fun j => t * k j * t⁻¹) = (F0 k).map (MulAut.conj t).toMonoidHom := by
  unfold F0
  rw [MonoidHom.map_closure, ← Set.range_comp]
  congr 2
  funext i
  simp [xB_conj, MulAut.conj_apply]

theorem basisProd_mem_closure {n : ℕ} {x : Fin n → X} (hx : ∀ i, x i ^ 3 = 1)
    (hc : ∀ i j, Commute (x i) (x j)) (a : Fin n → ZMod 3) :
    basisProd x a ∈ Subgroup.closure (Set.range x) := by
  have := coe_basisHom hx hc (Multiplicative.ofAdd a)
  rw [toAdd_ofAdd] at this
  rw [← this]
  exact Subtype.mem _

theorem isElementaryAbelian_closure_n {n : ℕ} {x : Fin n → X} (hx : ∀ i, x i ^ 3 = 1)
    (hc : ∀ i j, Commute (x i) (x j)) : IsElementaryAbelian 3 (Subgroup.closure (Set.range x)) := by
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range x)) :=
    isMulCommutative_closure (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _; exact hc i j)
  have hab : ∀ a ∈ Subgroup.closure (Set.range x), ∀ b ∈ Subgroup.closure (Set.range x),
      a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : Subgroup.closure (Set.range x)) ⟨b, hb⟩)
  rw [isElementaryAbelian_iff]
  refine ⟨hab, fun a ha => ?_⟩
  induction ha using closure_induction with
  | mem _ h =>
    obtain ⟨i, rfl⟩ := h
    exact hx i
  | one => exact one_pow 3
  | mul a b ha hb h₁ h₂ => rw [(show Commute a b from hab a ha b hb).mul_pow, h₁, h₂, one_mul]
  | inv a _ h => rw [inv_pow, h, inv_one]

namespace J3Pkg

variable (h : J3Pkg k)
include h

theorem card_F0 : Nat.card (F0 k) = 81 := by
  rw [F0, card_closure_basis h.x_pow h.x_comm h.basisProd_injective]
  norm_num

theorem isElementaryAbelian_F0 : IsElementaryAbelian 3 (F0 k) :=
  isElementaryAbelian_closure_n h.x_pow h.x_comm

theorem act_mem_F0 (i : Fin 6) (j : Fin 4) : k i * xB k j * (k i)⁻¹ ∈ F0 k := by
  rw [h.act]
  exact basisProd_mem_closure h.x_pow h.x_comm _

theorem k_mem_normalizer [Finite X] (i : Fin 6) : k i ∈ normalizer (F0 k : Set X) := by
  have : Finite (Subgroup.closure (Set.range (xB k))) := inferInstance
  refine mem_normalizer_closure_of_conj_mem (S := Set.range (xB k)) ?_
  rintro _ ⟨j, rfl⟩
  exact h.act_mem_F0 i j

theorem closure_le_normalizer [Finite X] :
    Subgroup.closure (Set.range k) ≤ normalizer (F0 k : Set X) := by
  rw [closure_le]
  rintro _ ⟨i, rfl⟩
  exact h.k_mem_normalizer i

theorem xB_mem_F0 (j : Fin 4) : xB k j ∈ F0 k := subset_closure ⟨j, rfl⟩

end J3Pkg

end F0

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
