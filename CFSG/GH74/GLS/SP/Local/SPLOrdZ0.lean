module

public import CFSG.GH74.GLS.SP.Local.SPLOrdG5
public import CFSG.GH74.GLS.SP.Local.SPLOrdCnt

public section

open Subgroup DihedralGroup

namespace CFSG.GH74.GLS.SP.Local

section Z0

variable {I : Type} [Group I]

theorem card_par_eq_zero {d : ℕ} [NeZero d] (hd : 2 ∣ d) :
    Nat.card {k : ZMod d // par hd k = 0} = d / 2 := by
  have h := OrdCnt.card_zmod_val_dvd (d := 2) (δ := d) (by norm_num) hd
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
  rw [par_eq_val_mod_two hd]
  omega

theorem card_Z0 [Finite I] (σ : MulAut I) (hσ : σ * σ = 1) {d : ℕ} [NeZero d] (hd : 2 ∣ d) :
    Nat.card ↥(Z0 σ hσ hd) = d / 2 + Nat.card {i : I // orderOf i = 2} := by
  set A' : Set (I ⋊[dihAct σ hσ hd] DihedralGroup d) :=
    (fun k : ZMod d => (⟨1, sr k⟩ : I ⋊[dihAct σ hσ hd] DihedralGroup d)) ''
      {k : ZMod d | par hd k = 0} with hA'
  set B' : Set (I ⋊[dihAct σ hσ hd] DihedralGroup d) :=
    (fun i : I => (⟨i, r ((d / 2 : ℕ) : ZMod d)⟩ : I ⋊[dihAct σ hσ hd] DihedralGroup d)) ''
      {i : I | i ≠ 1 ∧ i * i = 1} with hB'
  have hZ : Z0 σ hσ hd = A' ∪ B' := by
    ext x
    constructor
    · rintro (⟨k, hk, rfl⟩ | ⟨i, hi1, hii, rfl⟩)
      · exact Or.inl ⟨k, hk, rfl⟩
      · exact Or.inr ⟨i, ⟨hi1, hii⟩, rfl⟩
    · rintro (⟨k, hk, rfl⟩ | ⟨i, ⟨hi1, hii⟩, rfl⟩)
      · exact Or.inl ⟨k, hk, rfl⟩
      · exact Or.inr ⟨i, hi1, hii, rfl⟩
  have hinjA : Function.Injective
      (fun k : ZMod d => (⟨1, sr k⟩ : I ⋊[dihAct σ hσ hd] DihedralGroup d)) := by
    intro k k' h
    have := congrArg SemidirectProduct.right h
    simpa using this
  have hinjB : Function.Injective
      (fun i : I => (⟨i, r ((d / 2 : ℕ) : ZMod d)⟩ : I ⋊[dihAct σ hσ hd] DihedralGroup d)) := by
    intro i i' h
    have := congrArg SemidirectProduct.left h
    simpa using this
  have hdisj : Disjoint A' B' := by
    rw [Set.disjoint_left]
    rintro x ⟨k, -, rfl⟩ ⟨i, -, h⟩
    have := congrArg SemidirectProduct.right h
    simp at this
  have hfinA : A'.Finite := Set.Finite.image _ (Set.toFinite _)
  have hfinB : B'.Finite := Set.Finite.image _ (Set.toFinite _)
  have hA : A'.ncard = d / 2 := by
    rw [hA', Set.ncard_image_of_injective _ hinjA, ← Nat.card_coe_set_eq]
    exact card_par_eq_zero hd
  have hB : B'.ncard = Nat.card {i : I // orderOf i = 2} := by
    rw [hB', Set.ncard_image_of_injective _ hinjB, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
    rw [orderOf_eq_prime_iff, pow_two]
    exact and_comm
  rw [hZ, Nat.card_coe_set_eq, Set.ncard_union_eq hdisj hfinA hfinB, hA, hB]

end Z0

end CFSG.GH74.GLS.SP.Local
