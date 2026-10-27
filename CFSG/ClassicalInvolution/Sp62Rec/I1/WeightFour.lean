module

public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open Equiv CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem card_stab_weight_four :
    ∀ v : Fin 6 → ZMod 2, (Finset.univ.filter fun i => v i = 1).card = 4 →
      Fintype.card {σ : Perm (Fin 6) // ∀ i, v (σ.symm i) = v i} = 48 := by
  decide +kernel

private theorem card_even_vectors_six :
    Nat.card {v : Fin 6 → ZMod 2 // ∑ i, v i = 0} = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem odd_index_centralizer_vec (v : Fin 6 → ZMod 2)
    (hv : (Finset.univ.filter fun i => v i = 1).card = 4)
    (hmem : (⟨v, 1⟩ : Wr 6) ∈ Wsub) :
    Odd (Subgroup.centralizer ({(⟨⟨v, 1⟩, hmem⟩ : ↥Wsub)} : Set ↥Wsub)).index := by
  classical
  set x : ↥Wsub := ⟨⟨v, 1⟩, hmem⟩ with hx
  set C := Subgroup.centralizer ({x} : Set ↥Wsub) with hC
  have hxperm : (x : Wr 6).perm = 1 := rfl
  have hxvec : (x : Wr 6).vec = v := rfl
  have hCmem : ∀ w : ↥Wsub, w ∈ C ↔ ∀ i, v ((w : Wr 6).perm.symm i) = v i := by
    intro w
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h i
      have h1 := congrArg (fun a : ↥Wsub => (a : Wr 6).vec i) h
      simp only [Subgroup.coe_mul, Wr.mul_vec, hxperm, hxvec] at h1
      have hs : (Equiv.symm (1 : Perm (Fin 6))) i = i := rfl
      rw [hs] at h1
      have h2 : (w : Wr 6).vec i + v ((w : Wr 6).perm.symm i) = v i + (w : Wr 6).vec i := h1
      rw [add_comm (v i)] at h2
      exact add_left_cancel h2
    · intro h
      apply Subtype.ext
      refine Wr.ext (funext fun i => ?_) ?_
      · simp only [Subgroup.coe_mul, Wr.mul_vec, hxperm, hxvec]
        have hs : (Equiv.symm (1 : Perm (Fin 6))) i = i := rfl
        rw [h i, hs]
        exact add_comm _ _
      · simp [Wr.mul_perm, hxperm]
  let e : ↥C ≃ {v' : Fin 6 → ZMod 2 // ∑ i, v' i = 0} ×
      {σ : Perm (Fin 6) // ∀ i, v (σ.symm i) = v i} :=
    { toFun := fun w => (⟨(w.1 : Wr 6).vec, w.1.2⟩, ⟨(w.1 : Wr 6).perm, (hCmem w.1).mp w.2⟩)
      invFun := fun p => ⟨⟨⟨p.1.1, p.2.1⟩, p.1.2⟩, (hCmem _).mpr p.2.2⟩
      left_inv := fun w => rfl
      right_inv := fun p => rfl }
  have hcard : Nat.card ↥C = 1536 := by
    rw [Nat.card_congr e, Nat.card_prod, card_even_vectors_six, Nat.card_eq_fintype_card,
      card_stab_weight_four v hv]
  have h := Subgroup.card_mul_index C
  rw [hcard, card_Wsub] at h
  have hidx : C.index = 15 := by omega
  rw [hidx]
  exact ⟨7, by norm_num⟩

theorem card_support_zOf (ι : Fin 4 ↪ Fin 6) :
    (Finset.univ.filter fun i => (zOf ι).vec i = 1).card = 4 := by
  classical
  have h : (Finset.univ.filter fun i => (zOf ι).vec i = 1) = Finset.univ.map ι := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · intro hx
      by_cases hr : x ∈ Set.range ι
      · obtain ⟨i, rfl⟩ := hr
        exact ⟨i, rfl⟩
      · exfalso
        have h0 : (zOf ι).vec x = 0 := by
          show embedVec ι (zQ).vec x = 0
          exact embedVec_of_not_mem ι _ hr
        rw [h0] at hx
        exact zero_ne_one hx
    · rintro ⟨i, -, rfl⟩
      show embedVec ι (zQ).vec (ι i) = 1
      rw [embedVec_apply]
      revert i
      decide
  rw [h, card_map_univ]

theorem odd_index_centralizer_zOf (ι : Fin 4 ↪ Fin 6) (hmem : zOf ι ∈ Wsub) :
    Odd (Subgroup.centralizer ({(⟨zOf ι, hmem⟩ : ↥Wsub)} : Set ↥Wsub)).index := by
  have hz : zOf ι = (⟨(zOf ι).vec, 1⟩ : Wr 6) := Wr.ext rfl (zOf_perm ι)
  have hmem' : (⟨(zOf ι).vec, 1⟩ : Wr 6) ∈ Wsub := hz ▸ hmem
  have e : (⟨zOf ι, hmem⟩ : ↥Wsub) = ⟨⟨(zOf ι).vec, 1⟩, hmem'⟩ := Subtype.ext hz
  rw [e]
  exact odd_index_centralizer_vec (zOf ι).vec (card_support_zOf ι) hmem'

end CFSG.ClassicalInvolution.Sp62Rec.I1
