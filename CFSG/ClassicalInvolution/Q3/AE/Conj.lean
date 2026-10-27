module

public import CFSG.ClassicalInvolution.Q3.AE.Bar
public import CFSG.ClassicalInvolution.Q3.AE.Models

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem conj_e0_kList : ∀ k ∈ kList, ofVec (vec4 [0]) * k * ofVec (vec4 [0]) ∈ kStarList := by
  decide +kernel

theorem conj_e0_kStarList :
    ∀ k ∈ kStarList, ofVec (vec4 [0]) * k * ofVec (vec4 [0]) ∈ kList := by
  decide +kernel

@[expose] def twinVec (ι : Fin 4 ↪ Fin n) (j : Fin n) : Wr n :=
  ofVec fun x => (if x = ι 0 then 1 else 0) + (if x = j then 1 else 0)

theorem twinVec_mul_self (ι : Fin 4 ↪ Fin n) (j : Fin n) : twinVec ι j * twinVec ι j = 1 := by
  refine Wr.ext (funext fun x => ?_) rfl
  rw [mul_vec]
  exact zmod_two_add_self _

theorem twinVec_conj_embed (ι : Fin 4 ↪ Fin n) {j : Fin n} (hj : j ∉ Set.range ι) (k : Wr 4) :
    twinVec ι j * embed ι k * twinVec ι j =
      embed ι (ofVec (vec4 [0]) * k * ofVec (vec4 [0])) := by
  classical
  refine Wr.ext (funext fun x => ?_) ?_
  · have e1 : (twinVec ι j * embed ι k * twinVec ι j).vec x =
        ((if x = ι 0 then 1 else 0) + (if x = j then 1 else 0)) + (embed ι k).vec x +
          ((if (embed ι k).perm.symm x = ι 0 then 1 else 0) +
            (if (embed ι k).perm.symm x = j then 1 else 0)) := rfl
    rw [e1, embed_vec, embed_vec]
    by_cases hx : x ∈ Set.range ι
    · obtain ⟨i, rfl⟩ := hx
      have hji : ι i ≠ j := fun h => hj ⟨i, h⟩
      rw [embedVec_apply, embed_perm, embedPerm_symm_apply, embedVec_apply]
      have hjs : ι (k.perm.symm i) ≠ j := fun h => hj ⟨_, h⟩
      have e2 : (ofVec (vec4 [0]) * k * ofVec (vec4 [0])).vec i =
          vec4 [0] i + k.vec i + vec4 [0] (k.perm.symm i) := rfl
      rw [e2]
      simp only [ι.injective.eq_iff, hji, hjs, ite_false, add_zero]
      simp [vec4]
    · have hx0 : x ≠ ι 0 := fun h => hx ⟨0, h.symm⟩
      rw [embedVec_of_not_mem ι _ hx, embed_perm, embedPerm_symm_of_not_mem ι _ hx,
        embedVec_of_not_mem ι _ hx]
      simp only [hx0, ite_false, zero_add, add_zero]
      exact zmod_two_add_self _
  · show (1 * (embed ι k).perm) * 1 = embedPerm ι ((1 * k.perm) * 1)
    simp only [one_mul, mul_one, embed_perm]

theorem twinVec_mem (ι : Fin 4 ↪ Fin n) {j : Fin n} (hj : j ∉ Set.range ι)
    (A : Subgroup (Equiv.Perm (Fin n))) : twinVec ι j ∈ aeSubOver A := by
  classical
  refine ⟨⟨?_, by simp [twinVec, ofVec]⟩, ?_⟩
  · unfold wsum twinVec ofVec
    have h0 : ι 0 ≠ j := fun h => hj ⟨0, h⟩
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    exact zmod_two_add_self _
  · show (permHom n) (twinVec ι j) ∈ A
    exact A.one_mem

theorem map_conj_memK (ι : Fin 4 ↪ Fin n) {j : Fin n} (hj : j ∉ Set.range ι) :
    (memK ι).map (MulAut.conj (twinVec ι j)).toMonoidHom = memKStar ι := by
  have hinv : (twinVec ι j)⁻¹ = twinVec ι j := inv_eq_of_mul_eq_one_right (twinVec_mul_self ι j)
  ext y
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    show twinVec ι j * embed ι k * (twinVec ι j)⁻¹ ∈ memKStar ι
    rw [hinv, twinVec_conj_embed ι hj]
    exact ⟨_, conj_e0_kList k hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk' := conj_e0_kStarList k hk
    refine ⟨embed ι (ofVec (vec4 [0]) * k * ofVec (vec4 [0])), ⟨_, hk', rfl⟩, ?_⟩
    show twinVec ι j * embed ι (ofVec (vec4 [0]) * k * ofVec (vec4 [0])) * (twinVec ι j)⁻¹ =
      embed ι k
    rw [hinv, twinVec_conj_embed ι hj]
    congr 1
    have h0 : ofVec (vec4 [0]) * ofVec (vec4 [0]) = (1 : Wr 4) := by decide
    calc ofVec (vec4 [0]) * (ofVec (vec4 [0]) * k * ofVec (vec4 [0])) * ofVec (vec4 [0])
        = (ofVec (vec4 [0]) * ofVec (vec4 [0])) * k * (ofVec (vec4 [0]) * ofVec (vec4 [0])) := by
          group
      _ = k := by rw [h0, one_mul, mul_one]

theorem exists_conj_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (h : α.card = 4)
    (A : Subgroup (Equiv.Perm (Fin n))) :
    ∃ w ∈ aeSubOver A, (memBar α h true).map (MulAut.conj (mkQ n w)).toMonoidHom =
      memBar α h false := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j ∉ α := by
    by_contra hcon
    push Not at hcon
    have : (Finset.univ : Finset (Fin n)) ⊆ α := fun x _ => hcon x
    have h1 := Finset.card_le_card this
    rw [Finset.card_univ, Fintype.card_fin, h] at h1
    omega
  have hj' : j ∉ Set.range (emb α h) := by
    rw [range_emb]
    exact hj
  refine ⟨twinVec (emb α h) j, twinVec_mem _ hj' A, ?_⟩
  show ((memK (emb α h)).map (mkQ n)).map
      (MulAut.conj (mkQ n (twinVec (emb α h) j))).toMonoidHom = (memKStar (emb α h)).map (mkQ n)
  rw [← map_conj_memK (emb α h) hj', Subgroup.map_map, Subgroup.map_map]
  congr 1

end CFSG.ClassicalInvolution.Q3.AE
