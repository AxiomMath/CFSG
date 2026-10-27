module

public import CFSG.ClassicalInvolution.Q3.AE.Members
public import Mathlib.GroupTheory.Perm.Sign

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {n : ℕ}

theorem allOnes_mul_self (n : ℕ) : allOnes n * allOnes n = 1 := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show (1 : ZMod 2) + 1 = 0
    decide
  · show (1 : Equiv.Perm (Fin n)) * 1 = 1
    rw [mul_one]

@[expose] def piSub (n : ℕ) : Subgroup (Wr n) where
  carrier := {a | a = 1 ∨ a = allOnes n}
  mul_mem' {a b} ha hb := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · left; rw [one_mul]
    · right; rw [one_mul]
    · right; rw [mul_one]
    · left; exact allOnes_mul_self n
  one_mem' := Or.inl rfl
  inv_mem' {a} ha := by
    rcases ha with rfl | rfl
    · left; rw [inv_one]
    · right
      rw [inv_eq_of_mul_eq_one_right (allOnes_mul_self n)]

theorem mem_piSub {a : Wr n} : a ∈ piSub n ↔ a = 1 ∨ a = allOnes n := Iff.rfl

instance piSub_normal : (piSub n).Normal where
  conj_mem a ha g := by
    rcases ha with rfl | rfl
    · left; group
    · right
      rw [← allOnes_comm g, mul_assoc, mul_inv_cancel, mul_one]

abbrev AEQ (n : ℕ) := Wr n ⧸ piSub n

abbrev mkQ (n : ℕ) : Wr n →* AEQ n := QuotientGroup.mk' (piSub n)

theorem mkQ_eq_iff {a b : Wr n} : mkQ n a = mkQ n b ↔ a⁻¹ * b = 1 ∨ a⁻¹ * b = allOnes n :=
  QuotientGroup.eq

theorem sum_perm_apply (σ : Equiv.Perm (Fin n)) (w : Fin n → ZMod 2) :
    ∑ i, w (σ.symm i) = ∑ i, w i :=
  Equiv.sum_comp σ.symm w

theorem wsum_mul (a b : Wr n) : wsum (a * b) = wsum a + wsum b := by
  unfold wsum
  simp only [mul_vec, Finset.sum_add_distrib, sum_perm_apply]

theorem wsum_one : wsum (1 : Wr n) = 0 := by
  unfold wsum
  simp [one_vec]

theorem wsum_inv (a : Wr n) : wsum a⁻¹ = wsum a := by
  unfold wsum
  simp only [inv_vec]
  exact Equiv.sum_comp a.perm a.vec

@[expose] def aeSub (n : ℕ) : Subgroup (Wr n) where
  carrier := {a | wsum a = 0 ∧ Equiv.Perm.sign a.perm = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [wsum_mul, ha.1, hb.1, add_zero]
    · rw [mul_perm, Equiv.Perm.sign_mul, ha.2, hb.2, mul_one]
  one_mem' := ⟨wsum_one, by rw [one_perm, Equiv.Perm.sign_one]⟩
  inv_mem' {a} ha := ⟨by rw [wsum_inv]; exact ha.1, by rw [inv_perm, Equiv.Perm.sign_inv]; exact ha.2⟩

theorem mem_aeSub {a : Wr n} : a ∈ aeSub n ↔ wsum a = 0 ∧ Equiv.Perm.sign a.perm = 1 := Iff.rfl

theorem kList_even : ∀ a ∈ kList, (∑ i, a.vec i) = 0 ∧ Equiv.Perm.sign a.perm = 1 := by
  decide +kernel

theorem kStarList_even : ∀ a ∈ kStarList, (∑ i, a.vec i) = 0 ∧ Equiv.Perm.sign a.perm = 1 := by
  decide +kernel

theorem yQ_even : (∑ i, yQ.vec i) = 0 ∧ Equiv.Perm.sign yQ.perm = 1 := by
  decide +kernel

theorem sum_embedVec (ι : Fin 4 ↪ Fin n) (v : Fin 4 → ZMod 2) :
    ∑ x, embedVec ι v x = ∑ i, v i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ι))]
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => embedVec_apply ι v i
  · intro x _ hx
    apply embedVec_of_not_mem
    rintro ⟨i, rfl⟩
    exact hx (Finset.mem_map_of_mem ι (Finset.mem_univ i))

theorem embed_mem_aeSub (ι : Fin 4 ↪ Fin n) {a : Wr 4}
    (h : (∑ i, a.vec i) = 0 ∧ Equiv.Perm.sign a.perm = 1) : embed ι a ∈ aeSub n := by
  classical
  refine ⟨?_, ?_⟩
  · unfold wsum
    rw [embed_vec, sum_embedVec]
    exact h.1
  · rw [embed_perm]
    unfold embedPerm
    rw [Equiv.Perm.sign_extendDomain]
    exact h.2

theorem memK_le_aeSub (ι : Fin 4 ↪ Fin n) : memK ι ≤ aeSub n := by
  rintro _ ⟨a, ha, rfl⟩
  exact embed_mem_aeSub ι (kList_even a ha)

theorem memKStar_le_aeSub (ι : Fin 4 ↪ Fin n) : memKStar ι ≤ aeSub n := by
  rintro _ ⟨a, ha, rfl⟩
  exact embed_mem_aeSub ι (kStarList_even a ha)

theorem yOf_mem_aeSub (ι : Fin 4 ↪ Fin n) : yOf ι ∈ aeSub n :=
  embed_mem_aeSub ι yQ_even

@[expose] noncomputable def emb (α : Finset (Fin n)) (h : α.card = 4) : Fin 4 ↪ Fin n :=
  (α.orderEmbOfFin h).toEmbedding

theorem range_emb (α : Finset (Fin n)) (h : α.card = 4) :
    Set.range (emb α h) = (α : Set (Fin n)) :=
  Finset.range_orderEmbOfFin α h

theorem zOf_inv (ι : Fin 4 ↪ Fin n) : (zOf ι)⁻¹ = zOf ι := by
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [inv_vec, zOf_perm]
    rfl
  · rw [inv_perm, zOf_perm, inv_one]

theorem range_eq_finset (ι : Fin 4 ↪ Fin n) :
    Set.range ι = ((Finset.univ.map ι : Finset (Fin n)) : Set (Fin n)) := by
  ext x
  simp

theorem card_map_univ (ι : Fin 4 ↪ Fin n) : (Finset.univ.map ι).card = 4 := by
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem range_eq_of_subset {ι κ : Fin 4 ↪ Fin n} (h : Set.range ι ⊆ Set.range κ) :
    Set.range ι = Set.range κ := by
  classical
  rw [range_eq_finset, range_eq_finset] at h ⊢
  have h' : Finset.univ.map ι ⊆ Finset.univ.map κ := by exact_mod_cast h
  rw [Finset.eq_of_subset_of_card_le h' (by rw [card_map_univ, card_map_univ])]

theorem range_eq_of_mkQ_zOf_eq (hn8 : n ≠ 8) {ι κ : Fin 4 ↪ Fin n}
    (h : mkQ n (zOf ι) = mkQ n (zOf κ)) : Set.range ι = Set.range κ := by
  classical
  rcases mkQ_eq_iff.mp h with h1 | h1
  · exact range_eq_of_zOf_eq (inv_mul_eq_one.mp h1)
  · exfalso
    apply hn8
    have hv : ∀ x, (zOf ι).vec x + (zOf κ).vec x = 1 := by
      intro x
      have h2 := congrFun (congrArg Wr.vec h1) x
      rw [mul_vec, zOf_inv, zOf_perm] at h2
      exact h2
    have hx : ∀ x, x ∈ Set.range ι ↔ x ∉ Set.range κ := by
      intro x
      have h3 := hv x
      rw [zOf_vec_apply, zOf_vec_apply] at h3
      by_cases h4 : x ∈ Set.range ι <;> by_cases h5 : x ∈ Set.range κ <;>
        simp only [h4, h5, ite_true, ite_false] at h3 <;> first
          | exact absurd h3 (by decide) | simp [h4, h5]
    have hdisj : Disjoint (Finset.univ.map ι) (Finset.univ.map κ) := by
      rw [Finset.disjoint_left]
      intro x hxι hxκ
      have h6 : x ∈ Set.range ι := by rw [range_eq_finset]; exact_mod_cast hxι
      have h7 : x ∈ Set.range κ := by rw [range_eq_finset]; exact_mod_cast hxκ
      exact (hx x).mp h6 h7
    have hunion : Finset.univ.map ι ∪ Finset.univ.map κ = Finset.univ := by
      ext x
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases h6 : x ∈ Set.range ι
      · left
        rw [range_eq_finset] at h6
        exact_mod_cast h6
      · right
        have h7 : x ∈ Set.range κ := by
          by_contra h8
          exact h6 ((hx x).mpr h8)
        rw [range_eq_finset] at h7
        exact_mod_cast h7
    have h9 := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin, card_map_univ, card_map_univ] at h9
    exact h9

theorem comm_or_of_mkQ_comm {a b : Wr n} (h : mkQ n a * mkQ n b = mkQ n b * mkQ n a) :
    a * b = b * a ∨ a * b = b * a * allOnes n := by
  rw [← map_mul, ← map_mul] at h
  rcases mkQ_eq_iff.mp h with h1 | h1
  · left
    exact inv_mul_eq_one.mp h1
  · right
    have h2 : b * a = a * b * allOnes n := by rw [← h1]; group
    calc a * b = b * a * (allOnes n)⁻¹ := by rw [h2]; group
      _ = b * a * allOnes n := by rw [inv_eq_of_mul_eq_one_right (allOnes_mul_self n)]

theorem not_comm_mkQ_zOf_memK {ι κ : Fin 4 ↪ Fin n}
    (hne : (Set.range ι ∩ Set.range κ).Nonempty) (hneq : Set.range ι ≠ Set.range κ) :
    ∃ b ∈ memK κ, mkQ n (zOf ι) * mkQ n b ≠ mkQ n b * mkQ n (zOf ι) := by
  classical
  have hκι : ¬ Set.range κ ⊆ Set.range ι := fun h => hneq (range_eq_of_subset h).symm
  have hικ : ¬ Set.range ι ⊆ Set.range κ := fun h => hneq (range_eq_of_subset h)
  obtain ⟨b, hb, hzb⟩ := not_comm_zOf_memK hne hκι
  obtain ⟨x, hxι, hxκ⟩ := Set.not_subset.mp hικ
  refine ⟨b, hb, fun h => ?_⟩
  rcases comm_or_of_mkQ_comm h with h1 | h1
  · exact hzb h1
  · have hbs := supportedOn_of_mem_memK κ hb
    have h2 := congrFun (congrArg Wr.vec h1) x
    rw [mul_vec, mul_vec, mul_vec, zOf_perm, mul_perm] at h2
    have hbx : b.vec x = 0 := (hbs x hxκ).1
    have hbpx : b.perm.symm x = x := hbs.perm_symm hxκ
    have h3 : (1 : Equiv.Perm (Fin n)).symm x = x := rfl
    rw [h3, hbx, hbpx] at h2
    have h5 : (allOnes n).vec ((b.perm * (zOf ι).perm).symm x) = 1 := rfl
    rw [h5, add_zero, zero_add] at h2
    have h6 : (zOf ι).vec x + 1 = (zOf ι).vec x + 0 := by rw [add_zero]; exact h2.symm
    exact absurd (add_left_cancel h6) (by decide)

theorem not_comm_mkQ_zOf_memKStar {ι κ : Fin 4 ↪ Fin n}
    (hne : (Set.range ι ∩ Set.range κ).Nonempty) (hneq : Set.range ι ≠ Set.range κ) :
    ∃ b ∈ memKStar κ, mkQ n (zOf ι) * mkQ n b ≠ mkQ n b * mkQ n (zOf ι) := by
  classical
  have hκι : ¬ Set.range κ ⊆ Set.range ι := fun h => hneq (range_eq_of_subset h).symm
  have hικ : ¬ Set.range ι ⊆ Set.range κ := fun h => hneq (range_eq_of_subset h)
  obtain ⟨b, hb, hzb⟩ := not_comm_zOf_memKStar hne hκι
  obtain ⟨x, hxι, hxκ⟩ := Set.not_subset.mp hικ
  refine ⟨b, hb, fun h => ?_⟩
  rcases comm_or_of_mkQ_comm h with h1 | h1
  · exact hzb h1
  · have hbs := supportedOn_of_mem_memKStar κ hb
    have h2 := congrFun (congrArg Wr.vec h1) x
    rw [mul_vec, mul_vec, mul_vec, zOf_perm, mul_perm] at h2
    have hbx : b.vec x = 0 := (hbs x hxκ).1
    have hbpx : b.perm.symm x = x := hbs.perm_symm hxκ
    have h3 : (1 : Equiv.Perm (Fin n)).symm x = x := rfl
    rw [h3, hbx, hbpx] at h2
    have h5 : (allOnes n).vec ((b.perm * (zOf ι).perm).symm x) = 1 := rfl
    rw [h5, add_zero, zero_add] at h2
    have h6 : (zOf ι).vec x + 1 = (zOf ι).vec x + 0 := by rw [add_zero]; exact h2.symm
    exact absurd (add_left_cancel h6) (by decide)

end CFSG.ClassicalInvolution.Q3.AE
