module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCommV

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

private theorem dih_exists_zpowers {V : Type} [CommGroup V] [Finite V] {S : Subgroup V}
    (hS : Nat.card S = 2) : ∃ u : V, u ∈ S ∧ u ≠ 1 ∧ S = Subgroup.zpowers u := by
  have hne : S ≠ ⊥ := by
    rintro rfl
    simp at hS
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  refine ⟨u, hu, hu1', (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu) ?_).symm⟩
  rw [Nat.card_zpowers, hS]
  have hpos : 0 < orderOf u := orderOf_pos u
  have : orderOf u ≠ 1 := fun h => hu1' (orderOf_eq_one_iff.mp h)
  omega

private theorem dih_five_le_card {V : Type} [Group V] [Finite V] {W : Subgroup V} (x : Fin 4 → V)
    (hm : ∀ i, x i ∈ W) (h1 : ∀ i, x i ≠ 1) (hinj : Function.Injective x) :
    5 ≤ Nat.card W := by
  have hinj' : Function.Injective
      (Fin.cons (⟨1, W.one_mem⟩ : W) (fun i => (⟨x i, hm i⟩ : W)) : Fin 5 → W) := by
    rw [Fin.cons_injective_iff]
    refine ⟨?_, fun i j h => hinj (congrArg Subtype.val h)⟩
    rintro ⟨i, hi⟩
    exact h1 i (congrArg Subtype.val hi)
  simpa using Nat.card_le_card_of_injective _ hinj'

theorem orderOf_mul_le_three {V : Type} [CommGroup V] [Finite V] {𝒞 : Set (MulAut V)}
    {a b : MulAut V} (ha : a ∈ 𝒞) (hb : b ∈ 𝒞) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hconj : ∀ c ∈ 𝒞, ∀ g ∈ Subgroup.closure ({a, b} : Set (MulAut V)), g * c * g⁻¹ ∈ 𝒞)
    (hcard : ∀ c ∈ 𝒞, Nat.card ↥(commV (Subgroup.zpowers c)) = 2)
    (hdist : ∀ c ∈ 𝒞, ∀ c' ∈ 𝒞, c ≠ c' →
      commV (Subgroup.zpowers c) ≠ commV (Subgroup.zpowers c')) :
    orderOf (a * b) ≤ 3 := by
  by_contra hk
  replace hk := not_le.mp hk
  have haa : a * a = 1 := by rwa [← pow_two]
  have hbb : b * b = 1 := by rwa [← pow_two]
  have hinv : (a * b)⁻¹ * a = a * (a * b) := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right hbb, mul_assoc,
      haa, mul_one, ← mul_assoc, haa, one_mul]
  have hgmem : (a * b)⁻¹ ∈ Subgroup.closure ({a, b} : Set (MulAut V)) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hr : ∀ i : ℕ, a * (a * b) ^ i ∈ 𝒞 ∧ a * (a * b) ^ (i + 1) ∈ 𝒞 := by
    intro i
    induction i with
    | zero =>
      refine ⟨by simpa using ha, ?_⟩
      have : a * (a * b) ^ (0 + 1) = b := by simp [← mul_assoc, haa]
      rw [this]; exact hb
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := hconj _ ih.1 _ hgmem
      have e : (a * b)⁻¹ * (a * (a * b) ^ n) * (a * b)⁻¹⁻¹ = a * (a * b) ^ (n + 1 + 1) := by
        rw [inv_inv, ← mul_assoc (a * b)⁻¹ a ((a * b) ^ n), hinv, pow_succ (a * b) (n + 1),
          pow_succ' (a * b) n]
        simp only [mul_assoc]
      rwa [e] at h
  have hne : ∀ i j : ℕ, i < orderOf (a * b) → j < orderOf (a * b) → i ≠ j →
      a * (a * b) ^ i ≠ a * (a * b) ^ j := fun i j hi hj hij h =>
    hij (pow_injOn_Iio_orderOf hi hj (mul_left_cancel h))
  choose u hu1 hu2 hu3 using fun i : ℕ => dih_exists_zpowers (hcard _ (hr i).1)
  have hu_ne : ∀ i j : ℕ, i < orderOf (a * b) → j < orderOf (a * b) → i ≠ j → u i ≠ u j := by
    intro i j hi hj hij h
    apply hdist _ (hr i).1 _ (hr j).1 (hne i j hi hj hij)
    rw [hu3 i, hu3 j, h]
  have hW : ∀ i : ℕ, u i ∈ commV (Subgroup.zpowers a) ⊔ commV (Subgroup.zpowers b) := by
    intro i
    have hab : a * b ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
    have h1 : Subgroup.zpowers (a * (a * b) ^ i) ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
        (Subgroup.pow_mem _ hab i)
    exact commV_sup_le _ _ (commV_mono h1 (hu1 i))
  have hWcard : Nat.card (commV (Subgroup.zpowers a) ⊔ commV (Subgroup.zpowers b) :
      Subgroup V) ≤ 4 := by
    have hsurj : Function.Surjective
        (fun p : commV (Subgroup.zpowers a) × commV (Subgroup.zpowers b) =>
          (⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
            (commV (Subgroup.zpowers a) ⊔ commV (Subgroup.zpowers b) : Subgroup V))) := by
      rintro ⟨x, hx⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
      exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rwa [Nat.card_prod, hcard a ha, hcard b hb] at this
  have h5 := dih_five_le_card (W := commV (Subgroup.zpowers a) ⊔ commV (Subgroup.zpowers b))
    (fun i : Fin 4 => u i) (fun i => hW i) (fun i => hu2 i) (fun i j h => Fin.ext (by
      by_contra hij
      have hi := i.2
      have hj := j.2
      exact hu_ne i j (by omega) (by omega) hij h))
  omega

end CFSG.CGT.PushingUpLit.CGT6
