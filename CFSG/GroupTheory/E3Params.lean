module

public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin

section Module

variable {W : Type} [CommGroup W]

theorem aSet_aParam_nonempty [Finite W] {X : Subgroup (MulAut W)}
    (h : 0 < E3.aParam X) : (E3.aSet (E3.aParam X) X).Nonempty := by
  rw [E3.aParam] at h
  split_ifs at h with he
  · have hne : {k : ℕ | 0 < k ∧ (E3.aSet k X).Nonempty}.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, csSup_empty] at h
      exact lt_irrefl 0 h
    have hmem : sSup {k : ℕ | 0 < k ∧ (E3.aSet k X).Nonempty} ∈
        {k : ℕ | 0 < k ∧ (E3.aSet k X).Nonempty} :=
      Nat.sSup_mem hne (E3.aSet_bddAbove X)
    rw [E3.aParam, if_pos he]
    exact hmem.2
  · exact absurd h (lt_irrefl 0)

end Module

theorem mQuot_top_eq_rkIdx {W : Type} [CommGroup W] [Finite W] (S : Subgroup W) :
    E3.mQuot ⊤ S = rkIdx S := by
  unfold E3.mQuot rkIdx
  rw [Subgroup.relIndex_top_right]

theorem exists_mQuot_two_of_mem_aSet_two {W : Type} [CommGroup W] [Finite W]
    {X A : Subgroup (MulAut W)} (hA : A ∈ E3.aSet 2 X) (ha : E3.aParam X = 2) :
    ∃ C : Subgroup (MulAut W), C ≤ A ∧ E3.mQuot A C = 2 ∧ fixV C ≠ fixV A := by
  classical
  have hAX : A ≤ X := hA.1
  have hAne : A ≠ ⊥ := hA.2.1
  have hAel : IsElemAbelian2 A := hA.2.2.1
  have hAprop : ∀ C : Subgroup (MulAut W), C ≤ A → E3.mQuot A C < 2 → fixV C = fixV A :=
    hA.2.2.2
  have hnot3 : A ∉ E3.aSet 3 X := by
    intro h3
    have hle : 3 ≤ E3.aParam X := E3.le_aParam_of_mem_aSet (by norm_num) h3
    omega
  have hex : ∃ C : Subgroup (MulAut W), C ≤ A ∧ E3.mQuot A C < 3 ∧ fixV C ≠ fixV A := by
    by_contra hcon
    refine hnot3 ⟨hAX, hAne, hAel, fun C hC hlt => ?_⟩
    by_contra hne
    exact hcon ⟨C, hC, hlt, hne⟩
  obtain ⟨C, hCA, hlt, hfix⟩ := hex
  refine ⟨C, hCA, ?_, hfix⟩
  have hcases : E3.mQuot A C = 0 ∨ E3.mQuot A C = 1 ∨ E3.mQuot A C = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    have hCeq : C = A :=
      (E3.mQuot_eq_zero_iff (CFSG.Quasithin.E3.isPGroup_of_isElemAbelian2 hAel) hCA).1 h0
    exact hfix (by rw [hCeq])
  · exfalso
    exact hfix (hAprop C hCA (by omega))
  · exact h2

section Group

variable {G : Type} [Group G] [Finite G]

theorem mQuot_le_one_of_coset_cover {W K : Subgroup G} (hW : IsPGroup 2 W) (hKW : K ≤ W)
    {u : G} (h : ∀ w ∈ W, w ∈ K ∨ u⁻¹ * w ∈ K) : E3.mQuot W K ≤ 1 := by
  classical
  have hcover : (W : Set G) ⊆
      (K : Set G) ∪ (fun k : G => u * k) '' (K : Set G) := by
    intro w hw
    rcases h w hw with hk | hk
    · exact Or.inl hk
    · exact Or.inr ⟨u⁻¹ * w, hk, by group⟩
  have hcardle : (W : Set G).ncard ≤ 2 * (K : Set G).ncard := by
    have h1 : (W : Set G).ncard ≤
        ((K : Set G) ∪ (fun k : G => u * k) '' (K : Set G)).ncard :=
      Set.ncard_le_ncard hcover (Set.toFinite _)
    have h2 := Set.ncard_union_le (K : Set G)
      ((fun k : G => u * k) '' (K : Set G))
    have h3 := Set.ncard_image_le (s := (K : Set G)) (f := fun k : G => u * k)
      (Set.toFinite _)
    omega
  have hcard : Nat.card ↥W ≤ 2 * Nat.card ↥K := by
    have hWn : Nat.card ↥W = (W : Set G).ncard := (Nat.card_coe_set_eq (W : Set G)).symm
    have hKn : Nat.card ↥K = (K : Set G).ncard := (Nat.card_coe_set_eq (K : Set G)).symm
    omega
  have hmul := Subgroup.relIndex_mul_card (H := K) (K := W)
  rw [inf_eq_left.2 hKW] at hmul
  have hrel : K.relIndex W ≤ 2 := by
    have hle : K.relIndex W * Nat.card ↥K ≤ 2 * Nat.card ↥K := by
      rw [hmul]
      exact hcard
    exact Nat.le_of_mul_le_mul_right hle Nat.card_pos
  have hpoweq := CFSG.Quasithin.E3.relIndex_eq_two_pow hW K
  rw [hpoweq] at hrel
  have hpow : 2 ^ E3.mQuot W K ≤ 2 ^ 1 := by simpa using hrel
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hpow

end Group

end CFSG.GroupTheory
