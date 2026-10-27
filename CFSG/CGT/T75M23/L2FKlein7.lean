module

public import CFSG.CGT.T75M23.L2FTab7

public section

namespace CFSG.CGT.T75M23

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def KleinFact7 : Prop :=
  ∀ c : N7, c * c = 1 → c * bm0 = bm0 * c → (∀ k < 16, c ≠ n7 (tw7 k)) →
    (∀ k < 16, bm0 * c ≠ n7 (tw7 k)) → c ≠ bm0 →
    (∀ y : N7, (y * bm0 = bm0 * y ∨ y * c = c * y ∨ y * (bm0 * c) = bm0 * c * y) →
      y * bm0 * y⁻¹ ∈ ({1, bm0, c, bm0 * c} : Set N7) ∧
      y * c * y⁻¹ ∈ ({1, bm0, c, bm0 * c} : Set N7) ∧
      y⁻¹ * bm0 * y ∈ ({1, bm0, c, bm0 * c} : Set N7) ∧
      y⁻¹ * c * y ∈ ({1, bm0, c, bm0 * c} : Set N7)) →
    ∃ n : N7, n * bm0 * n⁻¹ ∈ ({1, bm0, c, bm0 * c} : Set N7) ∧
      n * bm1 * n⁻¹ ∈ ({1, bm0, c, bm0 * c} : Set N7)

section Klein



theorem genTab7_isTab (i : Fin 6) (b : Bool) : IsTab7 (genTab7 i.val b) (n7 [(i, b)]) := by
  have : (Fin.ofNat 6 i.val : Fin 6) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  rw [genTab7, this]
  exact IsTab7.ofWord _

theorem genTab7_isTab_inv (i : Fin 6) (b : Bool) :
    IsTab7 (genTab7 i.val (!b)) (n7 [(i, b)])⁻¹ := by
  have := genTab7_isTab i (!b)
  have e : n7 [(i, !b)] = (n7 [(i, b)])⁻¹ := n7_invWord [(i, b)]
  rwa [e] at this

theorem conj_gen_mem (ht : tCheck7 = true) (hn : normalCheck7 = true) (i : Fin 6) (b : Bool)
    {t : N7} (htT : t ∈ n7T) : n7 [(i, b)] * t * (n7 [(i, b)])⁻¹ ∈ n7T := by
  obtain ⟨k, hk, rfl⟩ := (mem_n7T_iff ht t).1 htT
  simp only [normalCheck7, List.all_eq_true, List.mem_range] at hn
  have h2 := hn i.val i.isLt (n7Tab (tw7 k)) (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
  rw [Bool.and_eq_true] at h2
  have hx := IsTab7.conj (genTab7_isTab i b) (genTab7_isTab_inv i b) (IsTab7.ofWord (tw7 k))
  cases b
  · exact (tTabs7_contains_iff ht hx).1 h2.2
  · exact (tTabs7_contains_iff ht hx).1 h2.1

theorem n7T_normal_word (ht : tCheck7 = true) (hn : normalCheck7 = true) :
    ∀ (w : Word6) (t : N7), t ∈ n7T → n7 w * t * (n7 w)⁻¹ ∈ n7T := by
  intro w
  induction w with
  | nil => intro t htT; simpa [n7_nil] using htT
  | cons p w ih =>
    intro t htT
    obtain ⟨i, b⟩ := p
    have h2 := conj_gen_mem ht hn i b (ih t htT)
    have e : n7 ((i, b) :: w) = n7 [(i, b)] * n7 w := by
      rw [← n7_append]
      rfl
    have e2 : n7 [(i, b)] * n7 w * t * (n7 [(i, b)] * n7 w)⁻¹ =
        n7 [(i, b)] * (n7 w * t * (n7 w)⁻¹) * (n7 [(i, b)])⁻¹ := by group
    rw [e, e2]
    exact h2

theorem n7T_normal (ht : tCheck7 = true) (hn : normalCheck7 = true) (n t : N7) (htT : t ∈ n7T) :
    n * t * n⁻¹ ∈ n7T := by
  obtain ⟨w, rfl⟩ := n7_exists_word n
  exact n7T_normal_word ht hn w t htT

theorem map_conj_n7T (ht : tCheck7 = true) (hn : normalCheck7 = true) (n : N7) :
    n7T.map (MulAut.conj n).toMonoidHom = n7T := by
  apply le_antisymm
  · rintro _ ⟨t, htT, rfl⟩
    exact n7T_normal ht hn n t htT
  · intro t htT
    refine ⟨n⁻¹ * t * n, ?_, ?_⟩
    · simpa using n7T_normal ht hn n⁻¹ t htT
    · simp [MulAut.conj_apply, mul_assoc]

theorem klein_class7_of_checks (ht : tCheck7 = true) (hb : bCheck7 = true)
    (hn : normalCheck7 = true) (hk : KleinFact7) (B' : Subgroup N7) (hb0 : bm0 ∈ B')
    (hexp : ∀ x ∈ B', x * x = 1) (hcard : Nat.card B' = 4) (hbot : B' ⊓ n7T = ⊥)
    (hcent : ∀ b ∈ B', b ≠ 1 → ∀ y : N7, y * b = b * y →
      y ∈ Subgroup.normalizer (B' : Set N7)) :
    ∃ ι : N7 ≃* N7, n7T.map ι.toMonoidHom = n7T ∧ n7B.map ι.toMonoidHom = B' := by
  obtain ⟨hsq0, -, -, hne0, -, -, -, -, -, -⟩ := bFacts7 hb ht
  obtain ⟨c, hcB, hc1, hcb⟩ : ∃ c ∈ B', c ≠ 1 ∧ c ≠ bm0 := by
    by_contra hcon
    push Not at hcon
    have hsub : (B' : Set N7) ⊆ {1, bm0} := by
      intro y hy
      by_cases h1 : y = 1
      · simp [h1]
      · simp [hcon y hy h1]
    have h2 : (B' : Set N7).ncard ≤ 2 := by
      refine (Set.ncard_le_ncard hsub).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have h3 : (B' : Set N7).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hcard
    omega
  have hcc : c * c = 1 := hexp c hcB
  have hbcB : bm0 * c ∈ B' := B'.mul_mem hb0 hcB
  have hcomm_c : c * bm0 = bm0 * c := by
    have h1 : (c * bm0)⁻¹ = c * bm0 := inv_eq_of_mul_eq_one_right (hexp _ (B'.mul_mem hcB hb0))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hcc, inv_eq_of_mul_eq_one_right hsq0] at h1
    exact h1.symm
  have hbc1 : bm0 * c ≠ 1 := by
    intro h
    apply hcb
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hsq0]
  have hnT : ∀ y ∈ B', y ≠ 1 → y ∉ n7T := by
    intro y hy hy1 hyT
    have : y ∈ B' ⊓ n7T := ⟨hy, hyT⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hy1 this
  have hcT : c ∉ n7T := hnT c hcB hc1
  have hbcT : bm0 * c ∉ n7T := hnT _ hbcB hbc1
  have hbc_ne_b : bm0 * c ≠ bm0 := by
    intro h
    apply hc1
    simpa using h
  have hbc_ne_c : bm0 * c ≠ c := by
    intro h
    apply hne0
    simpa using h
  have hsub : ({1, bm0, c, bm0 * c} : Set N7) ⊆ (B' : Set N7) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact B'.one_mem
    · exact hb0
    · exact hcB
    · exact hbcB
  have hB'eq : (B' : Set N7) = {1, bm0, c, bm0 * c} := by
    have h4 : ({1, bm0, c, bm0 * c} : Set N7).ncard = 4 :=
      ncard_four7 hne0.symm hc1.symm hbc1.symm hcb.symm hbc_ne_b.symm hbc_ne_c.symm
    have h5 : (B' : Set N7).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hcard
    exact (Set.eq_of_subset_of_ncard_le hsub (by omega)).symm
  have hmemS : ∀ y : N7, y ∈ B' ↔ y ∈ ({1, bm0, c, bm0 * c} : Set N7) := by
    intro y
    rw [← hB'eq, SetLike.mem_coe]
  have hB' : ∀ y ∈ B', y = 1 ∨ y = bm0 ∨ y = c ∨ y = bm0 * c := by
    intro y hy
    have := (hmemS y).1 hy
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hcT' : ∀ k < 16, c ≠ n7 (tw7 k) := by
    intro k _ h
    exact hcT (by rw [h]; exact n7_tw_mem k)
  have hbcT' : ∀ k < 16, bm0 * c ≠ n7 (tw7 k) := by
    intro k _ h
    exact hbcT (by rw [h]; exact n7_tw_mem k)
  have hN : ∀ y : N7, (y * bm0 = bm0 * y ∨ y * c = c * y ∨ y * (bm0 * c) = bm0 * c * y) →
      y * bm0 * y⁻¹ ∈ ({1, bm0, c, bm0 * c} : Set N7) ∧
      y * c * y⁻¹ ∈ ({1, bm0, c, bm0 * c} : Set N7) ∧
      y⁻¹ * bm0 * y ∈ ({1, bm0, c, bm0 * c} : Set N7) ∧
      y⁻¹ * c * y ∈ ({1, bm0, c, bm0 * c} : Set N7) := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (B' : Set N7) := by
      rcases hy with h | h | h
      · exact hcent _ hb0 hne0 y h
      · exact hcent _ hcB hc1 y h
      · exact hcent _ hbcB hbc1 y h
    obtain ⟨e1, e2, e3, e4⟩ := (mem_normalizer_klein7 hb0 hcB hB').1 hyN
    exact ⟨(hmemS _).1 e1, (hmemS _).1 e2, (hmemS _).1 e3, (hmemS _).1 e4⟩
  have hcard0 : Nat.card n7B = 4 := card_n7B hb ht
  have hfin : ∀ (ι : N7 ≃* N7), n7B.map ι.toMonoidHom ≤ B' → n7B.map ι.toMonoidHom = B' := by
    intro ι hle
    refine (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [Subgroup.card_map_of_injective ι.injective, hcard0, hcard]
  have hgen : ∀ (ι : N7 ≃* N7), ι bm0 ∈ B' → ι bm1 ∈ B' → n7B.map ι.toMonoidHom = B' := by
    intro ι h0 h1
    refine hfin ι ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro y (rfl | rfl)
    · exact h0
    · exact h1
  obtain ⟨n, h0, h1⟩ := hk c hcc hcomm_c hcT' hbcT' hcb hN
  refine ⟨MulAut.conj n, map_conj_n7T ht hn _, hgen _ ?_ ?_⟩
  · rw [MulAut.conj_apply]
    exact (hmemS _).2 h0
  · rw [MulAut.conj_apply]
    exact (hmemS _).2 h1

end Klein

end CFSG.CGT.T75M23
