module

public import CFSG.CGT.T75JM.L2FAlpha

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def TNormal : Prop := ∀ n : N0, ∀ k < 16, ∃ l < 16, n * n0 (tw k) * n⁻¹ = n0 (tw l)

@[expose] def KleinFact : Prop :=
  ∀ c : N0, c * c = 1 → c * bb0 = bb0 * c → (∀ k < 16, c ≠ n0 (tw k)) →
    (∀ k < 16, bb0 * c ≠ n0 (tw k)) → c ≠ bb0 →
    (∀ y : N0, (y * bb0 = bb0 * y ∨ y * c = c * y ∨ y * (bb0 * c) = bb0 * c * y) →
      y * bb0 * y⁻¹ ∈ ({1, bb0, c, bb0 * c} : Set N0) ∧
      y * c * y⁻¹ ∈ ({1, bb0, c, bb0 * c} : Set N0) ∧
      y⁻¹ * bb0 * y ∈ ({1, bb0, c, bb0 * c} : Set N0) ∧
      y⁻¹ * c * y ∈ ({1, bb0, c, bb0 * c} : Set N0)) →
    ∃ n : N0,
      (n * bb0 * n⁻¹ ∈ ({1, bb0, c, bb0 * c} : Set N0) ∧
        n * bb1 * n⁻¹ ∈ ({1, bb0, c, bb0 * c} : Set N0)) ∨
      (n * n0 (substWord (bGen 0)) * n⁻¹ ∈ ({1, bb0, c, bb0 * c} : Set N0) ∧
        n * n0 (substWord (bGen 1)) * n⁻¹ ∈ ({1, bb0, c, bb0 * c} : Set N0))

section Klein



theorem n0T_normal (ht : tCheck = true) (hn : TNormal) (n t : N0) (htT : t ∈ n0T) :
    n * t * n⁻¹ ∈ n0T := by
  obtain ⟨k, hk, rfl⟩ := (mem_n0T_iff ht t).1 htT
  obtain ⟨l, -, e⟩ := hn n k hk
  rw [e]
  exact n0_tw_mem l

theorem map_conj_n0T (ht : tCheck = true) (hn : TNormal) (n : N0) :
    n0T.map (MulAut.conj n).toMonoidHom = n0T := by
  apply le_antisymm
  · rintro _ ⟨t, htT, rfl⟩
    exact n0T_normal ht hn n t htT
  · intro t htT
    refine ⟨n⁻¹ * t * n, ?_, ?_⟩
    · simpa using n0T_normal ht hn n⁻¹ t htT
    · simp [MulAut.conj_apply, mul_assoc]

theorem map_trans_toMonoidHom (K : Subgroup N0) (e₁ e₂ : N0 ≃* N0) :
    K.map (e₁.trans e₂).toMonoidHom = (K.map e₁.toMonoidHom).map e₂.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem klein_class_of_checks (ht : tCheck = true) (hb : bCheck = true)
    (hn : TNormal) (hα1 : alphaRelCheck = true) (hα2 : AlphaInj)
    (hα3 : alphaTCheck = true) (hk : KleinFact) (B' : Subgroup N0) (hb0 : bb0 ∈ B')
    (hexp : ∀ x ∈ B', x * x = 1) (hcard : Nat.card B' = 4) (hbot : B' ⊓ n0T = ⊥)
    (hcent : ∀ b ∈ B', b ≠ 1 → ∀ y : N0, y * b = b * y →
      y ∈ Subgroup.normalizer (B' : Set N0)) :
    ∃ ι : N0 ≃* N0, n0T.map ι.toMonoidHom = n0T ∧ n0B.map ι.toMonoidHom = B' := by
  obtain ⟨hsq0, -, -, hne0, -, -, -, -, -, -⟩ := bFacts hb ht
  obtain ⟨c, hcB, hc1, hcb⟩ : ∃ c ∈ B', c ≠ 1 ∧ c ≠ bb0 := by
    by_contra hcon
    push Not at hcon
    have hsub : (B' : Set N0) ⊆ {1, bb0} := by
      intro y hy
      by_cases h1 : y = 1
      · simp [h1]
      · simp [hcon y hy h1]
    have h2 : (B' : Set N0).ncard ≤ 2 := by
      refine (Set.ncard_le_ncard hsub).trans ?_
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have h3 : (B' : Set N0).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hcard
    omega
  have hcc : c * c = 1 := hexp c hcB
  have hbcB : bb0 * c ∈ B' := B'.mul_mem hb0 hcB
  have hcomm_c : c * bb0 = bb0 * c := by
    have h1 : (c * bb0)⁻¹ = c * bb0 := inv_eq_of_mul_eq_one_right (hexp _ (B'.mul_mem hcB hb0))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hcc, inv_eq_of_mul_eq_one_right hsq0] at h1
    exact h1.symm
  have hbc1 : bb0 * c ≠ 1 := by
    intro h
    apply hcb
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hsq0]
  have hnT : ∀ y ∈ B', y ≠ 1 → y ∉ n0T := by
    intro y hy hy1 hyT
    have : y ∈ B' ⊓ n0T := ⟨hy, hyT⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hy1 this
  have hcT : c ∉ n0T := hnT c hcB hc1
  have hbcT : bb0 * c ∉ n0T := hnT _ hbcB hbc1
  have hbc_ne_b : bb0 * c ≠ bb0 := by
    intro h
    apply hc1
    simpa using h
  have hbc_ne_c : bb0 * c ≠ c := by
    intro h
    apply hne0
    simpa using h
  have hsub : ({1, bb0, c, bb0 * c} : Set N0) ⊆ (B' : Set N0) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact B'.one_mem
    · exact hb0
    · exact hcB
    · exact hbcB
  have hB'eq : (B' : Set N0) = {1, bb0, c, bb0 * c} := by
    have h4 : ({1, bb0, c, bb0 * c} : Set N0).ncard = 4 :=
      ncard_four hne0.symm hc1.symm hbc1.symm hcb.symm hbc_ne_b.symm hbc_ne_c.symm
    have h5 : (B' : Set N0).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hcard
    exact (Set.eq_of_subset_of_ncard_le hsub (by omega)).symm
  have hmemS : ∀ y : N0, y ∈ B' ↔ y ∈ ({1, bb0, c, bb0 * c} : Set N0) := by
    intro y
    rw [← hB'eq, SetLike.mem_coe]
  have hB' : ∀ y ∈ B', y = 1 ∨ y = bb0 ∨ y = c ∨ y = bb0 * c := by
    intro y hy
    have := (hmemS y).1 hy
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using this
  have hcT' : ∀ k < 16, c ≠ n0 (tw k) := by
    intro k _ h
    exact hcT (by rw [h]; exact n0_tw_mem k)
  have hbcT' : ∀ k < 16, bb0 * c ≠ n0 (tw k) := by
    intro k _ h
    exact hbcT (by rw [h]; exact n0_tw_mem k)
  have hN : ∀ y : N0, (y * bb0 = bb0 * y ∨ y * c = c * y ∨ y * (bb0 * c) = bb0 * c * y) →
      y * bb0 * y⁻¹ ∈ ({1, bb0, c, bb0 * c} : Set N0) ∧
      y * c * y⁻¹ ∈ ({1, bb0, c, bb0 * c} : Set N0) ∧
      y⁻¹ * bb0 * y ∈ ({1, bb0, c, bb0 * c} : Set N0) ∧
      y⁻¹ * c * y ∈ ({1, bb0, c, bb0 * c} : Set N0) := by
    intro y hy
    have hyN : y ∈ Subgroup.normalizer (B' : Set N0) := by
      rcases hy with h | h | h
      · exact hcent _ hb0 hne0 y h
      · exact hcent _ hcB hc1 y h
      · exact hcent _ hbcB hbc1 y h
    obtain ⟨e1, e2, e3, e4⟩ := (mem_normalizer_klein hb0 hcB hB').1 hyN
    exact ⟨(hmemS _).1 e1, (hmemS _).1 e2, (hmemS _).1 e3, (hmemS _).1 e4⟩
  have hcard0 : Nat.card n0B = 4 := card_n0B hb ht
  have hfin : ∀ (ι : N0 ≃* N0), n0B.map ι.toMonoidHom ≤ B' → n0B.map ι.toMonoidHom = B' := by
    intro ι hle
    refine (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [Subgroup.card_map_of_injective ι.injective, hcard0, hcard]
  have hgen : ∀ (ι : N0 ≃* N0), ι bb0 ∈ B' → ι bb1 ∈ B' → n0B.map ι.toMonoidHom = B' := by
    intro ι h0 h1
    refine hfin ι ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).2 ?_
    rintro y (rfl | rfl)
    · exact h0
    · exact h1
  obtain ⟨n, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩ := hk c hcc hcomm_c hcT' hbcT' hcb hN
  ·
    refine ⟨MulAut.conj n, map_conj_n0T ht hn _, hgen _ ?_ ?_⟩
    · rw [MulAut.conj_apply]
      exact (hmemS _).2 h0
    · rw [MulAut.conj_apply]
      exact (hmemS _).2 h1
  ·
    refine ⟨(alphaEquiv hα1 hα2).trans (MulAut.conj n), ?_, hgen _ ?_ ?_⟩
    · rw [map_trans_toMonoidHom, alpha_map_T hα1 hα2 ht hα3]
      exact map_conj_n0T ht hn _
    · rw [MulEquiv.trans_apply, MulAut.conj_apply, alphaEquiv_apply, bb0, alphaHom_mk]
      exact (hmemS _).2 h0
    · rw [MulEquiv.trans_apply, MulAut.conj_apply, alphaEquiv_apply, bb1, alphaHom_mk]
      exact (hmemS _).2 h1

end Klein

end CFSG.CGT.T75JM
