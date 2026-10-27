module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Count
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Star

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

variable {V : Type} [AddCommGroup V] {X : Type} [Group X] [DistribMulAction X V]
  {A B : Subgroup X} {R U W : AddSubgroup V}

namespace Hyp51

variable (h : Hyp51 X A B R U W)
include h

theorem pat_of_mem_U {u : V} (hu : u ∈ U) (h0 : u ≠ 0) :
    h.decomp.pat u = (false, true, false) := by
  obtain ⟨h1, h3⟩ := (h.decomp.mem_U_iff u).1 hu
  have h2 : h.decomp.cU u ≠ 0 := fun h2 => h0 (by rw [← h.decomp.coord_sum u, h1, h2, h3]; simp)
  simp [Decomp.pat, nz_of_ne h2, h1, h3]

theorem pat_of_mem_W {w : V} (hw : w ∈ W) (h0 : w ≠ 0) :
    h.decomp.pat w = (false, false, true) := by
  obtain ⟨h1, h2⟩ := (h.decomp.mem_W_iff w).1 hw
  have h3 : h.decomp.cW w ≠ 0 := fun h3 => h0 (by rw [← h.decomp.coord_sum w, h1, h2, h3]; simp)
  simp [Decomp.pat, nz_of_ne h3, h1, h2]

theorem occ_of_mem {T : AddSubgroup V} (hT : T ∈ members X R) {t : V} (ht : t ∈ T)
    (ht0 : t ≠ 0) : h.Occ (h.decomp.pat t) :=
  ⟨t, mem_fused_iff.2 ⟨ht0, T, hT, ht⟩, rfl⟩

variable [Finite V]

theorem exists_member_of_occ {p : Bool × Bool × Bool} (hp : h.Occ p) :
    ∃ T ∈ members X R, T ≠ ⊥ ∧ ∀ t ∈ T, t ≠ 0 → h.decomp.pat t = p := by
  obtain ⟨v, hv, rfl⟩ := hp
  obtain ⟨hv0, T, hT, hvT⟩ := mem_fused_iff.1 hv
  obtain ⟨p, hpT⟩ := h.pat_uniform hT
  refine ⟨T, hT, fun hbot => hv0 ?_, fun t ht ht0 => by rw [hpT t ht ht0, hpT v hvT hv0]⟩
  rw [hbot] at hvT
  exact AddSubgroup.mem_bot.1 hvT

theorem mem_U_of_occ (hp : h.Occ (false, true, false)) : U ∈ members X R := by
  obtain ⟨T, hT, hT0, hpT⟩ := h.exists_member_of_occ hp
  have hle : T ≤ U := fun t ht => by
    by_cases ht0 : t = 0
    · rw [ht0]
      exact zero_mem U
    have := hpT t ht ht0
    simp only [Decomp.pat, Prod.mk.injEq, nz_eq_false, nz_eq_true] at this
    exact (h.decomp.mem_U_iff t).2 ⟨this.1, this.2.2⟩
  rcases h.twoU T hT (hle.trans le_sup_right) with ⟨rfl, -⟩ | hTU
  · exact hT
  · exact absurd (by rwa [inf_eq_left.2 hle] at hTU) hT0

theorem mem_W_of_occ (hp : h.Occ (false, false, true)) : W ∈ members X R := by
  obtain ⟨T, hT, hT0, hpT⟩ := h.exists_member_of_occ hp
  have hle : T ≤ W := fun t ht => by
    by_cases ht0 : t = 0
    · rw [ht0]
      exact zero_mem W
    have := hpT t ht ht0
    simp only [Decomp.pat, Prod.mk.injEq, nz_eq_false, nz_eq_true] at this
    exact (h.decomp.mem_W_iff t).2 ⟨this.1, this.2.1⟩
  rcases h.twoW T hT (hle.trans le_sup_right) with ⟨rfl, -⟩ | hTW
  · exact hT
  · exact absurd (by rwa [inf_eq_left.2 hle] at hTW) hT0

theorem occ_of_mem_U (hU : U ∈ members X R) : h.Occ (false, true, false) := by
  obtain ⟨u, hu, hu0⟩ := U.bot_or_exists_ne_zero.resolve_left fun hbot => by
    have := h.two_lt_card_U
    rw [hbot, AddSubgroup.card_bot] at this
    omega
  exact h.pat_of_mem_U hu hu0 ▸ h.occ_of_mem hU hu hu0

theorem occ_of_mem_W (hW : W ∈ members X R) : h.Occ (false, false, true) := by
  obtain ⟨w, hw, hw0⟩ := W.bot_or_exists_ne_zero.resolve_left fun hbot => by
    have := h.two_lt_card_W
    rw [hbot, AddSubgroup.card_bot] at this
    omega
  exact h.pat_of_mem_W hw hw0 ▸ h.occ_of_mem hW hw hw0

theorem exists_RU_of_occ (hp : h.Occ (true, true, false)) :
    ∃ T ∈ members X R, T ≤ R ⊔ U ∧ T ⊓ U = ⊥ ∧ T ⊓ R = ⊥ := by
  obtain ⟨T, hT, -, hpT⟩ := h.exists_member_of_occ hp
  refine ⟨T, hT, fun t ht => ?_, ?_, ?_⟩
  · by_cases ht0 : t = 0
    · rw [ht0]
      exact zero_mem _
    have := hpT t ht ht0
    simp only [Decomp.pat, Prod.mk.injEq, nz_eq_false] at this
    exact (h.decomp.cW_eq_zero_iff t).1 this.2.2
  · refine eq_bot_iff.2 fun t ht => ?_
    obtain ⟨htT, htU⟩ := AddSubgroup.mem_inf.1 ht
    by_contra ht0
    have := (hpT t htT ht0).symm.trans (h.pat_of_mem_U htU ht0)
    simp at this
  · refine eq_bot_iff.2 fun t ht => ?_
    obtain ⟨htT, htR⟩ := AddSubgroup.mem_inf.1 ht
    by_contra ht0
    have := (hpT t htT ht0).symm.trans (h.pat_of_mem_R htR ht0)
    simp at this

theorem exists_RW_of_occ (hp : h.Occ (true, false, true)) :
    ∃ T ∈ members X R, T ≤ R ⊔ W ∧ T ⊓ W = ⊥ ∧ T ⊓ R = ⊥ := by
  obtain ⟨T, hT, -, hpT⟩ := h.exists_member_of_occ hp
  refine ⟨T, hT, fun t ht => ?_, ?_, ?_⟩
  · by_cases ht0 : t = 0
    · rw [ht0]
      exact zero_mem _
    have := hpT t ht ht0
    simp only [Decomp.pat, Prod.mk.injEq, nz_eq_false] at this
    exact (h.decomp.cU_eq_zero_iff t).1 this.2.1
  · refine eq_bot_iff.2 fun t ht => ?_
    obtain ⟨htT, htW⟩ := AddSubgroup.mem_inf.1 ht
    by_contra ht0
    have := (hpT t htT ht0).symm.trans (h.pat_of_mem_W htW ht0)
    simp at this
  · refine eq_bot_iff.2 fun t ht => ?_
    obtain ⟨htT, htR⟩ := AddSubgroup.mem_inf.1 ht
    by_contra ht0
    have := (hpT t htT ht0).symm.trans (h.pat_of_mem_R htR ht0)
    simp at this

theorem config :
    (¬h.Occ (false, true, false) ∧ ¬h.Occ (false, false, true) ∧ h.Occ (true, true, false) ∧
      h.Occ (true, false, true) ∧ ¬h.Occ (false, true, true) ∧ h.Occ (true, true, true)) ∨
    (h.Occ (false, true, false) ∧ h.Occ (false, false, true) ∧ Nat.card R = 4) := by
  classical
  obtain ⟨l, hl⟩ : ∃ l, Nat.card R = 4 * l + 4 := by
    obtain ⟨c, hc⟩ := h.four_dvd_card_R
    have := h.two_lt
    exact ⟨c - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, Nat.card U = 4 * k + 4 := by
    obtain ⟨c, hc⟩ := h.four_dvd_card_U
    have := h.two_lt_card_U
    exact ⟨c - 1, by omega⟩
  have hlk : l ≤ k := by
    have := h.card_R_le_card_U
    omega
  have hchi : h.chi = chi6 (decide (h.Occ (false, true, false)))
      (decide (h.Occ (false, false, true))) (decide (h.Occ (true, true, false)))
      (decide (h.Occ (true, false, true))) (decide (h.Occ (false, true, true)))
      (decide (h.Occ (true, true, true))) := by
    funext p
    rcases p with ⟨_ | _, _ | _, _ | _⟩ <;> simp [Hyp51.chi, chi6, h.occ_R, h.not_occ_zero]
  have hcard : ∀ {T : AddSubgroup V}, T ∈ members X R → T ≠ ⊥ := fun hT hbot => by
    have := card_of_mem_members hT
    rw [hbot, AddSubgroup.card_bot] at this
    have := h.two_lt
    omega
  have hres := arith (decide (h.Occ (false, true, false))) (decide (h.Occ (false, false, true)))
    (decide (h.Occ (true, true, false))) (decide (h.Occ (true, false, true)))
    (decide (h.Occ (false, true, true))) (decide (h.Occ (true, true, true))) k l hlk ?_ ?_ ?_ ?_
    ?_ ?_
  · simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hres
    rcases hres with hA | ⟨hU, hW, -, -, hl0⟩ | ⟨hU, hW, hiW, -, -⟩ | ⟨hU, hW, hiU, -, -⟩
    · exact Or.inl hA
    · exact Or.inr ⟨hU, hW, by omega⟩
    · exfalso
      obtain ⟨T, hT, hle, -, hTR⟩ := h.exists_RW_of_occ hiW
      refine h.star (h.mem_U_of_occ hU) (fun hWm => hW (h.occ_of_mem_W hWm)) ⟨T, hT, ?_, hle⟩
      intro hTR'
      rw [hTR', inf_idem] at hTR
      exact h.R_ne_bot hTR
    · exfalso
      obtain ⟨T, hT, hle, -, hTR⟩ := h.exists_RU_of_occ hiU
      refine h.symm.star (h.mem_W_of_occ hW) (fun hUm => hU (h.occ_of_mem_U hUm)) ⟨T, hT, ?_, hle⟩
      intro hTR'
      rw [hTR', inf_idem] at hTR
      exact h.R_ne_bot hTR
  ·
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    intro hU hiU
    have hUm := h.mem_U_of_occ hU
    obtain ⟨T, hT, hT0, hpT⟩ := h.exists_member_of_occ hiU
    obtain ⟨t, ht, ht0⟩ := T.bot_or_exists_ne_zero.resolve_left hT0
    have hle' : T ≤ R ⊔ U := fun s hs => by
      by_cases hs0 : s = 0
      · rw [hs0]
        exact zero_mem _
      have := hpT s hs hs0
      simp only [Decomp.pat, Prod.mk.injEq, nz_eq_false] at this
      exact (h.decomp.cW_eq_zero_iff s).1 this.2.2
    rcases h.eq_R_or_U hUm hT hle' with rfl | rfl
    · have := (hpT t ht ht0).symm.trans (h.pat_of_mem_R ht ht0)
      simp at this
    · have := (hpT t ht ht0).symm.trans (h.pat_of_mem_U ht ht0)
      simp at this
  ·
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
    intro hW hiW
    have hWm := h.mem_W_of_occ hW
    obtain ⟨T, hT, hT0, hpT⟩ := h.exists_member_of_occ hiW
    obtain ⟨t, ht, ht0⟩ := T.bot_or_exists_ne_zero.resolve_left hT0
    have hle' : T ≤ R ⊔ W := fun s hs => by
      by_cases hs0 : s = 0
      · rw [hs0]
        exact zero_mem _
      have := hpT s hs hs0
      simp only [Decomp.pat, Prod.mk.injEq, nz_eq_false] at this
      exact (h.decomp.cU_eq_zero_iff s).1 this.2.1
    rcases h.symm.eq_R_or_U hWm hT hle' with rfl | rfl
    · have := (hpT t ht ht0).symm.trans (h.pat_of_mem_R ht ht0)
      simp at this
    · have := (hpT t ht ht0).symm.trans (h.pat_of_mem_W ht ht0)
      simp at this
  ·
    simp only [decide_eq_true_eq]
    obtain ⟨T, hT, -, hTU, hTW⟩ := h.three
    obtain ⟨t, ht, ht0⟩ := T.bot_or_exists_ne_zero.resolve_left (hcard hT)
    obtain ⟨h2, h3⟩ := h.cU_cW_ne_zero hTU hTW ht ht0
    have hocc := h.occ_of_mem hT ht ht0
    have hpt : h.decomp.pat t = (nz (h.decomp.cR t), true, true) := by
      simp [Decomp.pat, nz_of_ne h2, nz_of_ne h3]
    rw [hpt] at hocc
    cases hb : nz (h.decomp.cR t)
    · exact Or.inl (hb ▸ hocc)
    · exact Or.inr (hb ▸ hocc)
  · simp only [decide_eq_true_eq]
    intro hU
    have := card_of_mem_members (h.mem_U_of_occ hU)
    omega
  · simp only [decide_eq_true_eq]
    intro hW
    have := card_of_mem_members (h.mem_W_of_occ hW)
    have := h.card_eq
    omega
  · intro p hp
    rw [← hchi] at hp ⊢
    have hocc : h.Occ p := by
      by_contra hn
      simp [Hyp51.chi, hn] at hp
    have := h.cform_eq hocc
    rwa [show Nat.card R - 2 = 4 * l + 2 by omega, show Nat.card U - 2 = 4 * k + 2 by omega]
      at this

theorem fused_eq_compl
    (hA : ¬h.Occ (false, true, false) ∧ ¬h.Occ (false, false, true) ∧ h.Occ (true, true, false) ∧
      h.Occ (true, false, true) ∧ ¬h.Occ (false, true, true) ∧ h.Occ (true, true, true)) :
    fused X R = ((U ⊔ W : AddSubgroup V) : Set V)ᶜ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hA
  ext v
  rw [h.mem_fused_iff_occ, Set.mem_compl_iff, SetLike.mem_coe, ← h.decomp.cR_eq_zero_iff]
  have hpat : h.decomp.pat v =
      (nz (h.decomp.cR v), nz (h.decomp.cU v), nz (h.decomp.cW v)) := rfl
  rw [hpat]
  cases hb1 : nz (h.decomp.cR v) <;> cases nz (h.decomp.cU v) <;> cases nz (h.decomp.cW v) <;>
    simp only [nz_eq_false, nz_eq_true] at hb1 <;>
    simp [hb1, h1, h2, h3, h4, h5, h6, h.occ_R, h.not_occ_zero]

theorem ncard_members_eq (hSig : fused X R = ((U ⊔ W : AddSubgroup V) : Set V)ᶜ) :
    (members X R).ncard = Nat.card U ^ 2 := by
  have h1 := h.ncard_fused
  rw [hSig, Set.ncard_compl, ← Nat.card_coe_set_eq ((U ⊔ W : AddSubgroup V) : Set V),
    SetLike.coe_sort_coe, h.decomp.card_UW,
    h.decomp.card_eq, ← h.card_eq] at h1
  obtain ⟨m', hm'⟩ : ∃ m', Nat.card R = m' + 1 := ⟨Nat.card R - 1, by have := h.two_lt; omega⟩
  rw [hm', Nat.add_sub_cancel] at h1
  have h2 : (m' + 1) * (Nat.card U * Nat.card U) - Nat.card U * Nat.card U =
      m' * (Nat.card U * Nat.card U) := by
    rw [add_mul, one_mul, Nat.add_sub_cancel]
  rw [h2, mul_comm (members X R).ncard] at h1
  have hm0 : 0 < m' := by
    have := h.two_lt
    omega
  rw [sq]
  exact (Nat.eq_of_mul_eq_mul_left hm0 h1).symm

end Hyp51

variable [Finite V]

theorem fusionLemma_full (h : Hyp51 X A B R U W) :
    (fused X R = ((U ⊔ W : AddSubgroup V) : Set V)ᶜ ∧ (members X R).ncard = Nat.card U ^ 2 ∧
      (∃ T ∈ members X R, T ≤ R ⊔ U ∧ T ⊓ U = ⊥ ∧ T ⊓ R = ⊥) ∧
      (∃ T ∈ members X R, T ≤ R ⊔ W ∧ T ⊓ W = ⊥ ∧ T ⊓ R = ⊥)) ∨
    (Nat.card U = 4 ∧ Nat.card R = 4 ∧ U ∈ members X R ∧ W ∈ members X R) := by
  rcases h.config with hA | ⟨hU, hW, hR4⟩
  · have hSig := h.fused_eq_compl hA
    exact Or.inl ⟨hSig, h.ncard_members_eq hSig, h.exists_RU_of_occ hA.2.2.1,
      h.exists_RW_of_occ hA.2.2.2.1⟩
  · have hUm := h.mem_U_of_occ hU
    exact Or.inr ⟨(card_of_mem_members hUm).trans hR4, hR4, hUm, h.mem_W_of_occ hW⟩

theorem fusionLemma (h : Hyp51 X A B R U W) :
    (fused X R = ((U ⊔ W : AddSubgroup V) : Set V)ᶜ ∧ (members X R).ncard = Nat.card U ^ 2) ∨
    (Nat.card U = 4 ∧ Nat.card R = 4 ∧ U ∈ members X R ∧ W ∈ members X R) := by
  rcases fusionLemma_full h with ⟨h1, h2, -, -⟩ | h'
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr h'

theorem fusionLemma_rot (h : Hyp51 X A B R U W) :
    (fused X R = ((U ⊔ W : AddSubgroup V) : Set V)ᶜ ∧
      (∃ T ∈ members X R, T ≤ R ⊔ U ∧ T ⊓ U = ⊥ ∧ T ⊓ R = ⊥) ∧
      (∃ T ∈ members X R, T ≤ R ⊔ W ∧ T ⊓ W = ⊥ ∧ T ⊓ R = ⊥)) ∨
    (Nat.card U = 4 ∧ Nat.card R = 4 ∧ U ∈ members X R ∧ W ∈ members X R) := by
  rcases fusionLemma_full h with ⟨h1, -, h3, h4⟩ | h'
  · exact Or.inl ⟨h1, h3, h4⟩
  · exact Or.inr h'

end CFSG.ComponentClassification.AS76b.Sec5
