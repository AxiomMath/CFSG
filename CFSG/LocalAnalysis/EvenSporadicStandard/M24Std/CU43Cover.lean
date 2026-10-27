
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43CoverBase

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Count

public section

namespace CFSG.EvenSporadicStandard.M24Std.CU43

open Subgroup CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43 CFSG.Sporadic.SmallOddCore

section Cover

theorem ncard_InvCoset {k N : ℕ} (hkN : (k, N) ∈ cosetCount) :
    (InvCoset k).ncard = N := by
  have h := card_sq_coset hkN
  let e : {g : P // (g : Equiv.Perm (Fin 820)) * tP k * ((g : Equiv.Perm (Fin 820)) * tP k) = 1} ≃
      ↥(InvCoset k) :=
    { toFun := fun x => ⟨(x.1 : Equiv.Perm (Fin 820)) * tP k, x.1.1, x.1.2, rfl, x.2⟩
      invFun := fun y => ⟨⟨y.1 * (tP k)⁻¹, by
        obtain ⟨g, hg, hy, -⟩ := y.2
        rw [hy]
        simpa using hg⟩, by
        obtain ⟨g, hg, hy, hy2⟩ := y.2
        have : y.1 * (tP k)⁻¹ * tP k = y.1 := by group
        rw [this]
        exact hy2⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  rw [← h, Nat.card_congr e, Nat.card_coe_set_eq]

theorem card_inf_centralizer_rP {j : ℕ} (hj : j < 9) :
    Nat.card ↥(P ⊓ centralizer ({rP j} : Set (Equiv.Perm (Fin 820)))) = repCent[j]! := by
  rw [← card_comm_rep hj]
  refine Nat.card_congr ?_
  exact
    { toFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).1⟩, by
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).2⟩
      invFun := fun y => ⟨y.1.1, mem_inf.2 ⟨y.1.2, mem_centralizer_singleton_iff.2 y.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem ncard_conjClass_rP {j : ℕ} (hj : j < 9) :
    (conjClass P (rP j)).ncard * repCent[j]! = 3265920 := by
  have h := ncard_conjClass_mul_card P (rP j)
  rwa [card_inf_centralizer_rP hj, card_P] at h

theorem ncard_class {j c N : ℕ} (hj : j < 9)
    (hc : repCent[j]! = c) (hN : N * c = 3265920) : (conjClass P (rP j)).ncard = N := by
  have h := ncard_conjClass_rP hj
  rw [hc] at h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hN
      omega
    · exact h0
  exact Nat.eq_of_mul_eq_mul_right hc0 (h.trans hN.symm)

theorem cover_coset_zero
    {β : Equiv.Perm (Fin 820)} (hβ : β ∈ InvCoset 0) :
    β ∈ conjClass P (1 : Equiv.Perm (Fin 820)) ∨ β ∈ conjClass P (rP 2) := by
  have hrep : repCoset[2]! = 0 := by decide
  have hsub : conjClass P (rP 2) ⊆ InvCoset 0 := by
    simpa [hrep] using conjClass_subset_InvCoset (j := 2) (by norm_num)
  have hn : (InvCoset 0).ncard = 2836 := ncard_InvCoset (k := 0) (N := 2836) (by simp [cosetCount])
  have h2 : (conjClass P (rP 2)).ncard = 2835 :=
    ncard_class (c := 1152) (by norm_num) (by decide) (by norm_num)
  exact subset_union_of_ncard (finite_InvCoset 0) conjClass_one_subset hsub
    (disjoint_conjClass_of_ne (by rw [ncard_conjClass_one, h2]; norm_num))
    (by rw [hn, ncard_conjClass_one, h2]) hβ

theorem cover_coset_single
    {k j N c : ℕ} (hkN : (k, N) ∈ cosetCount) (hj : j < 9) (hjk : repCoset[j]! = k)
    (hc : repCent[j]! = c) (hNc : N * c = 3265920) {β : Equiv.Perm (Fin 820)}
    (hβ : β ∈ InvCoset k) : β ∈ conjClass P (rP j) := by
  have hsub : conjClass P (rP j) ⊆ InvCoset k := by
    simpa [hjk] using conjClass_subset_InvCoset hj
  have hn := ncard_InvCoset hkN
  have h2 := ncard_class hj hc hNc
  exact subset_of_ncard (finite_InvCoset k) hsub (by rw [hn, h2]) hβ

theorem cover_coset_pair
    {k j₁ j₂ N c₁ c₂ N₁ N₂ : ℕ} (hkN : (k, N) ∈ cosetCount) (hj₁ : j₁ < 9) (hj₂ : j₂ < 9)
    (hjk₁ : repCoset[j₁]! = k) (hjk₂ : repCoset[j₂]! = k) (hc₁ : repCent[j₁]! = c₁)
    (hc₂ : repCent[j₂]! = c₂) (hN₁ : N₁ * c₁ = 3265920) (hN₂ : N₂ * c₂ = 3265920)
    (hne : N₁ ≠ N₂) (hsum : N₁ + N₂ = N) {β : Equiv.Perm (Fin 820)} (hβ : β ∈ InvCoset k) :
    β ∈ conjClass P (rP j₁) ∨ β ∈ conjClass P (rP j₂) := by
  have hsub₁ : conjClass P (rP j₁) ⊆ InvCoset k := by
    simpa [hjk₁] using conjClass_subset_InvCoset hj₁
  have hsub₂ : conjClass P (rP j₂) ⊆ InvCoset k := by
    simpa [hjk₂] using conjClass_subset_InvCoset hj₂
  have hn := ncard_InvCoset hkN
  have h₁ := ncard_class hj₁ hc₁ hN₁
  have h₂ := ncard_class hj₂ hc₂ hN₂
  exact subset_union_of_ncard (finite_InvCoset k) hsub₁ hsub₂
    (disjoint_conjClass_of_ne (by rw [h₁, h₂]; exact hne)) (by rw [hn, h₁, h₂, hsum]) hβ

theorem involution_data
    {β : Equiv.Perm (Fin 820)} (hβ : β ∈ R) (hβ2 : β * β = 1) (hβ1 : β ≠ 1) :
    ∃ j, j < 9 ∧ β ∈ conjClass P (rP j) ∧ ∃ g ∈ P, β = g * tP repCoset[j]! := by
  obtain ⟨g, hg, k, hk, rfl⟩ := mem_R_iff.1 hβ
  have hInv : g * tP k ∈ InvCoset k := ⟨g, hg, rfl, hβ2⟩
  interval_cases k
  · rcases cover_coset_zero hInv with h | h
    · exfalso
      obtain ⟨c, hc, hc'⟩ := h
      apply hβ1
      rw [hc']
      simp
    · exact ⟨2, by norm_num, h, g, hg, by simp [repCoset]⟩
  · exact absurd hβ2 (no_involution_odd (Or.inl rfl) hg)
  · rcases cover_coset_pair (k := 2) (j₁ := 3) (j₂ := 8) (N := 5076) (c₁ := 6048) (c₂ := 720)
      (N₁ := 540) (N₂ := 4536) (by simp [cosetCount]) (by norm_num) (by norm_num) (by decide)
      (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hInv with h | h
    · exact ⟨3, by norm_num, h, g, hg, by simp [repCoset]⟩
    · exact ⟨8, by norm_num, h, g, hg, by simp [repCoset]⟩
  · exact absurd hβ2 (no_involution_odd (Or.inr rfl) hg)
  · rcases cover_coset_pair (k := 4) (j₁ := 0) (j₂ := 7) (N := 5796) (c₁ := 25920) (c₂ := 576)
      (N₁ := 126) (N₂ := 5670) (by simp [cosetCount]) (by norm_num) (by norm_num) (by decide)
      (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hInv with h | h
    · exact ⟨0, by norm_num, h, g, hg, by simp [repCoset]⟩
    · exact ⟨7, by norm_num, h, g, hg, by simp [repCoset]⟩
  · exact ⟨5, by norm_num, cover_coset_single (k := 5) (j := 5) (N := 4536) (c := 720)
      (by simp [cosetCount]) (by norm_num) (by decide) (by decide) (by norm_num) hInv, g, hg,
      by simp [repCoset]⟩
  · rcases cover_coset_pair (k := 6) (j₁ := 1) (j₂ := 6) (N := 5796) (c₁ := 25920) (c₂ := 576)
      (N₁ := 126) (N₂ := 5670) (by simp [cosetCount]) (by norm_num) (by norm_num) (by decide)
      (by decide) (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hInv with h | h
    · exact ⟨1, by norm_num, h, g, hg, by simp [repCoset]⟩
    · exact ⟨6, by norm_num, h, g, hg, by simp [repCoset]⟩
  · exact ⟨4, by norm_num, cover_coset_single (k := 7) (j := 4) (N := 4536) (c := 720)
      (by simp [cosetCount]) (by norm_num) (by decide) (by decide) (by norm_num) hInv, g, hg,
      by simp [repCoset]⟩

theorem inner_involutions_conj
    {β β' : Equiv.Perm (Fin 820)} (hβ : β ∈ P) (hβ' : β' ∈ P) (h2 : β * β = 1)
    (h2' : β' * β' = 1) (h1 : β ≠ 1) (h1' : β' ≠ 1) : ∃ c ∈ P, β' = c * β * c⁻¹ := by
  obtain ⟨j, hj, hcl, g, hg, hβg⟩ := involution_data (P_le_R hβ) h2 h1
  obtain ⟨j', hj', hcl', g', hg', hβg'⟩ := involution_data (P_le_R hβ') h2' h1'
  have e1 := coset_index_of_mem hj (repCoset_eq_zero_of_mem hβ hj hg hβg)
  have e2 := coset_index_of_mem hj' (repCoset_eq_zero_of_mem hβ' hj' hg' hβg')
  subst e1
  subst e2
  obtain ⟨c₁, hc₁, rfl⟩ := hcl
  obtain ⟨c₂, hc₂, hc₂'⟩ := hcl'
  refine ⟨c₂ * c₁⁻¹, P.mul_mem hc₂ (P.inv_mem hc₁), ?_⟩
  rw [hc₂']
  group

theorem outer_card_centralizer
    {β : Equiv.Perm (Fin 820)} (hβ : β ∈ R) (hβP : β ∉ P) (h2 : β * β = 1) :
    Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 576 ∨
      Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 720 ∨
      Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 6048 ∨
      Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 25920 := by
  have hβ1 : β ≠ 1 := fun h => hβP (h ▸ P.one_mem)
  obtain ⟨j, hj, ⟨c, hc, rfl⟩, g, hg, hβg⟩ := involution_data hβ h2 hβ1
  have hj2 : j ≠ 2 := by
    rintro rfl
    apply hβP
    have : repCoset[2]! = 0 := by decide
    rw [hβg, this, tP_zero, mul_one]
    exact hg
  rw [card_inf_centralizer_conj hc, card_inf_centralizer_rP hj]
  interval_cases j <;> simp_all [repCent]

theorem same_coset_conj
    {β β' : Equiv.Perm (Fin 820)} (hβ : β ∈ R) (hβP : β ∉ P) (h2 : β * β = 1)
    (hβ' : β' ∈ R) (h2' : β' * β' = 1) (hcos : β' * β⁻¹ ∈ P)
    (hc : Nat.card ↥(P ⊓ centralizer ({β} : Set (Equiv.Perm (Fin 820)))) = 720)
    (hc' : Nat.card ↥(P ⊓ centralizer ({β'} : Set (Equiv.Perm (Fin 820)))) = 720) :
    ∃ c ∈ P, β' = c * β * c⁻¹ := by
  have hβ1 : β ≠ 1 := fun h => hβP (h ▸ P.one_mem)
  have hβ'P : β' ∉ P := by
    intro h
    apply hβP
    have : β = (β' * β⁻¹)⁻¹ * β' := by group
    rw [this]
    exact P.mul_mem (P.inv_mem hcos) h
  have hβ1' : β' ≠ 1 := fun h => hβ'P (h ▸ P.one_mem)
  obtain ⟨j, hj, ⟨c, hc₀, hβc⟩, g, hg, hβg⟩ := involution_data hβ h2 hβ1
  obtain ⟨j', hj', ⟨c', hc₀', hβc'⟩, g', hg', hβg'⟩ := involution_data hβ' h2' hβ1'
  have hk := repCoset_lt hj
  have hk' := repCoset_lt hj'
  have hkk : repCoset[j']! = repCoset[j]! := by
    by_contra hne
    have h1 : tP repCoset[j']! * (tP repCoset[j]!)⁻¹ ∈ P := by
      have e : tP repCoset[j']! * (tP repCoset[j]!)⁻¹ = g'⁻¹ * (β' * β⁻¹) * g := by
        have e1 : tP repCoset[j']! = g'⁻¹ * β' := by rw [hβg']; group
        have e2 : (tP repCoset[j]!)⁻¹ = β⁻¹ * g := by rw [hβg]; group
        rw [e1, e2]
        group
      rw [e]
      exact P.mul_mem (P.mul_mem (P.inv_mem hg') hcos) hg
    exact tP_mul_inv_not_mem hk' hk hne h1
  rw [hβc, card_inf_centralizer_conj hc₀, card_inf_centralizer_rP hj] at hc
  rw [hβc', card_inf_centralizer_conj hc₀', card_inf_centralizer_rP hj'] at hc'
  have hjj : j' = j := rep_unique j hj j' hj' hkk hc hc'
  subst hjj
  refine ⟨c' * c⁻¹, P.mul_mem hc₀' (P.inv_mem hc₀), ?_⟩
  rw [hβc', hβc]
  group

end Cover

end CFSG.EvenSporadicStandard.M24Std.CU43
