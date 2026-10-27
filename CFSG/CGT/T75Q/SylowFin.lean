module

public import CFSG.CGT.T75H.QuatZ
public import CFSG.CGT.T75H.Rank1

public section

namespace CFSG.CGT.T75Q

open CFSG.CGT.T75H

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {A C : Subgroup G} (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    {s : G} (hs : s ∈ A ⊔ C) : ∃ d ∈ A, ∃ c ∈ C, s = d * c := by
  have hA : A ≤ Subgroup.centralizer (C : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun c hc => (hcomm a ha c hc).symm
  have hs' : s ∈ ((A ⊔ C : Subgroup G) : Set G) := hs
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A C
    (hA.trans (Subgroup.centralizer_le_normalizer _))] at hs'
  obtain ⟨d, hd, c, hc, hdc⟩ := Set.mem_mul.1 hs'
  exact ⟨d, hd, c, hc, hdc.symm⟩

theorem false_of_sylow_split [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    {S : Sylow 2 G} {A C : Subgroup G}
    (hsup : A ⊔ C = (S : Subgroup G)) (hinf : A ⊓ C = ⊥)
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a) (hne : C ≠ ⊥)
    (hrank : ∀ α ∈ C, ∀ β ∈ C, α * α = 1 → β * β = 1 → α * β = β * α →
      α = 1 ∨ β = 1 ∨ α = β)
    (hfuse : ∀ g : G, ∀ c ∈ C, c * c = 1 → c ≠ 1 → g⁻¹ * c * g ∈ (S : Subgroup G) →
      g⁻¹ * c * g ∈ C) : False := by
  have hAS : A ≤ (S : Subgroup G) := hsup ▸ le_sup_left
  have hCS : C ≤ (S : Subgroup G) := hsup ▸ le_sup_right
  have hC2 : IsPGroup 2 C := S.isPGroup'.to_le hCS
  have hNC : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions ↥C := by
    intro first second hcommfs
    have h1 : orderOf ((first : ↥C) : G) = 2 := (Subgroup.orderOf_coe _).trans first.2
    have h2 : orderOf ((second : ↥C) : G) = 2 := (Subgroup.orderOf_coe _).trans second.2
    have hsq : ∀ x : G, orderOf x = 2 → x * x = 1 := fun x hx => by
      have := pow_orderOf_eq_one x
      rwa [hx, sq] at this
    have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := fun x hx h => by
      rw [h, orderOf_one] at hx
      omega
    rcases hrank _ (first : ↥C).2 _ (second : ↥C).2 (hsq _ h1) (hsq _ h2)
      (congrArg Subtype.val hcommfs) with h | h | h
    · exact absurd h (hne1 _ h1)
    · exact absurd h (hne1 _ h2)
    · exact Subtype.ext (Subtype.ext h)
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hC2 hNC with
    hcyc | ⟨e, -, ⟨ϕ⟩⟩
  ·
    obtain ⟨c, hcgen⟩ := hcyc.exists_generator
    have hCpow : ∀ x ∈ C, ∃ j : ℤ, x = (c : G) ^ j := by
      intro x hx
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hcgen ⟨x, hx⟩)
      exact ⟨j, by simpa using (congrArg Subtype.val hj).symm⟩
    have hc1 : (c : G) ≠ 1 := by
      intro h1
      apply hne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨j, rfl⟩ := hCpow x hx
      rw [h1, one_zpow]
      exact Subgroup.one_mem _
    have hcS : (c : G) ∈ (S : Subgroup G) := hCS c.2
    have hdec : ∀ s ∈ (S : Subgroup G), ∃ d ∈ A, ∃ j : ℤ, s = d * (c : G) ^ j := by
      intro s hs
      obtain ⟨d, hd, c', hc', rfl⟩ := exists_mul_of_mem_sup hcomm (hsup ▸ hs)
      obtain ⟨j, rfl⟩ := hCpow c' hc'
      exact ⟨d, hd, j, rfl⟩
    have hinf' : ∀ d ∈ A, ∀ j : ℤ, d * (c : G) ^ j = 1 → d = 1 ∧ (c : G) ^ j = 1 := by
      intro d hd j h
      have hcj : (c : G) ^ j ∈ C := Subgroup.zpow_mem _ c.2 j
      have hinv : (c : G) ^ j = d⁻¹ := eq_inv_of_mul_eq_one_right h
      have hmem : (c : G) ^ j ∈ A ⊓ C := ⟨by rw [hinv]; exact A.inv_mem hd, hcj⟩
      rw [hinf, Subgroup.mem_bot] at hmem
      refine ⟨?_, hmem⟩
      rw [hmem, mul_one] at h
      exact h
    have hcomm' : ∀ d ∈ A, d * (c : G) = (c : G) * d := fun d hd => hcomm d hd c c.2
    have hfuse' : ∀ g : G, ∀ z ∈ A, g⁻¹ * (c : G) ^ (orderOf (c : G) / 2) * g ≠ z := by
      intro g z hz h
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 S.isPGroup') ⟨(c : G), hcS⟩
      have hk' : orderOf (c : G) = 2 ^ k :=
        (Subgroup.orderOf_coe (⟨(c : G), hcS⟩ : (S : Subgroup G))).trans hk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · exact absurd (orderOf_eq_one_iff.1 (by simpa using hk')) hc1
        · exact hpos
      obtain ⟨m, hm⟩ : 2 ∣ orderOf (c : G) := by
        rw [hk']
        exact dvd_pow_self 2 (by omega)
      have hmpos : 0 < m := by
        have : 0 < orderOf (c : G) := orderOf_pos _
        omega
      have hdiv : orderOf (c : G) / 2 = m := by omega
      set t := (c : G) ^ (orderOf (c : G) / 2) with ht
      have hord : orderOf t = 2 := by
        rw [ht, hdiv, orderOf_pow_of_dvd hmpos.ne' ⟨2, by omega⟩, hm]
        exact Nat.mul_div_cancel 2 hmpos
      have htt : t * t = 1 := by
        have := pow_orderOf_eq_one t
        rwa [hord, sq] at this
      have ht1 : t ≠ 1 := fun h1 => by
        rw [h1, orderOf_one] at hord
        omega
      have htC : t ∈ C := Subgroup.pow_mem _ c.2 _
      have hzC : z ∈ C := h ▸ hfuse g t htC htt ht1 (h ▸ hAS hz)
      have hz1 : z = 1 := by
        have : z ∈ A ⊓ C := ⟨hz, hzC⟩
        rwa [hinf, Subgroup.mem_bot] at this
      apply ht1
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [h, hz1]; group
    obtain ⟨N, hN, hi⟩ := exists_index_two_of_cyclic_factor S.isPGroup' S.not_dvd_index hAS hcS
      hc1 hdec hinf' hcomm' hfuse'
    exact false_of_index_two hna hN hi
  · exact false_of_quaternion_split hna hsup hcomm ϕ hfuse

end CFSG.CGT.T75Q
