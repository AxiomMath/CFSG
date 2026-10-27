module

public import CFSG.CGT.T75H.QuatCbar
public import CFSG.CGT.T75H.ThompsonCyc
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.CGT.T75H

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem false_of_index_two [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    {N : Subgroup G} (hN : N.Normal) (hi : N.index = 2) : False := by
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.index_bot] at hi
    have : Fact (Nat.Prime (Nat.card G)) := ⟨by rw [hi]; exact Nat.prime_two⟩
    have hcyc : IsCyclic G := isCyclic_of_prime_card hi
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨a, b, hab⟩ := hna
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg b)
    exact hab ((Commute.zpow_zpow_self g i j).eq)
  · rw [h, Subgroup.index_top] at hi
    omega

theorem Cbar_eq_bot_of_rank_one [Finite G] [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a)
    (h57 : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ hSub T (normIn T₁ T), h * x * h⁻¹ = y)
    (hconj : ∃ x : G, T₁ = conjSubgroup x T) {ℓ a b y : G} (D : D8Data T T₁ ℓ a b y)
    {S : Sylow 2 G} (hS : SylowData T T₁ S)
    (hrank : ∀ α ∈ Cbar T T₁ S, ∀ β ∈ Cbar T T₁ S, α * α = 1 → β * β = 1 → α * β = β * α →
      α = 1 ∨ β = 1 ∨ α = β) : Cbar T T₁ S = ⊥ := by
  by_contra hne
  have hCS : Cbar T T₁ S ≤ (S : Subgroup G) := inf_le_left
  have hC2 : IsPGroup 2 (Cbar T T₁ S) := S.isPGroup'.to_le hCS
  have hNC : CFSG.DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
      ↥(Cbar T T₁ S) := by
    intro first second hcomm
    have h1 : orderOf ((first : ↥(Cbar T T₁ S)) : G) = 2 :=
      (Subgroup.orderOf_coe _).trans first.2
    have h2 : orderOf ((second : ↥(Cbar T T₁ S)) : G) = 2 :=
      (Subgroup.orderOf_coe _).trans second.2
    have hsq : ∀ x : G, orderOf x = 2 → x * x = 1 := fun x hx => by
      have := pow_orderOf_eq_one x
      rwa [hx, sq] at this
    have hne1 : ∀ x : G, orderOf x = 2 → x ≠ 1 := fun x hx h => by
      rw [h, orderOf_one] at hx
      omega
    rcases hrank _ (first : ↥(Cbar T T₁ S)).2 _ (second : ↥(Cbar T T₁ S)).2 (hsq _ h1) (hsq _ h2)
      (congrArg Subtype.val hcomm) with h | h | h
    · exact absurd h (hne1 _ h1)
    · exact absurd h (hne1 _ h2)
    · exact Subtype.ext (Subtype.ext h)
  rcases CFSG.DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion hC2 hNC with
    hcyc | ⟨_, -, ⟨ϕ⟩⟩
  ·
    obtain ⟨c, hcgen⟩ := hcyc.exists_generator
    have hCpow : ∀ x ∈ Cbar T T₁ S, ∃ j : ℤ, x = (c : G) ^ j := by
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
    have hdec : ∀ s ∈ (S : Subgroup G), ∃ d ∈ sStar T T₁, ∃ j : ℤ, s = d * (c : G) ^ j := by
      intro s hs
      obtain ⟨d, hd, c', hc', rfl⟩ := D.exists_split hS.norm hS.le hS.sStar_norm s hs
      obtain ⟨j, rfl⟩ := hCpow c' hc'
      exact ⟨d, hd, j, rfl⟩
    have hinf : ∀ d ∈ sStar T T₁, ∀ j : ℤ, d * (c : G) ^ j = 1 → d = 1 ∧ (c : G) ^ j = 1 := by
      intro d hd j h
      have hcj : (c : G) ^ j ∈ Cbar T T₁ S := Subgroup.zpow_mem _ c.2 j
      have hinv : (c : G) ^ j = d⁻¹ := eq_inv_of_mul_eq_one_right h
      have hmem : (c : G) ^ j ∈ sStar T T₁ ⊓ Cbar T T₁ S :=
        ⟨by rw [hinv]; exact (sStar T T₁).inv_mem hd, hcj⟩
      rw [D.sStar_inf_Cbar, Subgroup.mem_bot] at hmem
      refine ⟨?_, hmem⟩
      rw [hmem, mul_one] at h
      exact h
    have hcomm : ∀ d ∈ sStar T T₁, d * (c : G) = (c : G) * d := fun d hd =>
      comm_sStar_Cbar hd c.2
    have hfuse : ∀ g : G, ∀ z ∈ sStar T T₁, g⁻¹ * (c : G) ^ (orderOf (c : G) / 2) * g ≠ z := by
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
      have hzz : z * z = 1 := by
        rw [← h]
        calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
          _ = 1 := by rw [htt]; group
      have hz1 : z ≠ 1 := fun hz1 => by
        apply ht1
        calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
          _ = 1 := by rw [h, hz1]; group
      have hzD : z ∈ classD T := D.mem_classD_of_invol hz hzz hz1 hconj
      have htD : t ∈ classD T := by
        have := classD_conj hzD g⁻¹
        rw [← h] at this
        have e : g⁻¹⁻¹ * (g⁻¹ * t * g) * g⁻¹ = t := by group
        rwa [e] at this
      have htS : t ∈ (S : Subgroup G) := (S : Subgroup G).pow_mem hcS _
      have hts := hS.dS t htS htD
      have htC : t ∈ Cbar T T₁ S := Subgroup.pow_mem _ c.2 _
      have hmem : t ∈ sStar T T₁ ⊓ Cbar T T₁ S := ⟨hts, htC⟩
      rw [D.sStar_inf_Cbar, Subgroup.mem_bot] at hmem
      exact ht1 hmem
    obtain ⟨N, hN, hi⟩ := exists_index_two_of_cyclic_factor S.isPGroup' S.not_dvd_index hS.le hcS
      hc1 hdec hinf hcomm hfuse
    exact false_of_index_two hna hN hi
  · exact false_of_quaternion_cbar hna h57 hconj D hS ϕ

end CFSG.CGT.T75H
