module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneOrderFourOutside
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRelations

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

open CFSG.DisconnectedInvolutionGraph.Helpers

variable {Q : Type*} [Group Q] [Finite Q] {z : Q}

omit [Finite Q] in
theorem card_sq_eq_two_of_comm (hz : orderOf z = 2) (huniq : ∀ g : Q, g ^ 2 = 1 → g = 1 ∨ g = z)
    {H : Subgroup Q} (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {h₀ : Q} (hh₀ : h₀ ∈ H)
    (hh₀2 : h₀ ^ 2 = z) : Nat.card {g : Q // g ∈ H ∧ g ^ 2 = z} = 2 := by
  have hzH : z ∈ H := hh₀2 ▸ H.pow_mem hh₀ 2
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz; exact absurd hz (by decide)
  have hz2 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have e : {g : Q // g ∈ H ∧ g ^ 2 = z} ≃ {k : Q // k ∈ H ∧ k ^ 2 = 1} :=
    { toFun := fun g => ⟨h₀⁻¹ * g, H.mul_mem (H.inv_mem hh₀) g.2.1, by
        have hc : Commute h₀ g.1 := hcomm _ hh₀ _ g.2.1
        rw [hc.inv_left.mul_pow, g.2.2, inv_pow, hh₀2, inv_mul_cancel]⟩
      invFun := fun k => ⟨h₀ * k, H.mul_mem hh₀ k.2.1, by
        have hc : Commute h₀ k.1 := hcomm _ hh₀ _ k.2.1
        rw [hc.mul_pow, k.2.2, mul_one, hh₀2]⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }
  rw [Nat.card_congr e, Nat.card_eq_two_iff]
  refine ⟨⟨1, H.one_mem, one_pow 2⟩, ⟨z, hzH, hz2⟩, fun h => hz1 (congrArg Subtype.val h).symm, ?_⟩
  ext k
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases huniq k.1 k.2.2 with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)


theorem exists_sq_eq_of_four_le (hQ : IsPGroup 2 Q)
    (huniq : ∀ g : Q, g ^ 2 = 1 → g = 1 ∨ g = z) {H : Subgroup Q} (hH : 4 ≤ Nat.card H) :
    ∃ h ∈ H, h ^ 2 = z := by
  obtain ⟨h, hhH, hh1, hhz⟩ : ∃ h ∈ H, h ≠ 1 ∧ h ≠ z := by
    by_contra hcon
    push Not at hcon
    have hsub : (H : Set Q) ⊆ {1, z} := fun h hh => by
      by_cases h1 : h = 1
      · exact Or.inl h1
      · exact Or.inr (hcon h hh h1)
    have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h2
    have h3 : ({1, z} : Set Q).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    omega
  have hh2 : h ^ 2 ≠ 1 := fun h2 => by
    rcases huniq h h2 with h' | h'
    · exact hh1 h'
    · exact hhz h'
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hQ) h
  rcases m with _ | _ | k
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hm)) hh1
  · exact absurd (by rw [← pow_one 2, ← hm, pow_orderOf_eq_one]) hh2
  · refine ⟨h ^ (2 ^ k), H.pow_mem hhH _, ?_⟩
    have hsq : (h ^ (2 ^ k)) ^ 2 = h ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]
    rw [hsq]
    rcases huniq (h ^ (2 ^ (k + 1))) (by rw [← pow_mul, ← pow_succ, ← hm, pow_orderOf_eq_one])
      with h' | h'
    · exfalso
      have hdvd := orderOf_dvd_of_pow_eq_one h'
      rw [hm] at hdvd
      have := Nat.le_of_dvd (by positivity) hdvd
      have h4 : 2 ^ (k + 1) < 2 ^ (k + 1 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    · exact h'


omit [Finite Q] in
theorem card_sq_subgroup_eq {H : Subgroup Q} (hzH : z ∈ H) :
    Nat.card {g : Q // g ∈ H ∧ g ^ 2 = z} = Nat.card {h : H // h ^ 2 = ⟨z, hzH⟩} :=
  Nat.card_congr
    { toFun := fun g => ⟨⟨g.1, g.2.1⟩, Subtype.ext (by simpa using g.2.2)⟩
      invFun := fun h => ⟨h.1.1, h.1.2, by simpa using congrArg Subtype.val h.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_sq_eq_of_not_comm (hQ : IsPGroup 2 Q) (hz : orderOf z = 2)
    (huniq : ∀ g : Q, g ^ 2 = 1 → g = 1 ∨ g = z) {H : Subgroup Q} (hzH : z ∈ H)
    (hnc : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) :
    Nat.card {g : Q // g ∈ H ∧ g ^ 2 = z} = Nat.card H / 2 + 2 ∧ 8 ≤ Nat.card H := by
  classical
  have hp : IsPGroup 2 H := hQ.to_subgroup H
  set z' : H := ⟨z, hzH⟩
  have huniq' : ∀ g : H, g ^ 2 = 1 → g = 1 ∨ g = z' := fun g hg => by
    rcases huniq g.1 (by simpa using congrArg Subtype.val hg) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hz' : orderOf z' = 2 := by rw [← Subgroup.orderOf_coe]; exact hz
  have hrank : NoCommutingDistinctInvolutions H := by
    intro a b _
    have key : ∀ c : Involution H, (c : H) = z' := fun c => by
      have hc2 : (c : H) ^ 2 = 1 := by
        have h := pow_orderOf_eq_one (c : H)
        rwa [c.2] at h
      rcases huniq' c hc2 with h | h
      · exfalso
        have := c.2
        rw [h, orderOf_one] at this
        exact absurd this (by decide)
      · exact h
    exact Subtype.ext ((key a).trans (key b).symm)
  have hnonab : ∃ first second : H, first * second ≠ second * first := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  obtain ⟨N4, -, hN4cyc, hN4card, hidx, hcyc⟩ :=
    rank_one_two_exists_cyclic_index_two hp hrank hnonab
  set C := Subgroup.centralizer (N4 : Set H) with hC
  obtain ⟨e, heC, he4⟩ := rank_one_two_exists_order_four_outside_cyclic hp hrank hnonab C hcyc
  have he2 : e ^ 2 = z' := by
    have h1 : (e ^ 2) ^ 2 = 1 := by
      rw [← pow_mul, show 2 * 2 = orderOf e by rw [he4], pow_orderOf_eq_one]
    rcases huniq' _ h1 with h | h
    · exfalso
      have := orderOf_dvd_of_pow_eq_one h
      rw [he4] at this
      exact absurd this (by decide)
    · exact h
  have hout : ∀ w : H, w ∉ C → w ^ 2 = z' := fun w hw =>
    (rank_one_two_cyclic_index_two_outside_squares hp hrank hnonab C hidx hcyc e heC he4 w
      hw).trans he2
  have hN4C : N4 ≤ C := by
    intro a ha
    rw [hC, Subgroup.mem_centralizer_iff]
    intro b hb
    let _ := hN4cyc
    exact congrArg (fun inside : N4 => inside.val) (mul_comm' (⟨b, hb⟩ : N4) ⟨a, ha⟩)
  have hC4 : 4 ≤ Nat.card C := hN4card ▸ Subgroup.card_le_of_le hN4C
  have hHC : Nat.card C * 2 = Nat.card H := by
    rw [← hidx]
    exact C.card_mul_index
  have hCcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    let _ := hcyc
    exact congrArg (fun inside : C => inside.val) (mul_comm' (⟨a, ha⟩ : C) ⟨b, hb⟩)
  obtain ⟨h₀, hh₀C, hh₀2⟩ := exists_sq_eq_of_four_le hp huniq' hC4
  have hXC := card_sq_eq_two_of_comm hz' huniq' hCcomm hh₀C hh₀2
  have hsplit : Nat.card {h : H // h ^ 2 = z'} =
      Nat.card {h : H // h ∈ C ∧ h ^ 2 = z'} + Nat.card {h : H // h ∉ C} := by
    rw [← Nat.card_congr (Equiv.sumCompl fun a : {h : H // h ^ 2 = z'} => a.1 ∈ C),
      Nat.card_sum]
    congr 1
    · exact Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.2, a.1.2⟩
          invFun := fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    · exact Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.2⟩
          invFun := fun h => ⟨⟨h.1, hout h.1 h.2⟩, h.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
  have hcompl : Nat.card {h : H // h ∉ C} + Nat.card C = Nat.card H := by
    rw [← Nat.card_congr (Equiv.sumCompl fun h : H => h ∈ C), Nat.card_sum, add_comm]
  rw [card_sq_subgroup_eq hzH, hsplit, hXC]
  omega


omit [Finite Q] in
theorem card_sq_eq_zero_of_card_eq_two (hz : orderOf z = 2) {H : Subgroup Q}
    (hH : Nat.card H = 2) : Nat.card {g : Q // g ∈ H ∧ g ^ 2 = z} = 0 := by
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun g => ?_⟩
  have h : (⟨g.1, g.2.1⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  rw [hH] at h
  have h2 : g.1 ^ 2 = 1 := by simpa using congrArg Subtype.val h
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz; exact absurd hz (by decide)
  exact hz1 (g.2.2 ▸ h2)

theorem root_counts_arith {N₀ N₁ q : ℕ} (hq : 0 < q)
    (h : N₀ = 0 ∧ N₁ = 2 ∨ N₀ = 2 ∧ N₁ = 0 ∨ N₀ = 2 ∧ 4 ≤ N₁ ∨ 4 ≤ N₁ ∧ N₀ = N₁ + 2) :
    N₀ ≠ N₁ ∧ N₀ + q * N₁ ≠ 2 * q + 2 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h4⟩ | ⟨h4, rfl⟩
  · constructor <;> omega
  · constructor <;> omega
  · have : q * 4 ≤ q * N₁ := Nat.mul_le_mul_left q h4
    constructor <;> omega
  · have : q * 4 ≤ q * N₁ := Nat.mul_le_mul_left q h4
    constructor <;> omega

theorem root_counts_ne (hQ : IsPGroup 2 Q) (hz : orderOf z = 2)
    (huniq : ∀ g : Q, g ^ 2 = 1 → g = 1 ∨ g = z) {T : Subgroup Q} (hT : T.index = 2)
    (hzT : z ∈ T) {q : ℕ} (hq : 0 < q) :
    Nat.card {t : Q // t ∈ T ∧ t ^ 2 = z} ≠ Nat.card {w : Q // w ∉ T ∧ w ^ 2 = z} ∧
      Nat.card {t : Q // t ∈ T ∧ t ^ 2 = z} + q * Nat.card {w : Q // w ∉ T ∧ w ^ 2 = z} ≠
        2 * q + 2 := by
  classical
  have hQT : Nat.card T * 2 = Nat.card Q := by rw [← hT]; exact T.card_mul_index
  have hdvd : 2 ∣ Nat.card T := by
    have := orderOf_dvd_natCard (⟨z, hzT⟩ : T)
    rwa [Subgroup.orderOf_mk, hz] at this
  have hT2 : 2 ≤ Nat.card T := Nat.le_of_dvd Nat.card_pos hdvd
  have hsplit : Nat.card {g : Q // g ∈ (⊤ : Subgroup Q) ∧ g ^ 2 = z} =
      Nat.card {t : Q // t ∈ T ∧ t ^ 2 = z} + Nat.card {w : Q // w ∉ T ∧ w ^ 2 = z} := by
    rw [← Nat.card_congr (Equiv.sumCompl fun a : {g : Q // g ∈ (⊤ : Subgroup Q) ∧ g ^ 2 = z} =>
      a.1 ∈ T), Nat.card_sum]
    congr 1
    · exact Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.2, a.1.2.2⟩
          invFun := fun t => ⟨⟨t.1, Subgroup.mem_top _, t.2.2⟩, t.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    · exact Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.2, a.1.2.2⟩
          invFun := fun w => ⟨⟨w.1, Subgroup.mem_top _, w.2.2⟩, w.2.1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
  have hcardTop : Nat.card (⊤ : Subgroup Q) = Nat.card Q := Subgroup.card_top
  have hN₀ : (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) →
      Nat.card {t : Q // t ∈ T ∧ t ^ 2 = z} = if 4 ≤ Nat.card T then 2 else 0 := by
    intro hcomm
    split_ifs with h4
    · obtain ⟨h₀, hh₀, hh₀2⟩ := exists_sq_eq_of_four_le hQ huniq h4
      exact card_sq_eq_two_of_comm hz huniq hcomm hh₀ hh₀2
    · have hT2' : Nat.card T = 2 := by
        obtain ⟨k, hk⟩ := (hQ.to_subgroup T).exists_card_eq
        rcases k with _ | _ | k
        · rw [pow_zero] at hk; omega
        · simpa using hk
        · exfalso
          have : 4 ≤ 2 ^ (k + 2) := by
            calc 4 = 2 ^ 2 := rfl
              _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
      exact card_sq_eq_zero_of_card_eq_two hz hT2'
  refine root_counts_arith hq ?_
  by_cases hQc : ∀ a ∈ (⊤ : Subgroup Q), ∀ b ∈ (⊤ : Subgroup Q), a * b = b * a
  ·
    obtain ⟨h₀, hh₀, hh₀2⟩ := exists_sq_eq_of_four_le hQ huniq (H := ⊤) (by omega)
    have hX := card_sq_eq_two_of_comm hz huniq hQc hh₀ hh₀2
    have h0 := hN₀ fun a _ b _ => hQc a (Subgroup.mem_top a) b (Subgroup.mem_top b)
    rw [hX] at hsplit
    split_ifs at h0 <;> omega
  · push Not at hQc
    obtain ⟨hX, hQ8⟩ := card_sq_eq_of_not_comm hQ hz huniq (Subgroup.mem_top z) hQc
    rw [hcardTop] at hX hQ8
    rw [hX] at hsplit
    by_cases hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
    · have h0 := hN₀ hTc
      rw [ite_eq_left (by omega)] at h0
      omega
    · push Not at hTc
      obtain ⟨h0, hT8⟩ := card_sq_eq_of_not_comm hQ hz huniq hzT hTc
      omega

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
