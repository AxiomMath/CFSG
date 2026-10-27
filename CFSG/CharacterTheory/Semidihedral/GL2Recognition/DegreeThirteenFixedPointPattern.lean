module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.ThirteenPointPlaneAction
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.OrderThirtySixAction

public section

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.Assembly.LowTwoRank MulAction Pointwise

@[expose] def degreeThirteenBlocks (G Ω : Type*) [Group G] [MulAction G Ω] : Set (Set Ω) :=
  {S | ∃ g : G, orderOf g = 3 ∧ Nat.card (fixedBy Ω g) = 4 ∧ fixedBy Ω g = S}

section Blocks

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem fixingSubgroup_pair (x y : Ω) :
    fixingSubgroup G ({x, y} : Set Ω) = stabilizer G x ⊓ stabilizer G y := by
  ext g
  simp [mem_fixingSubgroup_iff, Subgroup.mem_inf, mem_stabilizer_iff]

theorem card_stabilizer_inf_stabilizer [Finite Ω] (hG : Nat.card G = 5616) (hΩ : Nat.card Ω = 13)
    (h2 : IsMultiplyPretransitive G Ω 2) {x y : Ω} (hxy : x ≠ y) :
    Nat.card (stabilizer G x ⊓ stabilizer G y : Subgroup G) = 36 := by
  have hncard : ({x, y} : Set Ω).ncard = 2 := Set.ncard_pair hxy
  have hidx := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := G) ({x, y} : Set Ω)
    (hncard ▸ h2)
  rw [hncard, hΩ, fixingSubgroup_pair] at hidx
  have hmul := Subgroup.card_mul_index (stabilizer G x ⊓ stabilizer G y)
  rw [hidx, hG, show (13 : ℕ).choose 2 * (2 : ℕ).factorial = 156 from rfl] at hmul
  omega

theorem fixedBy_subset_fixedBy_of_commute [Finite Ω] {a c : G} (hac : a * c = c * a)
    (hc3 : c ^ 3 = 1) (ha4 : (fixedBy Ω a).ncard = 4) {u v : Ω} (huv : u ≠ v)
    (hu : u ∈ fixedBy Ω a) (hv : v ∈ fixedBy Ω a) (hcu : c • u = u) (hcv : c • v = v) :
    fixedBy Ω a ⊆ fixedBy Ω c := by
  have hstable : ∀ z ∈ fixedBy Ω a, c • z ∈ fixedBy Ω a := fun z hz => by
    rw [mem_fixedBy] at hz ⊢
    rw [← mul_smul, hac, mul_smul, hz]
  intro x hx
  rw [mem_fixedBy]
  by_cases hxu : x = u
  · rw [hxu, hcu]
  by_cases hxv : x = v
  · rw [hxv, hcv]
  by_contra hxy
  set y := c • x with hy
  have hyx : y ≠ x := hxy
  have hyu : y ≠ u := fun h => hxu (smul_left_cancel c (h.trans hcu.symm))
  have hyv : y ≠ v := fun h => hxv (smul_left_cancel c (h.trans hcv.symm))
  have hya : y ∈ fixedBy Ω a := hstable x hx
  have h4 : ({u, v, x, y} : Set Ω).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [huv, Ne.symm hxu, Ne.symm hyu]),
      Set.ncard_insert_of_notMem (by simp [Ne.symm hxv, Ne.symm hyv]), Set.ncard_pair hyx.symm]
  have hsub : ({u, v, x, y} : Set Ω) ⊆ fixedBy Ω a := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hu
    · exact hv
    · exact hx
    · exact hya
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [ha4, h4]) (Set.toFinite _)
  have hcy : c • y ∈ ({u, v, x, y} : Set Ω) := heq ▸ hstable y hya
  have hcyx : c • y = x := by
    rcases hcy with h | h | h | h
    · exact absurd (smul_left_cancel c (h.trans hcu.symm)) hyu
    · exact absurd (smul_left_cancel c (h.trans hcv.symm)) hyv
    · exact h
    · exact absurd (smul_left_cancel c (h.trans hy)) hyx
  have h3 : (c ^ 3) • x = y := by
    rw [pow_succ, mul_smul, pow_two, mul_smul, ← hy, hcyx]
  rw [hc3, one_smul] at h3
  exact hyx h3.symm

end Blocks

theorem degree_thirteen_fixed_point_pattern_classical_recognition {G : Type} [Group G]
    (hG : Nat.card G = 5616) {Ω : Type*} [MulAction G Ω] (hΩ : Nat.card Ω = 13)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1) (h2 : IsMultiplyPretransitive G Ω 2)
    (hfix2 : ∀ g : G, orderOf g = 2 → Nat.card (fixedBy Ω g) = 5)
    (hfix3 : ∀ g : G, orderOf g = 3 → Nat.card (fixedBy Ω g) = 1 ∨ Nat.card (fixedBy Ω g) = 4)
    (hfix49 : ∀ g : G, orderOf g = 4 ∨ orderOf g = 9 → Nat.card (fixedBy Ω g) ≤ 1)
    (hfix6 : ∀ g : G, orderOf g = 6 → Nat.card (fixedBy Ω g) = 2) :
    (∀ g : G, ∀ b ∈ degreeThirteenBlocks G Ω,
        (fun u => g • u) '' b ∈ degreeThirteenBlocks G Ω) ∧
      (∀ b ∈ degreeThirteenBlocks G Ω, b.ncard = 4) ∧
      (∀ x y : Ω, x ≠ y → ∃! b, b ∈ degreeThirteenBlocks G Ω ∧ x ∈ b ∧ y ∈ b) ∧
      (∀ x y : Ω, x ≠ y → ∃ V : Sylow 3 (stabilizer G x ⊓ stabilizer G y : Subgroup G),
        (∀ W, W = V) ∧ Nat.card V = 9 ∧ (∀ a b : V, a * b = b * a) ∧ ∀ v : V, v ^ 3 = 1) ∧
      StatedClassicalModel G .PSL 3 3 1 := by
  have : Finite Ω := Nat.finite_of_card_ne_zero (by rw [hΩ]; norm_num)
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  have two_le : ∀ (g : G) {x y : Ω}, x ≠ y → g • x = x → g • y = y →
      2 ≤ Nat.card (fixedBy Ω g) := by
    intro g x y hxy hx hy
    rw [Nat.card_coe_set_eq, ← Set.ncard_pair hxy]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro z hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hloc : ∀ x y : Ω, x ≠ y →
      ∃ V : Sylow 3 (stabilizer G x ⊓ stabilizer G y : Subgroup G), (∀ W, W = V) ∧
        Nat.card V = 9 ∧ (∀ a b : V, a * b = b * a) ∧ (∀ v : V, v ^ 3 = 1) ∧
        ∀ a b : (stabilizer G x ⊓ stabilizer G y : Subgroup G), orderOf a = 3 →
          orderOf b = 3 → a * b = b * a := by
    intro x y hxy
    have hfixH : ∀ h : (stabilizer G x ⊓ stabilizer G y : Subgroup G),
        (h : G) • x = x ∧ (h : G) • y = y := fun h =>
      ⟨(Subgroup.mem_inf.mp h.2).1, (Subgroup.mem_inf.mp h.2).2⟩
    refine order_thirty_six_action_normal_three_subgroup
      (card_stabilizer_inf_stabilizer hG hΩ h2 hxy) ?_ ?_ hΩ ⟨x, y, hxy, hfixH⟩ ?_ ?_ ?_
    · intro h h4
      have := hfix49 h (Or.inl (by rw [Subgroup.orderOf_coe]; exact h4))
      have := two_le h hxy (hfixH h).1 (hfixH h).2
      omega
    · intro h h9
      have := hfix49 h (Or.inr (by rw [Subgroup.orderOf_coe]; exact h9))
      have := two_le h hxy (hfixH h).1 (hfixH h).2
      omega
    · intro h hh
      exact hfix2 h (by rw [Subgroup.orderOf_coe]; exact hh)
    · intro h hh
      rcases hfix3 h (by rw [Subgroup.orderOf_coe]; exact hh) with h1 | h4
      · have := two_le h hxy (hfixH h).1 (hfixH h).2
        omega
      · exact h4
    · intro h hh
      exact hfix6 h (by rw [Subgroup.orderOf_coe]; exact hh)
  have hB4 : ∀ b ∈ degreeThirteenBlocks G Ω, b.ncard = 4 := by
    rintro b ⟨g, -, hg4, rfl⟩
    rwa [← Nat.card_coe_set_eq]
  have hBG : ∀ g : G, ∀ b ∈ degreeThirteenBlocks G Ω,
      (fun u => g • u) '' b ∈ degreeThirteenBlocks G Ω := by
    rintro g b ⟨a, ha3, ha4, rfl⟩
    refine ⟨g * a * g⁻¹, ?_, ?_, ?_⟩
    · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact ha3
    · rw [← smul_fixedBy, Nat.card_coe_set_eq, ← Set.image_smul,
        Set.ncard_image_of_injective _ (MulAction.injective g), ← Nat.card_coe_set_eq, ha4]
    · rw [← smul_fixedBy, Set.image_smul]
  have hmem : ∀ x y : Ω, x ≠ y → ∃ b ∈ degreeThirteenBlocks G Ω, x ∈ b ∧ y ∈ b := by
    intro x y hxy
    obtain ⟨V, -, hV9, -, hV3, -⟩ := hloc x y hxy
    have : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV9]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : V)
    have hao : orderOf a = 3 := orderOf_eq_prime (hV3 a) ha
    have hgo : orderOf ((a : (stabilizer G x ⊓ stabilizer G y : Subgroup G)) : G) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hao]
    have hg := Subgroup.mem_inf.mp ((a : (stabilizer G x ⊓ stabilizer G y : Subgroup G))).2
    have hg4 : Nat.card (fixedBy Ω
        ((a : (stabilizer G x ⊓ stabilizer G y : Subgroup G)) : G)) = 4 := by
      rcases hfix3 _ hgo with h1 | h4
      · have := two_le _ hxy hg.1 hg.2
        omega
      · exact h4
    exact ⟨_, ⟨_, hgo, hg4, rfl⟩, hg.1, hg.2⟩
  have huniq : ∀ x y : Ω, x ≠ y → ∃! b, b ∈ degreeThirteenBlocks G Ω ∧ x ∈ b ∧ y ∈ b := by
    intro x y hxy
    obtain ⟨b, hb, hxb, hyb⟩ := hmem x y hxy
    refine ⟨b, ⟨hb, hxb, hyb⟩, ?_⟩
    rintro b' ⟨⟨c, hc3, hc4, rfl⟩, hxc, hyc⟩
    obtain ⟨a, ha3, ha4, rfl⟩ := hb
    obtain ⟨-, -, -, -, -, hcomm⟩ := hloc x y hxy
    have hac : a * c = c * a := congrArg Subtype.val
      (hcomm ⟨a, Subgroup.mem_inf.mpr ⟨hxb, hyb⟩⟩ ⟨c, Subgroup.mem_inf.mpr ⟨hxc, hyc⟩⟩
        (by rw [← Subgroup.orderOf_coe]; exact ha3) (by rw [← Subgroup.orderOf_coe]; exact hc3))
    have hsub := fixedBy_subset_fixedBy_of_commute hac (hc3 ▸ pow_orderOf_eq_one c)
      (by rw [← Nat.card_coe_set_eq, ha4]) hxy hxb hyb hxc hyc
    exact (Set.eq_of_subset_of_ncard_le hsub
      (by rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ha4, hc4]) (Set.toFinite _)).symm
  obtain ⟨-, -, -, -, hcm⟩ := thirteen_point_plane_action_classical_model hG hΩ hfaith
    (degreeThirteenBlocks G Ω) hBG hB4 huniq
  refine ⟨hBG, hB4, huniq, fun x y hxy => ?_, hcm⟩
  obtain ⟨V, h1, h2, h3, h4, -⟩ := hloc x y hxy
  exact ⟨V, h1, h2, h3, h4⟩

end CFSG.Semidihedral.GL2Recognition
