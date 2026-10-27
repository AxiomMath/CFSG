module

public import CFSG.GH74.Uniqueness.Section15HeringEnd1
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CosetNormalizerOrder168
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω] {ω : Ω} {K P : Subgroup G}

theorem EndHyp.card_group_three [Finite G] (h : EndHyp G Ω 3 ω K P) : Nat.card G = 168 := by
  rw [h.card_group]
  norm_num

theorem EndHyp.orderOf_ne_six [Finite G] (h : EndHyp G Ω 3 ω K P) (g : G) : orderOf g ≠ 6 := by
  intro hg
  have ht : orderOf (g ^ 3) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hy : orderOf (g ^ 2) = 3 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  exact h.mul_ne_of_orderOf_eq_two ht Nat.prime_three (by norm_num) hy
    ((Commute.pow_pow_self g 3 2).eq)

theorem EndHyp.eq_top_of_normal [Finite G] (h : EndHyp G Ω 3 ω K P) (N : Subgroup G)
    [hN : N.Normal] (hN1 : N ≠ ⊥) : N = ⊤ := by
  have := h.faithful
  have hpre := isPretransitive_of_normal h.twoTrans N hN1
  have h8 : 8 ∣ Nat.card N := by
    have h1 := (stabilizer N ω).index_dvd_card
    rw [index_stabilizer, orbit_eq_univ, Set.ncard_univ, h.card] at h1
    simpa using h1
  have h168 : Nat.card N ∣ 168 := h.card_group_three ▸ Subgroup.card_subgroup_dvd_card N
  by_contra htop
  have hlt : Nat.card N < 168 := by
    rw [← h.card_group_three]
    exact lt_of_le_of_ne N.card_le_card_group (fun heq => htop (N.eq_top_of_le_card heq.ge))
  obtain ⟨k, hk⟩ := h8
  have hk21 : k ∣ 21 := by
    rw [hk] at h168
    have : 8 * k ∣ 8 * 21 := h168
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
  have hk' : k < 21 := by omega
  have hsol : Group.IsSolvable N := by
    have : Fintype N := Fintype.ofFinite N
    have hcard : Fintype.card N = Nat.card N := Nat.card_eq_fintype_card.symm
    have hk3 : k = 1 ∨ k = 3 ∨ k = 7 := by
      have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hk21 (by norm_num)
      interval_cases k <;> first | (left; rfl) | (right; left; rfl) | (right; right; rfl) |
        (exfalso; norm_num at hk21)
    rcases hk3 with rfl | rfl | rfl
    · exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (a := 3) (b := 0) Nat.prime_two Nat.prime_three (by norm_num) (by rw [hcard, hk]; norm_num)
    · exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) (by rw [hcard, hk]; norm_num)
    · exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
        (a := 3) (b := 1) Nat.prime_two (by norm_num : Nat.Prime 7) (by norm_num)
        (by rw [hcard, hk]; norm_num)
  exact hN1 (h.solvable N hN hsol)

theorem EndHyp.nonempty_mulEquiv_GL [Finite G] (h : EndHyp G Ω 3 ω K P) :
    Nonempty (G ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  have hcard := h.card_group_three
  have hnt : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  have hsimple : IsSimpleGroup G := by
    refine ⟨fun N hN => ?_⟩
    by_cases hN1 : N = ⊥
    · exact Or.inl hN1
    · exact Or.inr (h.eq_top_of_normal N hN1)
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hsol : Group.IsSolvable (⊤ : Subgroup G) := by
      have : Group.IsSolvable G := Group.isSolvable_of_comm hcon
      infer_instance
    have := h.solvable ⊤ inferInstance hsol
    have h1 : Nat.card (⊤ : Subgroup G) = 1 := by rw [this, Subgroup.card_bot]
    rw [Subgroup.card_top, hcard] at h1
    omega
  obtain ⟨G', _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  have : Finite G' := Finite.of_equiv G e.toEquiv
  have : IsSimpleGroup G' := e.isSimpleGroup_congr.mp hsimple
  have hnonab' : ∃ a b : G', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e a, e b, fun h' => hab (e.injective ?_)⟩
    rw [map_mul, map_mul, h']
  have hcard' : Nat.card G' = 168 := (Nat.card_congr e.toEquiv).symm.trans hcard
  have hsix' : ∀ g : G', orderOf g ≠ 6 := by
    intro g
    rw [← MulEquiv.orderOf_eq e.symm g]
    exact h.orderOf_ne_six _
  obtain ⟨-, -, -, φ, -⟩ :=
    CFSG.ProperTwoGeneratedCore.CosetNormalizer.simple_order_168_without_six_projective_seven_recognition
      G' hnonab' hcard' hsix'
  obtain ⟨ψ⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨(e.trans φ).trans ψ.symm⟩

end CFSG.GH74.Uniqueness.Hering
