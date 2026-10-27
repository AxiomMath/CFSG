module

public import CFSG.CharacterTheory.Wreathed.QuaternionOvergroupsSupport

public section

namespace CFSG.Wreathed.QuaternionOvergroups

open CFSG.Wreathed.Original CFSG.Wreathed.CyclicDisjointActor

theorem proper_overgroups_of_maximal_quaternion_have_no_odd_abelian_centric_automorphisms
    (n : ℕ) (hn : 2 ≤ n) :
    (Nonempty (QuaternionGroup (2 ^ n / 2) ≃* Y (2 ^ n)) ∧
      ∀ Y₁ : Subgroup (Wreath (2 ^ n)), Nonempty (QuaternionGroup (2 ^ n / 2) ≃* Y₁) →
        Y₁ = Y (2 ^ n)) ∧
    ∀ P : Subgroup (Wreath (2 ^ n)), Y (2 ^ n) ≤ P → P < ⊤ →
      (∃! k : ℕ, k < n ∧ (Y (2 ^ n)).relIndex P = 2 ^ k) ∧
      (∀ k : ℕ, k < n → (Y (2 ^ n)).relIndex P = 2 ^ k →
        (P ⊓ U (2 ^ n) = Subgroup.closure {r (2 ^ n), s (2 ^ n) ^ (2 ^ (n - k))} ∧
          Nonempty ((P ⊓ U (2 ^ n) : Subgroup (Wreath (2 ^ n))) ≃*
            Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ k)))) ∧
        ((Subgroup.center P).map P.subtype = P ⊓ Z (2 ^ n) ∧
          P ⊓ Z (2 ^ n) = Subgroup.zpowers (a (2 ^ n) ^ (2 ^ (n - k) / 2)) ∧
          Nat.card (Subgroup.center P) = 2 ^ (k + 1)) ∧
        ∀ u ∈ P, u ∉ U (2 ^ n) →
          (k = 0 → IsCyclic (P ⊓ Subgroup.centralizer {u} : Subgroup (Wreath (2 ^ n))) ∧
            Nat.card (P ⊓ Subgroup.centralizer {u} : Subgroup (Wreath (2 ^ n))) = 4) ∧
          (1 ≤ k → Nonempty ((P ⊓ Subgroup.centralizer {u} : Subgroup (Wreath (2 ^ n))) ≃*
            Multiplicative (ZMod (2 ^ (k + 1))) × Multiplicative (ZMod 2)))) ∧
      (∀ A : Subgroup (Wreath (2 ^ n)), A ≤ P → IsMulCommutative A →
        P ⊓ Subgroup.centralizer (A : Set (Wreath (2 ^ n))) = A → IsPGroup 2 (MulAut A)) ∧
      ∀ A : Subgroup (Wreath (2 ^ n)), A ≤ P → (∃ u v : A, u * v ≠ v * u) →
        P ⊓ Subgroup.centralizer (A : Set (Wreath (2 ^ n))) =
          (Subgroup.center A).map A.subtype →
        (Subgroup.center A).map A.subtype = (Subgroup.center P).map P.subtype ∧
          IsCyclic (Subgroup.center A) ∧ x (2 ^ n) ∈ (Subgroup.center A).map A.subtype ∧
          (∀ g ∈ (Subgroup.center A).map A.subtype, orderOf g = 2 → g = x (2 ^ n)) ∧
          ∃ hx : x (2 ^ n) ∈ A, ∀ φ : MulAut A, φ ⟨x (2 ^ n), hx⟩ = ⟨x (2 ^ n), hx⟩ := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hN : 1 ≤ N := by omega
  have hstr := wreath_center_involution_and_quaternion_coordinates (N + 1) hn
  refine ⟨⟨hstr.quaternion, fun Y₁ hY₁ => ?_⟩, fun P hYP hP => ?_⟩
  · rw [half_eq] at hY₁
    obtain ⟨e⟩ := hY₁
    exact quaternion_unique N hN Y₁ e
  have hPnonab : ∃ u v : P, u * v ≠ v * u := by
    obtain ⟨u, v, huv⟩ := originalY_is_nonabelian (N + 1) hn
    refine ⟨⟨u, hYP u.2⟩, ⟨v, hYP v.2⟩, fun h => huv ?_⟩
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  refine ⟨overgroup_relIndex N hN P hYP hP, fun k hk hkP => ?_, fun A hAP habel hcent => ?_,
    fun A hAP hA hcent => nonabelian_centric N hN P hYP A hAP hA hcent⟩
  · obtain ⟨j, hj⟩ : ∃ j, j = N + 1 - k := ⟨_, rfl⟩
    have hkj : k + j = N + 1 := by omega
    have hj1 : 1 ≤ j := by omega
    rw [← hj]
    have hZP := (hstr.nonabelian_centralizers P hPnonab).2
    have hPeq := overgroup_eq_ker N hN P hYP k j hkj (hkj ▸ Nat.le_add_left j k) hkP
    subst hPeq
    have hhalf : 2 ^ j / 2 = 2 ^ (j - 1) := by rw [← Nat.pow_div hj1 two_pos, pow_one]
    have hZ := ker_nuMod_inf_center N j hj1 (by omega)
    refine ⟨⟨ker_nuMod_inf_base N j _, ker_nuMod_inf_base_equiv N k j hkj⟩,
      ⟨hZP, by rw [hhalf]; exact hZ, ?_⟩, ?_⟩
    · rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hZP, hZ,
        Nat.card_zpowers, orderOf_center_generator N k j hkj hj1]
    · intro u hu huU
      obtain ⟨p, q, eu, rfl⟩ := exists_element u
      rw [U_eq, element_mem_base] at huU
      have heu : eu = 1 := (swap_exponent_cases eu).resolve_left huU
      subst heu
      refine ⟨fun hk0 => ?_, fun hk1 => centralizer_swap_equiv N k j hkj hj1 hk1 p q hu⟩
      obtain rfl : j = N + 1 := by omega
      exact centralizer_swap_cyclic N p q hu
  · obtain ⟨k, ⟨hk, hkP⟩, -⟩ := overgroup_relIndex N hN P hYP hP
    have hkj : k + (N + 1 - k) = N + 1 := Nat.add_sub_of_le hk.le
    have hPeq := overgroup_eq_ker N hN P hYP k (N + 1 - k) hkj (Nat.sub_le (N + 1) k) hkP
    subst hPeq
    exact abelian_centric_isPGroup N hN k (N + 1 - k) hkj (by omega) A hAP habel hcent

end CFSG.Wreathed.QuaternionOvergroups
