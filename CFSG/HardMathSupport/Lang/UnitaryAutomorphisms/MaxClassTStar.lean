module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.MaxClassBridge
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.MaxClassRankBound

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

variable {G : Type} [Group G] [Finite G]

theorem card_elemAbelian_lt_27 (hG : IsPGroup 3 G) {x : G} (hx3 : x ^ 3 = 1)
    (hCx : Nat.card (Subgroup.centralizer ({x} : Set G)) = 9)
    {M : Subgroup G} [M.Normal] (hMi : M.index = 3) (hxM : x ∉ M) (hM81 : 81 ≤ Nat.card M)
    {E : Subgroup G} (hEM : E ≤ M) (hE : IsMulCommutative E ∧ ∀ e ∈ E, e ^ 3 = 1) :
    Nat.card E < 27 := by
  have _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn5, hcard, hne, S⟩ := cubeSetup_of_card_centralizer hG hx3 hCx hMi hxM hM81
  by_contra h27
  push Not at h27
  set L1 := (⊤ : Subgroup G).lowerCentralSeries 1 with hL1
  have hM := lcs_one_le_of_index_prime hMi
  have hnc := two_dvd_index_lcs_one hG (by omega) hcard hne
  have hL : ∀ k, 1 ≤ k → k ≤ n - 1 →
      Nat.card ((⊤ : Subgroup G).lowerCentralSeries k) = 3 ^ (n - 1 - k) :=
    fun k hk1 hk => card_lcs_eq hG hcard hne hnc hk1 hk
  have hΩ : Nat.card ((⊤ : Subgroup G).lowerCentralSeries (n - 3)) = 9 := by
    rw [hL (n - 3) (by omega) (by omega), show n - 1 - (n - 3) = 2 by omega]; norm_num
  have hinter : L1 ⊓ E ≤ (⊤ : Subgroup G).lowerCentralSeries (n - 3) := by
    intro z hz
    exact lcs_pow_three_eq_one_mem hG (by omega) hcard hne hx3 hCx hMi hxM (by omega) hz.1 (hE.2 z hz.2)
  have hc9 : Nat.card (L1 ⊓ E : Subgroup G) ≤ 9 := hΩ ▸ Subgroup.card_le_of_le hinter
  have hrelM : L1.relIndex M = 3 := by
    have hmul := Subgroup.relIndex_mul_card (H := L1) (K := M)
    rw [inf_of_le_left hM, hL 1 le_rfl (by omega)] at hmul
    have hMcard : Nat.card M * 3 = 3 ^ n := by
      have := Subgroup.card_mul_index M
      rwa [hMi, hcard] at this
    have h3 : 3 ^ n = 3 ^ (n - 1) * 3 := by rw [← pow_succ]; congr 1; omega
    have hMc : Nat.card M = 3 ^ (n - 1) := by
      rw [h3] at hMcard; exact Nat.eq_of_mul_eq_mul_right (by norm_num) hMcard
    rw [hMc, show n - 1 - 1 = n - 2 by omega] at hmul
    have h4 : 3 ^ (n - 1) = 3 * 3 ^ (n - 2) := by rw [← pow_succ']; congr 1; omega
    rw [h4] at hmul
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num : 0 < 3) (n - 2)) hmul
  have hrel3 : L1.relIndex E ≤ 3 := by
    rw [← hrelM]
    exact Subgroup.relIndex_le_of_le_right hEM (by rw [hrelM]; norm_num)
  have hmulE := Subgroup.relIndex_mul_card (H := L1) (K := E)
  have hEcard : L1.relIndex E * Nat.card (L1 ⊓ E : Subgroup G) = Nat.card E := hmulE
  have hr3 : L1.relIndex E = 3 ∧ Nat.card (L1 ⊓ E : Subgroup G) = 9 := by
    generalize L1.relIndex E = r at *
    generalize Nat.card (L1 ⊓ E : Subgroup G) = c at *
    interval_cases r <;> omega
  obtain ⟨y, hyE, hyL⟩ : ∃ y ∈ E, y ∉ L1 := by
    by_contra hall
    push Not at hall
    have : L1.relIndex E = 1 := Subgroup.relIndex_eq_one.2 hall
    omega
  have hEq : L1 ⊓ E = (⊤ : Subgroup G).lowerCentralSeries (n - 3) :=
    Subgroup.eq_of_le_of_card_ge hinter (by rw [hΩ, hr3.2])
  have hcent : ∀ z ∈ lcsFil M (n - 2), y * z = z * y := by
    intro z hz
    rw [lcsFil_of_gt (by omega), show n - 2 - 1 = n - 3 by omega] at hz
    have hzE : z ∈ E := by
      have : z ∈ L1 ⊓ E := hEq ▸ hz
      exact this.2
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨y, hyE⟩ : E) ⟨z, hzE⟩)
  exact S.false_of_order_three hn5 (by rw [lcsFil_of_le le_rfl]; exact hEM hyE)
    (by rw [lcsFil_of_gt (by omega)]; exact hyL) (hE.2 y hyE)
    (fun j hj w hw => lcsFil_cx_mem M y⁻¹ (by omega) hw) hcent

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
