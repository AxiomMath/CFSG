module

public import CFSG.CharacterTheory.Semidihedral.Principal.TrivialCoreTorusTwentyNine
public import CFSG.CharacterTheory.BrauerLinearThree.TenThirtyOne
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveRegular
public import CFSG.CharacterTheory.Semidihedral.Principal.PureFivePowerNontrivialOddCore

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open
open CFSG.Semidihedral (r s)

theorem perfect_trivial_core_field_factor_one_parameter_cases
    {G : Type} [Group G] [Fintype G]
    [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 ∨ p ^ f = 11 ∨ p ^ f = 29 ∨ p ^ f = 31 := by
  set s₀ : G := (fS (s n) : G) with hs₀def
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s₀ with hVdef
  set D : Subgroup G := Subgroup.centralizer (V : Set G) with hDdef
  set W : Subgroup G := (CFSG.pPrimeCore 2 D).map D.subtype with hWdef
  set K : Subgroup G := Subgroup.centralizer (W : Set G) with hKdef
  have hdvd : Nat.card W ∣ (W.subgroupOf K).index :=
    trivial_core_torus_card_dvd_index n hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel
      hN hY
  obtain ⟨-, hW1, hWcyc, hWodd, hWcard, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      ⟨hcases, -⟩, -⟩ :=
    perfect_field_factor_one_trivial_core_torus_has_two_small_normalizer_quotients n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY
  have hW1 : W ≠ ⊥ := hW1
  have hWcyc : IsCyclic W := hWcyc
  have hWodd : Odd (Nat.card W) := hWodd
  have hqW : p ^ f + 1 = 2 * Nat.card W ∨ p ^ f = 2 * Nat.card W + 1 := by
    have h : (Nat.card W : ℤ) = (((p ^ f : ℕ) : ℤ) + if p ^ f % 4 = 1 then 1 else -1) / 2 :=
      hWcard
    obtain ⟨k, hk⟩ := hpodd.pow (n := f)
    by_cases h1 : p ^ f % 4 = 1
    · rw [ite_eq_left h1] at h
      left
      omega
    · rw [ite_eq_right h1] at h
      right
      omega
  have hcases : Nat.card K = 12 * Nat.card W ∨ Nat.card K = 60 * Nat.card W := by
    rcases hcases with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hWK : W ≤ K := fun w hw =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => hWcomm x hx w hw
  have hindex : Nat.card K = (W.subgroupOf K).index * Nat.card W := by
    have h := Subgroup.card_mul_index (W.subgroupOf K)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWK).toEquiv] at h
    rw [← h, mul_comm]
  have hW15 : Nat.card W ∣ 15 := by
    have hW0 : 0 < Nat.card W := Nat.card_pos
    have h60 : (W.subgroupOf K).index ∣ 2 ^ 2 * 15 := by
      rcases hcases with h | h
      · rw [h] at hindex
        rw [← Nat.eq_of_mul_eq_mul_right hW0 hindex]
        norm_num
      · rw [h] at hindex
        rw [← Nat.eq_of_mul_eq_mul_right hW0 hindex]
        norm_num
    exact Nat.Coprime.dvd_of_dvd_mul_left
      (Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hWodd)) (hdvd.trans h60)
  have hWgt : 1 < Nat.card W := (Subgroup.one_lt_card_iff_ne_bot W).mpr hW1
  have hm : Nat.card W = 3 ∨ Nat.card W = 5 ∨ Nat.card W = 15 := by
    have hle := Nat.le_of_dvd (by norm_num) hW15
    obtain ⟨m, hm⟩ : ∃ m, Nat.card W = m := ⟨_, rfl⟩
    rw [hm] at hle hW15 hWgt ⊢
    interval_cases m <;> omega
  rcases hm with h | h | h <;> rcases hqW with h' | h' <;> omega

theorem perfect_trivial_core_field_factor_one_parameter_five_or_seven
    {G : Type} [Group G]
    [Finite G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    p ^ f = 5 ∨ p ^ f = 7 := by
  have := Fintype.ofFinite G
  rcases perfect_trivial_core_field_factor_one_parameter_cases n hn S fS t ht hnonab hcentral hnc
      p f hp hpodd hf hq hmodel hN hY with h5 | h7 | h9 | h11 | h29 | h31
  · exact Or.inl h5
  · exact Or.inr h7
  · exact absurd hN (perfect_field_factor_one_pure_five_power_parameter_has_nontrivial_odd_core n
      hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hY 1 le_rfl
      (by rw [h9]; norm_num))
  · exact absurd hN (perfect_field_factor_one_pure_five_power_parameter_has_nontrivial_odd_core n
      hn S fS t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel hY 1 le_rfl
      (by rw [h11]; norm_num))
  · exact (perfect_trivial_core_field_factor_one_parameter_ne_twentynine n hn S fS t ht hnonab
      hcentral hnc p f hp hpodd hf h29 hmodel hN hY).elim
  · exact (BrauerLinearThree.false_of_field_card_thirtyone n hn S fS t ht hnonab hcentral hnc p f
      hp hpodd hf h31 hmodel hN hY).elim

theorem perfect_trivial_core_field_factor_one_parameter_five_or_seven_regular
    {G : Type}
    [Group G] [Finite G] [Group.IsPerfect G]
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    p ^ f = 5 ∨
      (p ^ f = 7 ∧
        (padicValNat p (Nat.card G) : ℤ) =
          3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) : ℤ) -
            2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
              Subgroup.centralizer ({(fS (s n) : G)} : Set G) : Subgroup G)) : ℤ)) := by
  have := Fintype.ofFinite G
  rcases perfect_trivial_core_field_factor_one_parameter_five_or_seven n hn S fS t ht hnonab
      hcentral hnc p f hp hpodd hf hq hmodel hN hY with h5 | h7
  · exact Or.inl h5
  · refine Or.inr ⟨h7, ?_⟩
    obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).mp h7
    obtain ⟨-, -, -, -, -, hval⟩ :=
      perfect_local_parameter_seven_with_five_free_odd_core_is_regular n hn S fS t ht hnonab
        hcentral hnc hmodel (by rw [hN]; simp)
    exact hval

theorem simple_trivial_core_field_factor_one_is_regular
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 3 < p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (hN : N t = ⊥)
    (hY : (((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).index = 2) :
    (p ^ f = 5 ∨ p ^ f = 7) ∧
      (padicValNat p (Nat.card G) : ℤ) =
        3 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G))) : ℤ) -
          2 * (padicValNat p (Nat.card (Subgroup.centralizer ({t} : Set G) ⊓
            Subgroup.centralizer ({(fS (s n) : G)} : Set G) : Subgroup G)) : ℤ) := by
  have := Fintype.ofFinite G
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  rcases perfect_trivial_core_field_factor_one_parameter_five_or_seven_regular n hn S fS t ht
      hnonab hcentral hnc p f hp hpodd hf hq hmodel hN hY with h5 | ⟨h7, hval⟩
  · refine ⟨Or.inl h5, ?_⟩
    obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 5)).mp h5
    obtain ⟨-, -, -, -, -, -, hval⟩ :=
      simple_local_parameter_five_is_regular_with_exact_order hGnonab n hn S fS t ht hnonab
        hcentral hnc hmodel
    exact hval
  · exact ⟨Or.inr h7, hval⟩

end CFSG.Semidihedral.Principal
