module

public import CFSG.LocalAnalysis.ComponentInitial.RefinedOddCoreSelection
public import CFSG.LocalAnalysis.ComponentInitial.SplitCentralSecondDiagonal

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.Assembly (IsComponentOf IsElemAbelian)
open CFSG.Assembly.ComponentType (IsTwoPComponent)

variable {G : Type*} [Group G]

theorem pRank_coe_le_of_pRank_le [Finite G] {J : Subgroup G} {r : ℕ}
    (hr : CFSG.Assembly.pRank 2 J ≤ r) : CFSG.pRank 2 J ≤ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine pRank_le_of_forall_card_le one_lt_two fun E hE => ?_
  have hE' : IsElemAbelian 2 (E.map J.subtype) :=
    isElemAbelian_map (isElemAbelian_iff_isElementaryAbelian.mpr hE) _
  rw [← card_map_of_injective J.subtype_injective]
  exact (card_le_pow_pRank_of_le (map_subtype_le E) hE').trans (Nat.pow_le_pow_right two_pos hr)

theorem coe_mem_centralizer_of_mem_center {J : Subgroup G} {z : J} (hz : z ∈ center J) :
    (z : G) ∈ centralizer (J : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)

theorem card_le_two_of_lt_four [Finite G] {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E < 4) : Nat.card E ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (isPGroup_of_isElemAbelian hE).exists_card_eq
  rw [hk] at h4 ⊢
  rcases k with _ | _ | k
  · norm_num
  · norm_num
  · rw [pow_succ, pow_succ] at h4
    have := Nat.one_le_two_pow (n := k)
    omega

theorem rank_one_selected_quaternion {C : CFSG.Assembly.GroupProp}
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (hB : CFSG.Assembly.ComponentType.LocalBProperty G)
    {a : G} (ha : orderOf a = 2) {J A : Subgroup G}
    (hJ : IsComponentOf J (centralizer ({a} : Set G))) (hAe : IsElemAbelian 2 A) (haA : a ∈ A)
    (hmax : RefinedMaxima J A)
    (hcent : ∀ c ∈ J, c ∈ centralizer (J : Set G) → orderOf c = 2 → c ∈ A)
    (hcases : ∀ b ∈ A, b ≠ 1 → ∃ L : Subgroup G, IsComponentOf L (centralizer ({b} : Set G)) ∧
      IsTwoPComponent (L.subgroupOf (centralizer ({b} : Set G))) ∧
      (L = J ∨ (conjSub a⁻¹ L ≠ L ∧ (J : Set G) = {g | ∃ x ∈ L, x * (a⁻¹ * x * a) = g} ∧
        Nonempty (J ⧸ center J ≃* L ⧸ center L) ∧
        (CFSG.Assembly.oddCore L).index = (CFSG.Assembly.oddCore J).index ∧
        (∃ δ : L →* J, (∀ x : L, (δ x : G) = x * (a⁻¹ * x * a)) ∧
          Function.Surjective δ ∧ Odd (Nat.card δ.ker)) ∧
        CFSG.Assembly.pRank 2 J = 1 ∧ CFSG.Assembly.pRank 2 L = 1)))
    (hr : CFSG.Assembly.pRank 2 J ≤ 1) :
    ∃ c : G, orderOf c = 2 ∧ ∃ L : Subgroup G,
      IsComponentOf L (centralizer ({c} : Set G)) ∧ c ∈ L ∧ c ∈ centralizer (L : Set G) ∧
        ∃ r : ℕ, 3 ≤ r ∧ ∃ T : Sylow 2 L,
          Nonempty ((T : Subgroup L) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨z, hz, hzuniq⟩, hzcent, hquat⟩ := quasisimple_rank_one_unique_central_involution
    ((AssemblyBPredicates.isQuasisimple_iff_native J).1 hJ.2.2) (pRank_coe_le_of_pRank_le hr)
  have hz' : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hzC : (z : G) ∈ centralizer (J : Set G) := coe_mem_centralizer_of_mem_center (hzcent z hz)
  have hzA : (z : G) ∈ A := hcent z z.2 hzC hz'
  have hz1 : (z : G) ≠ 1 := fun h => by rw [h, orderOf_one] at hz'; exact absurd hz' (by norm_num)
  obtain ⟨L, hL, -, hLJ | ⟨hLa, -, hiso, -, ⟨δ, hδ, -, hodd⟩, -, hL1⟩⟩ := hcases z hzA hz1
  ·
    subst hLJ
    obtain ⟨r, hr3, hT⟩ := hquat default
    exact ⟨z, hz', L, hL, z.2, hzC, r, hr3, default, hT⟩
  ·
    obtain ⟨-, ⟨c, hc, -⟩, hccent, hquatL⟩ := quasisimple_rank_one_unique_central_involution
      ((AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2)
      (pRank_coe_le_of_pRank_le hL1.le)
    have hc' : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hc
    have hcC : (c : G) ∈ centralizer (L : Set G) := coe_mem_centralizer_of_mem_center (hccent c hc)
    have hc2 : c ^ 2 = 1 := hc ▸ pow_orderOf_eq_one c
    have hδc : orderOf (δ c) = 2 := by
      refine orderOf_eq_prime (by rw [← map_pow, hc2, map_one]) fun h1 => ?_
      have hord : orderOf (⟨c, h1⟩ : δ.ker) = 2 :=
        (Subgroup.orderOf_coe (⟨c, h1⟩ : δ.ker)).symm.trans hc
      have h2 := orderOf_dvd_natCard (⟨c, h1⟩ : δ.ker)
      rw [hord] at h2
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
    have hzc : (z : G) = c * (a⁻¹ * c * a) := by rw [← hzuniq _ hδc, hδ]
    have hab : a * z = z * a := congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, haA⟩ ⟨z, hzA⟩)
    have hd : (center L).index = (center J).index := by
      obtain ⟨e⟩ := hiso
      rw [index_eq_card, index_eq_card]
      exact (Nat.card_congr e.toEquiv).symm
    have hLc := split_central_involution_prevents_second_diagonal hC hpump hK hB ha hz' hab hL
      hLa c.2 hcC hc' hzc fun t ht Q hQ => hd ▸ hmax.1 t ht Q hQ
    obtain ⟨r, hr3, hT⟩ := hquatL default
    exact ⟨c, hc', L, hLc, c.2, hcC, r, hr3, default, hT⟩

theorem initial_component_constant_on_selected_four_group_reduction
    {C : CFSG.Assembly.GroupProp} (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    (∃ a : G, orderOf a = 2 ∧ ∃ J : Subgroup G,
        IsComponentOf J (centralizer ({a} : Set G)) ∧
          CFSG.Assembly.ComponentType.IsStandardSubgroup J) ∨
      (∃ c : G, orderOf c = 2 ∧ ∃ L : Subgroup G,
        IsComponentOf L (centralizer ({c} : Set G)) ∧ c ∈ L ∧ c ∈ centralizer (L : Set G) ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ T : Sylow 2 L,
            Nonempty ((T : Subgroup L) ≃* QuaternionGroup (2 ^ (r - 2)))) ∨
      ∃ a : G, orderOf a = 2 ∧ ∃ J : Subgroup G, IsComponentOf J (centralizer ({a} : Set G)) ∧
        IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))) ∧
        ∃ A : Subgroup G, A ≤ centralizer (J : Set G) ∧ IsElemAbelian 2 A ∧ a ∈ A ∧
          4 ≤ Nat.card A ∧ 2 ≤ CFSG.Assembly.pRank 2 J ∧
          (∀ b ∈ A, b ≠ 1 → IsComponentOf J (centralizer ({b} : Set G))) ∧
          RefinedMaxima J A ∧
          ∀ c ∈ J, c ∈ centralizer (J : Set G) → orderOf c = 2 → c ∈ A := by
  obtain ⟨a, ha, J, hJ, hJp, A, hAC, hAe, haA, hmax, hcent, hcases⟩ :=
    refined_odd_core_index_selection_diagonal_rank_one hC hpump hK hcomp hB
  by_cases hr : CFSG.Assembly.pRank 2 J ≤ 1
  · exact Or.inr (Or.inl (rank_one_selected_quaternion hC hpump hK hB ha hJ hAe haA hmax hcent
      hcases hr))
  have hr2 : 2 ≤ CFSG.Assembly.pRank 2 J := by omega
  have hall : ∀ b ∈ A, b ≠ 1 → IsComponentOf J (centralizer ({b} : Set G)) := by
    intro b hbA hb1
    obtain ⟨L, hL, -, hLJ | ⟨-, -, -, -, -, hJ1, -⟩⟩ := hcases b hbA hb1
    · exact hLJ ▸ hL
    · omega
  by_cases hA4 : 4 ≤ Nat.card A
  · exact Or.inr (Or.inr ⟨a, ha, J, hJ, hJp, A, hAC, hAe, haA, hA4, hr2, hall, hmax, hcent⟩)
  have hE : ∀ E : Subgroup G, E ≤ centralizer (J : Set G) → IsElemAbelian 2 E → a ∈ E →
      Nat.card E ≤ 2 := fun E hEC hEe haE =>
    card_le_two_of_lt_four hEe ((hmax.2.2 a ha J hJ hJp rfl rfl E hEC hEe haE).trans_lt
      (by omega))
  rcases rank_one_centralizer_standard_or_quaternion ha hJ
      (pRank_centralizer_eq_one_of_no_four_group ha hJ hE) with
    hstd | ⟨z, hz, hzJ, hzC, hJz, r, hr3, T, hT⟩
  · exact Or.inl ⟨a, ha, J, hJ, hstd⟩
  · exact Or.inr (Or.inl ⟨z, hz, J, hJz, hzJ, hzC, r, hr3, T, hT⟩)

theorem initial_component_constant_on_selected_four_group_reduction_frontier
    {C : CFSG.Assembly.GroupProp} (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hpump : KProperOrdinaryLocalBPumpUp C) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Assembly.KProper C G) (hcomp : CFSG.Assembly.IsComponentType G)
    (hB : CFSG.Assembly.ComponentType.LocalBProperty G) :
    (∃ t : G, orderOf t = 2 ∧ ∃ L : Subgroup G,
        IsComponentOf L (Subgroup.centralizer ({t} : Set G)) ∧
          CFSG.Assembly.ComponentType.IsStandardSubgroup L) ∨
      (∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G,
        IsComponentOf J (Subgroup.centralizer ({z} : Set G)) ∧ z ∈ J ∧
          ∃ r : ℕ, 3 ≤ r ∧ ∃ S : Sylow 2 J,
            Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) ∨
      ∃ a : G, orderOf a = 2 ∧ ∃ J : Subgroup G, IsComponentOf J (centralizer ({a} : Set G)) ∧
        IsTwoPComponent (J.subgroupOf (centralizer ({a} : Set G))) ∧
        ∃ A : Subgroup G, A ≤ centralizer (J : Set G) ∧ IsElemAbelian 2 A ∧ a ∈ A ∧
          4 ≤ Nat.card A ∧ 2 ≤ CFSG.Assembly.pRank 2 J ∧
          (∀ b ∈ A, b ≠ 1 → IsComponentOf J (centralizer ({b} : Set G))) ∧
          RefinedMaxima J A ∧
          ∀ c ∈ J, c ∈ centralizer (J : Set G) → orderOf c = 2 → c ∈ A := by
  rcases initial_component_constant_on_selected_four_group_reduction hC hpump hK hcomp hB with
    h1 | ⟨c, hc, L, hL, hcL, -, r, hr3, T, hT⟩ | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨c, hc, L, hL, hcL, r, hr3, T, hT⟩)
  · exact Or.inr (Or.inr h3)

end CFSG.LocalAnalysis.ComponentInitial
