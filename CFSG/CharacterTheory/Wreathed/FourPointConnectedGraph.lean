module

public import CFSG.CharacterTheory.Wreathed.FourPointConnectedGraphSupport
public import CFSG.CharacterTheory.Wreathed.FourPointSixtyThree

public noncomputable section

namespace CFSG.Wreathed.FourPointConnectedGraph

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.FourPointCompleteModel
  CFSG.Wreathed.FourPointOrderFour CFSG.Assembly CFSG.GroupTheory.SevenInvolutionWreathLaw

open scoped Classical

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem wreath_four_x2_z :
    Original.x2 (2 ^ 2) * Original.x (2 ^ 2) = Original.x (2 ^ 2) * Original.x2 (2 ^ 2) ∧
    Original.z (2 ^ 2) * Original.x (2 ^ 2) = Original.x (2 ^ 2) * Original.z (2 ^ 2) ∧
    Original.x2 (2 ^ 2) ≠ Original.x (2 ^ 2) ∧ Original.z (2 ^ 2) ≠ Original.x (2 ^ 2) ∧
    Original.x2 (2 ^ 2) ≠ Original.z (2 ^ 2) ∧
    Original.x2 (2 ^ 2) * Original.z (2 ^ 2) ≠ Original.z (2 ^ 2) * Original.x2 (2 ^ 2) := by
  have hx : Original.x (2 ^ 2) = element (2 ^ 2) 2 2 0 := by
    rw [Original.x_eq]
    norm_num
  have hx2 : Original.x2 (2 ^ 2) = element (2 ^ 2) 2 0 0 := by
    rw [Original.x2_eq]
    norm_num
  have hz : Original.z (2 ^ 2) = element (2 ^ 2) 0 0 1 := rfl
  rw [hx, hx2, hz]
  simp only [element_base_mul, element_swap_mul, ne_eq, element_eq_iff]
  decide

theorem four_point_connected_involution_graph_and_trivial_original_odd_core
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let C := orderFourCentralizer n S e
    n = 2 ∧ R = ⊥ ∧ Nat.card G = 6048 ∧ Nat.card N = 96 ∧ C = N ∧
      Nat.card {g : G // orderOf g = 2} = 63 ∧
      (∀ t : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet t).ncard = 6) ∧
      (involutionGraph G).Connected := by
  intro N R C
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, -, hCN, hinvR, -, -, hN96, hG6048, -, hN7, hG63⟩ :=
    FourPointSixtyThree.four_point_odd_core_centralization_and_sixty_three_involutions hnonab 2 hn
      S e alpha
  obtain ⟨-, ⟨Φ, hΦ⟩, hord⟩ :=
    FourPointPrincipalOrderScalar.four_point_actual_principal_order_scalar hnonab 2 hn S e alpha
  obtain ⟨⟨y₀, hy₀2, hy₀Φ⟩, hyall⟩ := hord Φ hΦ
  obtain ⟨-, -, hcent16, hinvcls, -, -, -⟩ := hyall y₀ hy₀2 hy₀Φ
  set x : G := wreathModelHom S e (Original.x (2 ^ 2)) with hxdef
  have hinjW := wreathModelHom_injective S e
  have hx2 : orderOf x = 2 := by
    rw [hxdef, orderOf_injective _ hinjW]
    exact (wreath_center_involution_and_quaternion_coordinates 2 le_rfl).involution_orders.1
  have hclass : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b :=
    all_involutions_conjugate_of_simple_wreathed hnonab 2 hn S e
  have hRP : CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = R :=
    (weakClosure_oddCore_eq_pPrimeCore _).symm
  have hlocal : InvolutionOddCoreLocalHypotheses x := by
    refine localHypotheses_of_quotient x (centralizerOddCoreMap 2 S e)
      ((QuotientGroup.ker_mk' (centralizerOddCore 2 S e)).trans hRP.symm) (fun y hy r hr => ?_)
      (fun y hy hyx => ?_)
    · rw [hRP] at hr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hinvR y hy r hr).symm
    · have hyconj : IsConj y₀ y := by
        rcases (hinvcls y).mp hy with h | h
        · exact absurd (congrArg (fun t : N => (t : G)) h) hyx
        · exact h
      obtain ⟨c, hc⟩ := isConj_iff.mp hyconj
      have hπ : (MulAut.conj (centralizerOddCoreMap 2 S e c)) (centralizerOddCoreMap 2 S e y₀) =
          centralizerOddCoreMap 2 S e y := by
        rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, hc]
      have hcard : Nat.card (Subgroup.centralizer
          ({centralizerOddCoreMap 2 S e y} : Set (centralizerOddCoreQuotient 2 S e))) = 16 := by
        rw [← hcent16]
        exact (Nat.card_congr (centralizerTransport _ _ _ hπ).toEquiv).symm
      exact IsPGroup.of_card (n := 4) (hcard.trans (by norm_num))
  have hedge : ∀ u v : {g : G // orderOf g = 2}, (involutionGraph G).Adj u v →
      involutionOddCore (u : G) = involutionOddCore (v : G) := fun u v huv =>
    commuting_involution_odd_cores_eq x hx2 hclass hlocal u v u.2 v.2 (coe_ne_of_adj huv)
      (commute_of_adj huv)
  have hdeg : ∀ t : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet t).ncard = 6 := by
    intro t
    apply ncard_neighborSet_eq_six
    obtain ⟨c, hc⟩ := isConj_iff.mp (hclass x t hx2 t.2)
    rw [← hc, ncard_centralizer_involutions_conj, ← card_involutions_subgroup_eq_ncard]
    exact hN7
  obtain ⟨hs2x, hwx, hs2ne, hwne, hs2w, hs2wc⟩ := wreath_four_x2_z
  have hs2o : orderOf (wreathModelHom S e (Original.x2 (2 ^ 2))) = 2 := by
    rw [orderOf_injective _ hinjW]
    exact (wreath_center_involution_and_quaternion_coordinates 2 le_rfl).involution_orders.2.1
  have hwo : orderOf (wreathModelHom S e (Original.z (2 ^ 2))) = 2 := by
    rw [orderOf_injective _ hinjW]
    exact Original.orderOf_z _
  let tx : {g : G // orderOf g = 2} := ⟨x, hx2⟩
  let ts : {g : G // orderOf g = 2} := ⟨_, hs2o⟩
  let tw : {g : G // orderOf g = 2} := ⟨_, hwo⟩
  have hadjs : (involutionGraph G).Adj tx ts := by
    refine adj_iff_ne_and_commute.mpr ⟨fun h => ?_, ?_⟩
    · have h' : wreathModelHom S e (Original.x (2 ^ 2)) =
          wreathModelHom S e (Original.x2 (2 ^ 2)) :=
        congrArg (fun t : {g : G // orderOf g = 2} => (t : G)) h
      exact hs2ne (hinjW h').symm
    · change x * wreathModelHom S e (Original.x2 (2 ^ 2)) =
        wreathModelHom S e (Original.x2 (2 ^ 2)) * x
      rw [hxdef, ← map_mul, ← map_mul, hs2x]
  have hadjw : (involutionGraph G).Adj tx tw := by
    refine adj_iff_ne_and_commute.mpr ⟨fun h => ?_, ?_⟩
    · have h' : wreathModelHom S e (Original.x (2 ^ 2)) =
          wreathModelHom S e (Original.z (2 ^ 2)) :=
        congrArg (fun t : {g : G // orderOf g = 2} => (t : G)) h
      exact hwne (hinjW h').symm
    · change x * wreathModelHom S e (Original.z (2 ^ 2)) =
        wreathModelHom S e (Original.z (2 ^ 2)) * x
      rw [hxdef, ← map_mul, ← map_mul, hwx]
  have hsw : ts ≠ tw := fun h => by
    have h' : wreathModelHom S e (Original.x2 (2 ^ 2)) =
        wreathModelHom S e (Original.z (2 ^ 2)) :=
      congrArg (fun t : {g : G // orderOf g = 2} => (t : G)) h
    exact hs2w (hinjW h')
  have hnc : (ts : G) * tw ≠ tw * ts := by
    change wreathModelHom S e (Original.x2 (2 ^ 2)) * wreathModelHom S e (Original.z (2 ^ 2)) ≠
      wreathModelHom S e (Original.z (2 ^ 2)) * wreathModelHom S e (Original.x2 (2 ^ 2))
    rw [← map_mul, ← map_mul]
    exact fun h => hs2wc (hinjW h)
  have h32 : 32 ∣ Nat.card G := by
    have h := Subgroup.card_subgroup_dvd_card (S : Subgroup G)
    rw [Nat.card_congr e.toEquiv, card_wreath] at h
    exact h
  have hconn := involutionGraph_connected_of_counts hG63 hdeg h32 tx ts tw hadjs hadjw hsw hnc
  have hreach : ∀ u v : {g : G // orderOf g = 2}, (involutionGraph G).Reachable u v →
      involutionOddCore (u : G) = involutionOddCore (v : G) := by
    intro u v huv
    rw [SimpleGraph.reachable_iff_reflTransGen] at huv
    induction huv with
    | refl => rfl
    | tail _ hadj ih => exact ih.trans (hedge _ _ hadj)
  have hconst : ∀ t : G, orderOf t = 2 → involutionOddCore t = involutionOddCore x :=
    fun t ht => hreach ⟨t, ht⟩ tx (hconn.preconnected _ _)
  have hR : R = ⊥ := by
    have := involutionOddCore_normal x hx2 hconst
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (involutionOddCore x) with hbot | htop
    · rw [← hRP]
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hbot
    · exfalso
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcop := CFSG.pPrimeCore_coprime_card (p := 2)
        (G := Subgroup.centralizer ({x} : Set G))
      have hcardO : Nat.card (involutionOddCore x) =
          Nat.card (CFSG.pPrimeCore 2 (Subgroup.centralizer ({x} : Set G))) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      rw [htop, Subgroup.card_top] at hcardO
      rw [← hcardO] at hcop
      have h2 : 2 ∣ Nat.card G := hx2 ▸ orderOf_dvd_natCard x
      have h1 := Nat.Coprime.eq_one_of_dvd hcop h2
      omega
  have hG' : Nat.card G = 6048 * Nat.card R := hG6048
  have hN' : Nat.card N = 96 * Nat.card R := hN96
  refine ⟨rfl, hR, ?_, ?_, hCN, hG63, hdeg, hconn⟩
  · rw [hG', hR, Subgroup.card_bot]
  · rw [hN', hR, Subgroup.card_bot]

end CFSG.Wreathed.FourPointConnectedGraph
