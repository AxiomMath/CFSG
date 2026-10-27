module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairIndexTwo

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.TwoRankLowerBound.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem involution_rank_three_coverage_of_no_index_two
    (hindexTwo : ∀ K : Subgroup G, K.index ≠ 2) (hrank : 3 ≤ twoRank G) (t : G)
    (ht : orderOf t = 2) :
    ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E := by
  classical
  let S : Sylow 2 G := default
  let P := (S : Subgroup G)
  have hPrank : 3 ≤ twoRank P := by
    change 3 ≤ Open.pRank 2 (⊤ : Subgroup P)
    rw [← pRank_subgroup_eq_internal_top 2 (by decide), sylow_two_rank_eq]
    exact hrank
  obtain ⟨V, hVnormal, hV, hVcard⟩ := high_two_rank_normal_four P S.isPGroup' hPrank
  let : V.Normal := hVnormal
  obtain ⟨A, hA, hAcard⟩ := exists_elementary_eight_of_rank_three hPrank
  let C := Subgroup.centralizer (V : Set P)
  obtain ⟨_, _, hindex⟩ := normal_four_centralizer_index S.isPGroup' V hV hVcard
  change C.index ≤ 2 at hindex
  let Cimage := C.map P.subtype
  have hCimageP : Cimage ≤ P := Subgroup.map_subtype_le _
  have hrelative : Cimage.relIndex P = C.index := by
    change ((C.map P.subtype).comap P.subtype).index = C.index
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  have hconjugate : ∃ g : G, g⁻¹ * t * g ∈ Cimage := by
    by_cases hCtop : C = ⊤
    · have hCimage : Cimage = P := by
        change C.map P.subtype = P
        rw [hCtop, Subgroup.map_top, Subgroup.range_subtype]
      obtain ⟨g, _, hgt⟩ := involution_conjugate_into_sylow S (⊤ : Subgroup G) le_top
        t (by trivial) ht
      exact ⟨g, hCimage.symm ▸ hgt⟩
    · have hCindex : C.index = 2 := by
        have hpositive : 0 < C.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
        have hnotOne : C.index ≠ 1 := fun heq => hCtop (Subgroup.index_eq_one.mp heq)
        omega
      exact exists_conj_mem_of_sylow_relIndex_two hindexTwo S Cimage hCimageP
        (hrelative.trans hCindex) t ht
  obtain ⟨g, x, hxC, hx⟩ := hconjugate
  change (x : G) = g⁻¹ * t * g at hx
  have hxOrder : orderOf (x : G) = 2 := by
    rw [hx]
    simpa only [MulAut.conj_apply, inv_inv, ht] using (MulAut.conj g⁻¹).orderOf_eq t
  obtain ⟨E, _, hE, hEcard, hxE⟩ := normal_four_centralizer_involution_coverage
    S.isPGroup' V hV hVcard A hA hAcard x ((Subgroup.orderOf_coe x).symm.trans hxOrder) hxC
  obtain ⟨F, _, hF, hFcard, hxF⟩ := elementary_eight_coverage_lift P x ⟨E, hE, hEcard, hxE⟩
  exact elementary_eight_coverage_conjugate t g F hF hFcard (hx ▸ hxF)

theorem sylow_three_involutions_no_elementary_eight {M : Type u} [Group M] [Finite M]
    (T : Sylow 2 M) (hT : Nat.card {t : (T : Subgroup M) // orderOf t = 2} = 3)
    (E : Subgroup M) (hE : IsElemAbelian 2 E) (hEcard : Nat.card E = 8) : False := by
  classical
  have hEtwo : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
  obtain ⟨Q, hEQ⟩ := hEtwo.exists_le_sylow
  let φ := Q.equiv T
  let f : {e : E // e ≠ 1} → {t : (T : Subgroup M) // orderOf t = 2} := fun e =>
    ⟨φ ⟨e.1, hEQ e.1.property⟩, by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, Subgroup.coe_mk,
        Subgroup.orderOf_coe]
      exact orderOf_eq_prime (Subtype.ext (hE.2 e.1 e.1.property)) e.2⟩
  have hinjective : Function.Injective f := by
    intro a b hab
    have h := φ.injective (congrArg Subtype.val hab)
    exact Subtype.ext (Subtype.ext (congrArg (fun q : (Q : Subgroup M) => (q : M)) h))
  let : Fintype E := Fintype.ofFinite E
  have hcard : Nat.card {e : E // e ≠ 1} = 7 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hEcard]
  have hle := Nat.card_le_card_of_injective f hinjective
  omega

theorem three_involution_centralizer_forces_two_rank_two
    (hindexTwo : ∀ K : Subgroup G, K.index ≠ 2) (u : G) (hu : orderOf u = 2)
    (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hT : Nat.card {t : (T : Subgroup (Subgroup.centralizer ({u} : Set G))) //
      orderOf t = 2} = 3) :
    CFSG.Open.twoRank G = 2 := by
  classical
  let M := Subgroup.centralizer ({u} : Set G)
  let P := (T : Subgroup M)
  have hT' : Nat.card {t : P // orderOf t = 2} = 3 := hT
  have hlower : 2 ≤ twoRank G := by
    obtain ⟨⟨t, ht⟩⟩ := (Nat.card_pos_iff.mp (by omega :
      0 < Nat.card {t : P // orderOf t = 2})).1
    have : Nontrivial P := ⟨⟨t, 1, fun h => by simp [h] at ht⟩⟩
    obtain ⟨c, hc, hcCenter⟩ := exists_central_involution_of_two_group P T.isPGroup'
    have : Nontrivial {t : P // orderOf t = 2} :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨d, hd⟩ := exists_ne (⟨c, hc⟩ : {t : P // orderOf t = 2})
    have hdc : d.1 ≠ c := fun h => hd (Subtype.ext h)
    refine two_le_twoRank_of_commuting_involutions G ((d.1 : M) : G) ((c : M) : G)
      ((Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe _).trans d.2))
      ((Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe _).trans hc))
      (fun h => hdc (Subtype.ext (Subtype.ext h))) ?_
    exact congrArg (fun x : P => ((x : M) : G)) (Subgroup.mem_center_iff.mp hcCenter d.1)
  by_contra hne
  obtain ⟨E, hE, hEcard, huE⟩ :=
    involution_rank_three_coverage_of_no_index_two hindexTwo (by omega) u hu
  have hEM : E ≤ M := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (@mul_comm' E _ hE.1 ⟨x, hx⟩ ⟨u, huE⟩))
  let E' := E.subgroupOf M
  have hE' : IsElemAbelian 2 E' :=
    elementary_transport 2 E E' (Subgroup.subgroupOfEquivOfLe hEM).symm hE
  have hE'card : Nat.card E' = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv).trans hEcard
  exact sylow_three_involutions_no_elementary_eight T hT E' hE' hE'card

end CFSG.ProperTwoGeneratedCore.RankOnePair
