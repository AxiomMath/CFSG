module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQGF2FusedCoreIntersection
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCCyclicLayerSevenGenerated
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2HigherCenterResidual

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.SectionRank.Ccomm (ThompsonCritical)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open CFSG.LargeEvenClassification.Helpers (pGeneratorRank pGeneratorRank_le_generators)
open scoped IsMulCommutative commutatorElement

namespace SteinbergBQ.HigherCenter

theorem seven_generated_of_eq {H : Type*} [Group H] [Finite H] {Y D Q : Subgroup H} [Y.Normal]
    [D.Normal] [Q.Normal] (hYD : Y ≤ D) (hDQ : D ≤ Q) (hQ : IsPGroup 2 Q) (hY : IsCyclic Y)
    (hQD : D.relIndex Q ≤ 2) {K : Subgroup D} [K.Normal] (hK : Y.subgroupOf D = K)
    [IsElementaryAbelian 2 (D ⧸ K)] (hV : Nat.card (D ⧸ K) = 16)
    (b : LinearMap.BilinForm (ZMod 2) (Additive (D ⧸ K))) (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hbH : ∀ (h : H) (x y : D),
      b (Additive.ofMul (MulAut.conjNormal h x : D ⧸ K))
        (Additive.ofMul (MulAut.conjNormal h y : D ⧸ K)) =
      b (Additive.ofMul (x : D ⧸ K)) (Additive.ofMul (y : D ⧸ K)))
    (hker : ∀ h : H, (∀ x : D, ((MulAut.conjNormal h x : D) : D ⧸ K) = (x : D ⧸ K)) ↔ h ∈ Q)
    (P : Subgroup H) (hP : IsPGroup 2 P) :
    ∃ S : Finset P, S.card ≤ 7 ∧ closure (S : Set P) = ⊤ := by
  subst hK
  obtain ⟨-, -, -, -, -, -, h7, -⟩ :=
    cyclic_layer_symplectic_four_extension_seven_generated hYD hDQ hQ hY hQD hV b hb hnd hbH hker
      P hP
  exact h7

end SteinbergBQ.HigherCenter

theorem gf2_higher_center_critical_width_at_least_three_at_rank_four
    {G : Type*} [Group G]
    [Finite G] (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G)
    {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M))
    (hB : GLAIsBmax 3 B) (hBM : B ≤ M) {Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {D : Subgroup Q} (hD : ThompsonCritical D)
    (hY8 : 8 ≤ Nat.card (center D)) :
    ∃ _ : IsElementaryAbelian 2 (D ⧸ center D), ∃ u : ℕ, 3 ≤ u ∧
      Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 2 * u ∧
      64 ≤ Nat.card (D ⧸ center D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQM : Q ≤ M := hQ ▸ map_subtype_le _
  have hQ2 : IsPGroup 2 Q := by
    rw [hQ]
    exact IsPGroup.map CFSG.pCore_isPGroup _
  obtain ⟨⟨z, hzQ, hz, -, -, -, -, hSyl⟩, -⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ rfl
  obtain ⟨-, -, hYcyc, -, -, -, -, -, -, -⟩ :=
    (gf2_critical_center_and_exponent_four_reduction hchar (by omega) hM hsym hB hBM hQ hzQ hz
      rfl).2 D hD _ rfl _ rfl
  obtain ⟨k, hYk⟩ := IsPGroup.iff_card.1 (hQ2.to_subgroup ((center D).map D.subtype))
  have hYcard : Nat.card ((center D).map D.subtype) = Nat.card (center D) :=
    Nat.card_congr ((center D).equivMapOfInjective D.subtype D.subtype_injective).symm.toEquiv
  have hk : 3 ≤ k := by
    by_contra hk
    have h1 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨y₀, hy₀⟩ := hYcyc.exists_generator
  have hy₀o : orderOf (y₀ : Q) = 2 ^ k := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy₀, hYk]
  have hdvd : 2 ^ (k - 2) ∣ orderOf (y₀ : Q) := hy₀o ▸ pow_dvd_pow 2 (by omega)
  have hTY : zpowers ((y₀ : Q) ^ 2 ^ (k - 2)) ≤ (center D).map D.subtype :=
    zpowers_le.2 (pow_mem y₀.2 _)
  have hT4 : Nat.card (zpowers ((y₀ : Q) ^ 2 ^ (k - 2))) = 4 := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd (by positivity) hdvd, hy₀o,
      Nat.pow_div (by omega) (by norm_num), show k - (k - 2) = 2 by omega]
  obtain ⟨-, hidx, -, u, hu2, -, hEA, hDZcard, hMND, -, -, -, -, -, -, -⟩ :=
    gf2_higher_center_residual_presentations_and_fusion hchar he hM hsym hB hBM hQ hzQ hz rfl hD
      rfl hk hYk hTY hT4
  have hfin : Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 2 * u := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (D ⧸ center D))
    rw [Nat.card_zmod] at h1
    have h2 : 2 ^ Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 2 ^ (2 * u) :=
      h1.symm.trans hDZcard
    exact Nat.pow_right_injective (le_refl 2) h2
  have hu3 : 3 ≤ u := by
    by_contra hu3
    have hu : u = 2 := by omega
    set D' : Subgroup M := (D.map Q.subtype).subgroupOf M with hD'
    obtain ⟨hEA', b, -, -, hbalt, hbnd, hfin', ι, hι, hιc⟩ :=
      SteinbergBQ.HigherCenter.critical_form_data hchar he hM hsym hB hBM hQ hzQ hz hD hDZcard
        hD'
    have hYcyc' : IsCyclic (center D') :=
      ((gf2_critical_quotient_and_width_at_rank_four hchar he hM hsym hB hBM hQ rfl).2 D hD D'
        hD').2.1
    have hDM : D.map Q.subtype ≤ M := (map_subtype_le D).trans hQM
    have hD'n : D'.Normal := (normal_subgroupOf_iff_le_normalizer hDM).2 hMND
    have hYn : ((center D').map D'.subtype).Normal := by
      rw [← normalizer_eq_top_iff, eq_top_iff]
      calc (⊤ : Subgroup M) = normalizer (D' : Set M) := (normalizer_eq_top D').symm
        _ ≤ _ := SteinbergBK.normalizer_le_normalizer_map_of_characteristic inferInstance
    have hDP : D' ≤ CFSG.pCore 2 M := (SteinbergBK.critical_subgroup_transport_to_core hQ hD).1
    have hYc : IsCyclic ((center D').map D'.subtype) :=
      isCyclic_of_surjective ((center D').equivMapOfInjective D'.subtype
        D'.subtype_injective).toMonoidHom (MulEquiv.surjective _)
    have hPQ : CFSG.pCore 2 M = Q.subgroupOf M := by
      rw [hQ]
      exact (comap_map_eq_self_of_injective M.subtype_injective _).symm
    have hrel : D'.relIndex (CFSG.pCore 2 M) ≤ 2 := by
      rw [hPQ, hD', relIndex_subgroupOf hQM, relIndex,
        show (D.map Q.subtype).subgroupOf Q = D from
          comap_map_eq_self_of_injective Q.subtype_injective D]
      exact hidx
    have hK : ((center D').map D'.subtype).subgroupOf D' = center D' :=
      comap_map_eq_self_of_injective D'.subtype_injective _
    have hV : Nat.card (D' ⧸ center D') = 16 := by
      have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (D' ⧸ center D'))
      rw [Nat.card_zmod, hfin', hu] at h1
      exact h1
    have hbH : ∀ (h : M) (x y : D'),
        b (Additive.ofMul (MulAut.conjNormal h x : D' ⧸ center D'))
          (Additive.ofMul (MulAut.conjNormal h y : D' ⧸ center D')) =
        b (Additive.ofMul (x : D' ⧸ center D')) (Additive.ofMul (y : D' ⧸ center D')) := by
      intro h x y
      rw [← hιc h x _ (MulAut.conjNormal_apply h x), ← hιc h y _ (MulAut.conjNormal_apply h y)]
      exact (ι (h : M ⧸ CFSG.pCore 2 M)).2 _ _
    have hker : ∀ h : M, (∀ x : D', ((MulAut.conjNormal h x : D') : D' ⧸ center D') =
        (x : D' ⧸ center D')) ↔ h ∈ CFSG.pCore 2 M := by
      intro h
      constructor
      · intro htriv
        have h1 : ι (h : M ⧸ CFSG.pCore 2 M) = 1 := by
          apply Subtype.ext
          apply Units.ext
          apply LinearMap.ext
          intro v
          obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
          have hv : v = Additive.ofMul (x : D' ⧸ center D') := by
            rw [hx]
            rfl
          rw [hv, hιc h x _ (MulAut.conjNormal_apply h x), htriv x]
          rfl
        exact (QuotientGroup.eq_one_iff h).1 (hι (h1.trans (map_one ι).symm))
      · intro hh x
        have h1 : (h : M ⧸ CFSG.pCore 2 M) = 1 := (QuotientGroup.eq_one_iff h).2 hh
        have h2 := hιc h x _ (MulAut.conjNormal_apply h x)
        rw [h1, map_one] at h2
        exact (Additive.ofMul.injective h2).symm
    have h7 := SteinbergBQ.HigherCenter.seven_generated_of_eq (map_subtype_le _) hDP
      CFSG.pCore_isPGroup hYc hrel hK hV b hbalt hbnd hbH hker
    obtain ⟨Q₀, hQ₀2, hQ₀d⟩ := SteinbergBK.exists_two_subgroup_eight_le_pGeneratorRank hchar he
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 M))
    have hSM : IsSylowOf 2 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
    obtain ⟨g, hg⟩ := SteinbergBK.exists_conj_le_of_isSylowOf_top (hSyl _ hSM).1 hQ₀2
    have hX₀M : Q₀.map (MulAut.conj g).toMonoidHom ≤ M := hg.trans (map_subtype_le _)
    let eX : ↥((Q₀.map (MulAut.conj g).toMonoidHom).subgroupOf M) ≃* Q₀ :=
      (subgroupOfEquivOfLe hX₀M).trans
        (Q₀.equivMapOfInjective _ (MulAut.conj g).injective).symm
    have hX2 : IsPGroup 2 ((Q₀.map (MulAut.conj g).toMonoidHom).subgroupOf M) :=
      hQ₀2.of_equiv eX.symm
    obtain ⟨T, hT, hTcl⟩ := h7 _ hX2
    have h1 := pGeneratorRank_le_generators Nat.prime_two hX2 T hTcl
    rw [SymplecticSixLayer.pGeneratorRank_congr eX] at h1
    omega
  refine ⟨hEA, u, hu3, hfin, ?_⟩
  rw [hDZcard]
  calc 64 = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ (2 * u) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.GorensteinLyons
