module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQGF2HigherCenterWidthThree
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2ExtraspecialWidthFour

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.SectionRank.Ccomm (ThompsonCritical)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative

namespace SteinbergBX.HigherCenterWidthFour

theorem two_subgroups_eleven_generated_of_width_three {H : Type*} [Group H] [Finite H]
    {D' : Subgroup H} [D'.Normal] [((center D').map D'.subtype).Normal]
    (hDP : D' ≤ CFSG.pCore 2 H) (hYc : IsCyclic ((center D').map D'.subtype))
    (hrel : D'.relIndex (CFSG.pCore 2 H) ≤ 2) [IsElementaryAbelian 2 (D' ⧸ center D')]
    (hfin : Module.finrank (ZMod 2) (Additive (D' ⧸ center D')) = 6)
    {b : LinearMap.BilinForm (ZMod 2) (Additive (D' ⧸ center D'))} (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (ι : H ⧸ CFSG.pCore 2 H →* bilinIsometryGroup b)
    (hι : Function.Injective ι)
    (hιc : ∀ (m : H) (x y : D'), (y : H) = m * x * m⁻¹ →
      (((ι (m : H ⧸ CFSG.pCore 2 H) : bilinIsometryGroup b) :
        LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D' ⧸ center D'))) :
          Module.End (ZMod 2) (Additive (D' ⧸ center D')))
        (Additive.ofMul (x : D' ⧸ center D')) = Additive.ofMul (y : D' ⧸ center D'))
    (P : Subgroup H) (hP : IsPGroup 2 P) :
    ∃ S : Finset P, S.card ≤ 11 ∧ closure (S : Set P) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : Nat.card (Additive (D' ⧸ center D')) = 64 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (D' ⧸ center D'))
    rw [Nat.card_zmod, hfin] at h1
    exact h1
  let π : D' →* Multiplicative (Additive (D' ⧸ center D')) :=
    { toFun := fun x => Multiplicative.ofAdd (Additive.ofMul (x : D' ⧸ center D'))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hπ : Function.Surjective π := fun v => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Multiplicative.toAdd v).toMul
    refine ⟨x, ?_⟩
    change Multiplicative.ofAdd (Additive.ofMul (x : D' ⧸ center D')) = v
    rw [hx]
    rfl
  have hπker : π.ker = ((center D').map D'.subtype).subgroupOf D' := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change Multiplicative.ofAdd (Additive.ofMul (x : D' ⧸ center D')) =
      Multiplicative.ofAdd (Additive.ofMul 1) ↔ _
    refine ((Multiplicative.ofAdd.injective.comp Additive.ofMul.injective).eq_iff).trans ?_
    refine (QuotientGroup.eq_one_iff _).trans ?_
    constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨c, hc, hceq⟩
      obtain rfl : c = x := Subtype.ext hceq
      exact hc
  let ρ : H →* bilinIsometryGroup b := ι.comp (QuotientGroup.mk' (CFSG.pCore 2 H))
  have hρ : ∀ (h : H) (d d' : D'), (d' : H) = h * d * h⁻¹ →
      Multiplicative.toAdd (π d') = ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
        (Additive (D' ⧸ center D'))) : Additive (D' ⧸ center D') →ₗ[ZMod 2]
          Additive (D' ⧸ center D')) (Multiplicative.toAdd (π d)) :=
    fun h d d' hd => (hιc h d d' hd).symm
  have hρker : ρ.ker = CFSG.pCore 2 H := by
    ext h
    rw [MonoidHom.mem_ker]
    change ι (h : H ⧸ CFSG.pCore 2 H) = 1 ↔ _
    rw [← map_one ι, hι.eq_iff, QuotientGroup.eq_one_iff]
  obtain ⟨-, -, -, -, -, -, -, -, h11, -, -⟩ :=
    cyclic_layer_symplectic_six_extension_eleven_generated (map_subtype_le _) hDP
      CFSG.pCore_isPGroup hYc hrel hV π hπ hπker hb hnd ρ hρ hρker P hP _ rfl _ rfl _ _ rfl rfl
  exact h11

end SteinbergBX.HigherCenterWidthFour

open SteinbergBX.HigherCenterWidthFour

theorem gf2_higher_center_critical_width_at_least_four_at_rank_four
    {G : Type*} [Group G]
    [Finite G] (hchar : IsCharacteristicPType G 2) (he : 4 ≤ CFSG.twoLocalOddRank G)
    {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M))
    (hB : GLAIsBmax 3 B) (hBM : B ≤ M) {Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {D : Subgroup Q} (hD : ThompsonCritical D)
    (hY8 : 8 ≤ Nat.card (center D)) :
    ∃ _ : IsElementaryAbelian 2 (D ⧸ center D), ∃ u : ℕ, 4 ≤ u ∧
      Module.finrank (ZMod 2) (Additive (D ⧸ center D)) = 2 * u ∧
      256 ≤ Nat.card (D ⧸ center D) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEA, u, hu3, hfin, -⟩ :=
    gf2_higher_center_critical_width_at_least_three_at_rank_four hchar he hM hsym hB hBM hQ hD
      hY8
  have hDZcard : Nat.card (D ⧸ center D) = 2 ^ (2 * u) := by
    rw [SteinbergBK.natCard_eq_two_pow_finrank, hfin]
  have hu4 : 4 ≤ u := by
    by_contra hu4
    have hu : u = 3 := by omega
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
    obtain ⟨-, hidx, -, u', -, hru', -, hDZcard', hMND, -, -, -, -, -, -, -⟩ :=
      gf2_higher_center_residual_presentations_and_fusion hchar he hM hsym hB hBM hQ hzQ hz rfl
        hD rfl hk hYk hTY hT4
    have huu' : u' = u := by
      have h1 := Nat.pow_right_injective (le_refl 2) (hDZcard'.symm.trans hDZcard)
      omega
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
    have hfin6 : Module.finrank (ZMod 2) (Additive (D' ⧸ center D')) = 6 := by
      rw [hfin', hu]
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 M))
    have hSM : IsSylowOf 2 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
    have hgen : ∀ P : Subgroup G, IsPGroup 2 P →
        ∃ T : Finset G, T.card ≤ 11 ∧ closure (T : Set G) = P :=
      SteinbergBK.two_subgroups_generated_of_sylow_le (map_subtype_le _) (hSyl _ hSM).1
        (two_subgroups_eleven_generated_of_width_three hDP hYc hrel hfin6 hbalt hbnd ι hι hιc)
    obtain ⟨-, -, h4⟩ :=
      eleven_generator_two_subgroups_force_large_odd_local_prime_three hchar he hgen
    omega
  refine ⟨hEA, u, hu4, hfin, ?_⟩
  rw [hDZcard]
  calc 256 = 2 ^ 8 := by norm_num
    _ ≤ 2 ^ (2 * u) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LocalAnalysis.GorensteinLyons
