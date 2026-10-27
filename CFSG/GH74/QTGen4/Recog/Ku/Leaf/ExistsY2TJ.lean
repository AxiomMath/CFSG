module

public import CFSG.GH74.QTGen4.Recog.Ku.Leaf.InvolInvert

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem not_inverts_of_mem_oTwoUpper_inf_kuN
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) {y : G}
    (hy : y ∈ oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (hy3 : orderOf y = 3)
    {g : G} (hg : g ∈ oTwoUpper M ⊓ kuN P H) (hgy : g * y * g⁻¹ = y⁻¹) : False := by
  set X : Subgroup G := oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G) with hX
  have hgX : g ∈ X := by
    rw [hX, ← h.oTwoUpper_inf_kuN_eq]; exact hg
  have hRX : kuR T M ≤ X := fun r hr => ⟨KuHyp.kuR_le hr, h.kuR_le_normalizer_kuV2 hr⟩
  have hRn : ((kuR T M).subgroupOf X).Normal :=
    ⟨fun n hn x => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h1 := (Subgroup.mem_normalizer_iff.mp (h.normalizer_kuR_of_X x.2) (n : G)).mp hn
      simpa using h1⟩
  have hidx : ((kuR T M).subgroupOf X).index = 3 := by
    have hX192 : Nat.card ↥X = 192 := h.card_L_inf_normalizer_kuV2
    have h1 := ((kuR T M).subgroupOf X).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv, h.card_kuR, hX192] at h1
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hRn
  have hQ : Nat.card (↥X ⧸ (kuR T M).subgroupOf X) = 3 := by
    rw [← Subgroup.index_eq_card, hidx]
  haveI := isCyclic_of_prime_card hQ
  have hcomm : ∀ a b : ↥X ⧸ (kuR T M).subgroupOf X, a * b = b * a := fun a b => by
    letI : CommGroup (↥X ⧸ (kuR T M).subgroupOf X) := IsCyclic.commGroup
    exact mul_comm a b
  let yq : ↥X ⧸ (kuR T M).subgroupOf X := QuotientGroup.mk ⟨y, hy⟩
  let gq : ↥X ⧸ (kuR T M).subgroupOf X := QuotientGroup.mk ⟨g, hgX⟩
  have h1 : gq * yq * gq⁻¹ = yq⁻¹ := by
    have h' : (⟨g, hgX⟩ : ↥X) * ⟨y, hy⟩ * ⟨g, hgX⟩⁻¹ = ⟨y, hy⟩⁻¹ := Subtype.ext hgy
    have := congrArg (QuotientGroup.mk (s := (kuR T M).subgroupOf X)) h'
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at this
    exact this
  have h2 : yq = yq⁻¹ := by
    rw [← h1, hcomm gq yq, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : yq ^ 3 = 1 := by
    have h4 : (⟨y, hy⟩ : ↥X) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hy3]
      exact pow_orderOf_eq_one y
    show (QuotientGroup.mk (⟨y, hy⟩ : ↥X) : ↥X ⧸ (kuR T M).subgroupOf X) ^ 3 = 1
    rw [← QuotientGroup.mk_pow, h4, QuotientGroup.mk_one]
  have h5 : yq = 1 := by
    have h6 : yq * yq = 1 := by
      calc yq * yq = yq * yq⁻¹ := by rw [← h2]
        _ = 1 := mul_inv_cancel yq
    calc yq = yq ^ 3 * (yq * yq)⁻¹ := by group
      _ = 1 := by rw [h3, h6]; group
  have h7 : (⟨y, hy⟩ : ↥X) ∈ (kuR T M).subgroupOf X := (QuotientGroup.eq_one_iff _).mp h5
  have hyR : y ∈ kuR T M := Subgroup.mem_subgroupOf.mp h7
  have hd := orderOf_dvd_natCard (⟨y, hyR⟩ : ↥(kuR T M))
  rw [h.card_kuR, ← Subgroup.orderOf_coe] at hd
  have hd' : orderOf y ∣ 64 := hd
  rw [hy3] at hd'
  norm_num at hd'

end KuHyp

theorem leafExistsY2TJ
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafHInfCentralizerKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    : LeafExistsY2TJ := by
  intro G _ _ T M H P z h Ψ
  obtain ⟨y, hyL, hy3⟩ := h.exists_y2_mem_L2 Ψ
  obtain ⟨t, ht, htt, hty⟩ := h.exists_t_inverting Ψ hyL hy3
  obtain ⟨j, hj, hjj, hjy⟩ := h.exists_j_inverting Ψ hyL hy3
  obtain ⟨t₁, ht₁, ht₁t₁, ht₁y⟩ := h.exists_t₁_inverting (Subgroup.mem_inf.mp hyL).1 hy3
  have hyN : y ∈ Subgroup.normalizer (kuV2 T M : Set G) := by
    have h1 : y ∈ oTwoUpper M ⊓ kuN P H :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hyL).1,
        Ψ.pre_le_N lamS (Subgroup.mem_inf.mp hyL).2⟩
    rw [h.oTwoUpper_inf_kuN_eq] at h1
    exact (Subgroup.mem_inf.mp h1).2
  have hno := fun {g : G} (hg : g ∈ oTwoUpper M ⊓ kuN P H) (hgy : g * y * g⁻¹ = y⁻¹) =>
    h.not_inverts_of_mem_oTwoUpper_inf_kuN
      (Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hyL).1, hyN⟩) hy3 hg hgy
  refine ⟨y, t, j, t₁, hyL, hy3, ht, ?_, htt, hty, hj, ?_, hjj, hjy,
    h.cube_of_inverting Ψ hy3 hyL ht hty hj hjy, ht₁, ?_, ht₁t₁, ht₁y⟩
  ·
    exact fun hL => hno (Subgroup.mem_inf.mpr ⟨hL, h.M_inf_normalizer_V2_le_kuN ht⟩) hty
  ·
    exact fun hL => hno (Subgroup.mem_inf.mpr ⟨hL, Ψ.pre_le_N lamS hj⟩) hjy
  ·
    exact fun hN => hno (Subgroup.mem_inf.mpr ⟨ht₁, hN⟩) ht₁y


end CFSG.GH74.QTGen4.Ku
