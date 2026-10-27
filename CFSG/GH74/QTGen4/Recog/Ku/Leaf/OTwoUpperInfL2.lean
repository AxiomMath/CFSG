module

public import CFSG.GH74.QTGen4.Recog.Ku.NInvolutionsC
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem mem_L2_of_order_three
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    {y : G} (hyX : y ∈ oTwoUpper M ⊓ Subgroup.normalizer (kuV2 T M : Set G))
    (hy3 : orderOf y = 3) : y ∈ Ψ.L2 := by
  have hyLN : y ∈ oTwoUpper M ⊓ kuN P H := by
    rw [h.oTwoUpper_inf_kuN_eq]
    exact hyX
  have hyN : y ∈ kuN P H := (Subgroup.mem_inf.mp hyLN).2
  have hstab := pi_mem_stabS_of_normalizer Ψ hyN (Subgroup.mem_inf.mp hyX).2
  have hy3' : y ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hpow : (⟨y, hyN⟩ : ↥(kuN P H)) ^ 3 = 1 := Subtype.ext (by simpa using hy3')
  have hcube : Ψ.π ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow, hpow, map_one]
  exact (Ψ.mem_pre_iff lamS).mpr ⟨hyN, mem_lamS_of_pow_three _ hstab hcube⟩

theorem oTwoUpper_inf_kuN_le_L2
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    oTwoUpper M ⊓ kuN P H ≤ Ψ.L2 := by
  obtain ⟨y, hyX, hy3⟩ := h.exists_order_three_X
  have hyLN : y ∈ oTwoUpper M ⊓ kuN P H := by
    rw [h.oTwoUpper_inf_kuN_eq]
    exact hyX
  have hinf : kuR T M ⊓ Subgroup.zpowers y = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgR, hgy⟩ := Subgroup.mem_inf.mp hg
    have h3 : orderOf g ∣ 3 := by
      have hd := orderOf_dvd_of_mem_zpowers hgy
      rwa [hy3] at hd
    have h64 : orderOf g ∣ 64 := by
      have hd := orderOf_dvd_natCard (⟨g, hgR⟩ : ↥(kuR T M))
      rw [← Subgroup.orderOf_coe, h.card_kuR] at hd
      exact hd
    have hgcd : orderOf g ∣ Nat.gcd 3 64 := Nat.dvd_gcd h3 h64
    have h1 : orderOf g = 1 := by
      have e : Nat.gcd 3 64 = 1 := by norm_num
      rw [e] at hgcd
      exact Nat.dvd_one.mp hgcd
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (kuR T M : Set G) :=
    Subgroup.zpowers_le.mpr (h.normalizer_kuR_of_X hyX)
  have hcard : Nat.card ↥(kuR T M ⊔ Subgroup.zpowers y) = 192 := by
    have e := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (kuR T M) (Subgroup.zpowers y) hnorm (disjoint_iff.mpr hinf)
    rw [h.card_kuR, Nat.card_zpowers, hy3] at e
    omega
  have hRL1 : kuR T M ≤ oTwoUpper M := inf_le_right
  have hRN : kuR T M ≤ kuN P H := (inf_le_left : kuR T M ≤ T).trans h.T_le_kuN
  have hle : kuR T M ⊔ Subgroup.zpowers y ≤ oTwoUpper M ⊓ kuN P H :=
    sup_le (le_inf hRL1 hRN) (Subgroup.zpowers_le.mpr hyLN)
  have heq : kuR T M ⊔ Subgroup.zpowers y = oTwoUpper M ⊓ kuN P H :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [h.card_oTwoUpper_inf_kuN, hcard]))
  have hRL2 : kuR T M ≤ Ψ.L2 :=
    (h.kuR_eq_pre_kleinS Ψ).le.trans (Ψ.pre_mono kleinS_le_lamS)
  have hyL2 : y ∈ Ψ.L2 := h.mem_L2_of_order_three Ψ hyX hy3
  rw [← heq]
  exact sup_le hRL2 (Subgroup.zpowers_le.mpr hyL2)

end KuHyp

theorem leafOTwoUpperInfL2
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    : LeafOTwoUpperInfL2 := by
  intro G _ _ T M H P z h Ψ
  exact KuHyp.oTwoUpper_inf_L2_eq_of_le Ψ (h.oTwoUpper_inf_kuN_le_L2 Ψ)

theorem leafCardOTwoUpperInfL2
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    : LeafCardOTwoUpperInfL2 := by
  intro G _ _ T M H P z h Ψ
  exact h.card_oTwoUpper_inf_L2_of_le Ψ (h.oTwoUpper_inf_kuN_le_L2 Ψ)


end CFSG.GH74.QTGen4.Ku
