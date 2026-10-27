module

public import CFSG.GH74.QTGen4.Recog.Ku.NInvolutions
public import CFSG.GH74.QTGen4.Recog.Ku.NInvolutionsC

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem L2_inf_M1_le_oTwoUpper
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    Ψ.L2 ⊓ (M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) ≤ oTwoUpper M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set X : Subgroup (Equiv.Perm (Fin 6)) :=
    ((oTwoUpper M ⊓ kuN P H).subgroupOf (kuN P H)).map Ψ.π
  have hkX : kleinS ≤ X := by
    intro k hk
    obtain ⟨n, hn⟩ := Ψ.π_surj k (kleinS_le_alt hk)
    have hnpre : (n : G) ∈ Ψ.pre kleinS :=
      (Ψ.mem_pre_iff kleinS).mpr ⟨n.2, by show Ψ.π n ∈ kleinS; rw [hn]; exact hk⟩
    have hnR : (n : G) ∈ kuR T M := by
      rw [h.kuR_eq_pre_kleinS Ψ]
      exact hnpre
    exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨(inf_le_right : kuR T M ≤ oTwoUpper M) hnR, n.2⟩), hn⟩
  obtain ⟨y, hyX, hy3⟩ := h.exists_order_three_X
  obtain ⟨hyL, hyV⟩ := Subgroup.mem_inf.mp hyX
  have hyN : y ∈ kuN P H :=
    h.M_inf_normalizer_V2_le_kuN (Subgroup.mem_inf.mpr ⟨oTwoUpper_le M hyL, hyV⟩)
  have hstab := pi_mem_stabS_of_normalizer Ψ hyN hyV
  have hy3' : y ^ 3 = 1 := by
    rw [← hy3]
    exact pow_orderOf_eq_one y
  have hpow : (⟨y, hyN⟩ : ↥(kuN P H)) ^ 3 = 1 := Subtype.ext (by simpa using hy3')
  have hcube : Ψ.π ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow, hpow, map_one]
  have htauL : Ψ.π ⟨y, hyN⟩ ∈ lamS := mem_lamS_of_pow_three _ hstab hcube
  have htau1 : Ψ.π ⟨y, hyN⟩ ≠ 1 := by
    intro h1
    have hyE : y ∈ kuA P H := (Ψ.ker ⟨y, hyN⟩).mp h1
    have hd := orderOf_dvd_natCard (⟨y, hyE⟩ : ↥(kuA P H))
    rw [Subgroup.orderOf_mk, hy3, h.card_kuA] at hd
    norm_num at hd
  have htauord : orderOf (Ψ.π ⟨y, hyN⟩) = 3 := orderOf_eq_prime hcube htau1
  have htauX : Ψ.π ⟨y, hyN⟩ ∈ X :=
    Subgroup.mem_map.mpr ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨hyL, hyN⟩), rfl⟩
  have hlam0X : lam0 ≤ X := by
    have hZle : X ⊓ lam0 ≤ lam0 := inf_le_right
    have hkZ : kleinS ≤ X ⊓ lam0 := le_inf hkX kleinS_le_lam0
    have hτZ : Ψ.π ⟨y, hyN⟩ ∈ X ⊓ lam0 :=
      Subgroup.mem_inf.mpr ⟨htauX, Subgroup.mem_inf.mpr ⟨htauL, hstab⟩⟩
    have h4 : 4 ∣ Nat.card (X ⊓ lam0 : Subgroup (Equiv.Perm (Fin 6))) := by
      have := Subgroup.card_dvd_of_le hkZ
      rwa [card_kleinS] at this
    have h3 : 3 ∣ Nat.card (X ⊓ lam0 : Subgroup (Equiv.Perm (Fin 6))) := by
      have := orderOf_dvd_natCard (⟨_, hτZ⟩ : ↥(X ⊓ lam0 : Subgroup (Equiv.Perm (Fin 6))))
      rwa [Subgroup.orderOf_mk, htauord] at this
    have h12 : 12 ∣ Nat.card (X ⊓ lam0 : Subgroup (Equiv.Perm (Fin 6))) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
    have hpos : 0 < Nat.card (X ⊓ lam0 : Subgroup (Equiv.Perm (Fin 6))) := Nat.card_pos
    have hge : Nat.card lam0 ≤ Nat.card (X ⊓ lam0 : Subgroup (Equiv.Perm (Fin 6))) := by
      rw [card_lam0]
      exact Nat.le_of_dvd hpos h12
    have heq : X ⊓ lam0 = lam0 := Subgroup.eq_of_le_of_card_ge hZle hge
    intro σ hσ
    have hσZ : σ ∈ X ⊓ lam0 := by
      rw [heq]
      exact hσ
    exact (Subgroup.mem_inf.mp hσZ).1
  intro g hg
  obtain ⟨hgL2, hgM1⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨hgN, hgL⟩ := (Ψ.mem_pre_iff lamS).mp hgL2
  have hgstab := pi_mem_stabS_of_normalizer Ψ hgN (Subgroup.mem_inf.mp hgM1).2
  have hgmem : Ψ.π ⟨g, hgN⟩ ∈ lam0 := Subgroup.mem_inf.mpr ⟨hgL, hgstab⟩
  obtain ⟨a, haN, hapi⟩ := Subgroup.mem_map.mp (hlam0X hgmem)
  have haL : (a : G) ∈ oTwoUpper M ⊓ kuN P H := Subgroup.mem_subgroupOf.mp haN
  have hw1 : Ψ.π (a⁻¹ * ⟨g, hgN⟩) = 1 := by
    rw [map_mul, map_inv, hapi, inv_mul_cancel]
  have hwL : ((a⁻¹ * ⟨g, hgN⟩ : ↥(kuN P H)) : G) ∈ oTwoUpper M :=
    (h.kuA_le_kuR.trans (inf_le_right : kuR T M ≤ oTwoUpper M)) ((Ψ.ker _).mp hw1)
  have hgeq : g = (a : G) * ((a⁻¹ * ⟨g, hgN⟩ : ↥(kuN P H)) : G) := by
    simp
  rw [hgeq]
  exact Subgroup.mul_mem _ (Subgroup.mem_inf.mp haL).1 hwL

end KuHyp

theorem leafKuNEqL2DoubleCoset
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    : LeafKuNEqL2DoubleCoset := by
  intro G _ _ T M H P z h Ψ t ht htL g hg
  exact h.kuN_eq_L2_doubleCoset_of_inf_le Ψ (h.L2_inf_M1_le_oTwoUpper Ψ) ht htL g hg


end CFSG.GH74.QTGen4.Ku
