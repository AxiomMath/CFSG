module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseFuseB
public import CFSG.GH74.QTGen4.Recog.Ku.CloseOddG
public import CFSG.GH74.QTGen4.Recog.Ku.Parabolics
public import CFSG.GH74.QTGen4.Recog.Ku.CloseFinal

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem kuClose_adjust {y t₀ j : G} {n k : ℤ} (hy : y ^ (n - 2 * k) = 1)
    (ht₀ : t₀ * t₀ = 1) (ht₀y : t₀ * y * t₀⁻¹ = y⁻¹)
    (hj : j * j = 1) (hjy : j * y * j⁻¹ = y⁻¹) (hn : (t₀ * j) ^ 2 = y ^ n) :
    (t₀ * y ^ k) * (t₀ * y ^ k) = 1 ∧ (t₀ * y ^ k) * y * (t₀ * y ^ k)⁻¹ = y⁻¹ ∧
      ((t₀ * y ^ k) * j) ^ 2 = 1 := by
  have hti : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀
  have hji : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj
  have hts : ∀ m : ℤ, t₀ * y ^ m * t₀ = (y ^ m)⁻¹ := fun m => by
    have h1 : t₀ * y ^ m * t₀⁻¹ = (y ^ m)⁻¹ := by
      rw [← conj_zpow, ht₀y, inv_zpow]
    rwa [hti] at h1
  have hjs : ∀ m : ℤ, j * y ^ m * j = (y ^ m)⁻¹ := fun m => by
    have h1 : j * y ^ m * j⁻¹ = (y ^ m)⁻¹ := by
      rw [← conj_zpow, hjy, inv_zpow]
    rwa [hji] at h1
  refine ⟨?_, ?_, ?_⟩
  · calc t₀ * y ^ k * (t₀ * y ^ k) = (t₀ * y ^ k * t₀) * y ^ k := by group
      _ = 1 := by rw [hts k, inv_mul_cancel]
  · calc t₀ * y ^ k * y * (t₀ * y ^ k)⁻¹ = t₀ * y * t₀⁻¹ := by group
      _ = y⁻¹ := ht₀y
  · have hc : Commute (t₀ * j) y := kuClose_mul_comm_of_inv ht₀y hjy
    have hc' : Commute (t₀ * j) (y ^ k)⁻¹ := (hc.zpow_right k).inv_right
    have e : t₀ * y ^ k * j = (t₀ * j) * (y ^ k)⁻¹ := by
      calc t₀ * y ^ k * j = t₀ * (j * j) * y ^ k * j := by rw [hj, mul_one]
        _ = t₀ * j * (j * y ^ k * j) := by group
        _ = (t₀ * j) * (y ^ k)⁻¹ := by rw [hjs k]
    rw [e, hc'.mul_pow, hn]
    calc y ^ n * ((y ^ k)⁻¹) ^ 2 = y ^ (n - 2 * k) := by group
      _ = 1 := hy

theorem KuA6Model.frame_product_bound_map [Finite G] {E W V2 N : Subgroup G} {z : G}
    (Ψ : KuA6Model E W V2 N z) (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) (φ : MulAut G)
    {x w δ₁ δ₂ : G} (hxH : φ x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3)
    (hw : orderOf w = 3) (hwx : w * x = x * w) (hwX : w ∉ Subgroup.zpowers x)
    (hδ₁ : δ₁ * δ₁ = 1) (hδ₁x : δ₁ * x * δ₁⁻¹ = x⁻¹)
    (hδ₂ : δ₂ * δ₂ = 1) (hδ₂x : δ₂ * x * δ₂⁻¹ = x⁻¹) :
    (δ₁ * δ₂) ^ 2 ∈ Subgroup.zpowers x ∨ (δ₁ * δ₂) ^ 3 = 1 := by
  have hinj : Function.Injective φ := φ.injective
  have hmem : ∀ u : G, φ u ∈ Subgroup.zpowers (φ x) ↔ u ∈ Subgroup.zpowers x := by
    intro u
    constructor
    · intro hu
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, hinj (by rw [map_zpow]; exact hk)⟩
    · intro hu
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← map_zpow, hk]⟩
  have key := Ψ.frame_product_bound hHN (x := φ x) (w := φ w) (δ₁ := φ δ₁) (δ₂ := φ δ₂) hxH
    ((MulEquiv.orderOf_eq φ x).trans hx) ((MulEquiv.orderOf_eq φ w).trans hw)
    (by rw [← map_mul, ← map_mul, hwx]) (fun hm => hwX ((hmem w).mp hm))
    (by rw [← map_mul, hδ₁, map_one])
    (by simpa only [map_mul, map_inv] using congrArg φ hδ₁x)
    (by rw [← map_mul, hδ₂, map_one])
    (by simpa only [map_mul, map_inv] using congrArg φ hδ₂x)
  rcases key with h2 | h3
  · left
    rw [← map_mul, ← map_pow, hmem] at h2
    exact h2
  · right
    rw [← map_mul, ← map_pow] at h3
    exact hinj (h3.trans (map_one φ).symm)

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem notMem_L2_of_M1 [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafKuNEqL2DoubleCoset]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    {t : G} (htMN : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (htoT : t ∉ oTwoUpper M) :
    t ∉ Ψ.L2 := by
  intro htL
  have hle : kuN P H ≤ Ψ.L2 := by
    intro g hg
    rcases h.kuN_eq_L2_doubleCoset Ψ htMN htoT g hg with hL | ⟨a, ha, b, hb, hab⟩
    · exact hL
    · rw [hab]
      exact Ψ.L2.mul_mem (Ψ.L2.mul_mem ha htL) hb
  have h1 : Ψ.L2.relIndex (kuN P H) = 1 := Subgroup.relIndex_eq_one.mpr hle
  have h6 := h.relIndex_L2 Ψ
  rw [h1] at h6
  norm_num at h6

theorem closeHolds_frame_bound
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafHInfCentralizerKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    [KuLeaf LeafExistsIsParabolicL1] [KuLeaf LeafKuNEqL2DoubleCoset]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) {y t j t₀ : G}
    (hyL : y ∈ oTwoUpper M ⊓ Ψ.L2) (hy3 : orderOf y = 3)
    (htMN : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (htoT : t ∉ oTwoUpper M)
    (hty : t * y * t⁻¹ = y⁻¹) (hjL2 : j ∈ Ψ.L2) (hjj : j * j = 1) (hjy : j * y * j⁻¹ = y⁻¹)
    (htj : (t * j) ^ 3 = 1) (ht₀t₀ : t₀ * t₀ = 1) (ht₀y : t₀ * y * t₀⁻¹ = y⁻¹) :
    (t₀ * j) ^ 2 ∈ Subgroup.zpowers y ∨ (t₀ * j) ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hyL₁ : y ∈ oTwoUpper M := (Subgroup.mem_inf.mp hyL).1
  have hyL₂ : y ∈ Ψ.L2 := (Subgroup.mem_inf.mp hyL).2
  have hfpf := h.fpf_pCore_of_order_three hyL₁ hy3
  obtain ⟨t', ht'M, ht'2, ht'1, ht'y⟩ :=
    h.exists_invol_commute (oTwoUpper_le M hyL₁) hy3 hfpf
  obtain ⟨g, hg⟩ := h.invol_M_conj_z Ψ ht'M ht'2 ht'1
  have hxH : (MulAut.conj g⁻¹) y ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    have h1 : g * z * g⁻¹ * y = y * (g * z * g⁻¹) := by rw [hg]; exact ht'y
    calc g⁻¹ * y * g⁻¹⁻¹ * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹ * y) * g := by rw [h1]
      _ = z * (g⁻¹ * y * g⁻¹⁻¹) := by group
  have hHN : Subgroup.centralizer ({z} : Set G) ≤ kuN P H := by
    rw [← h.hCz]
    exact h.H_le_kuN
  have hwY : t * j ∉ Subgroup.zpowers y := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply h.notMem_L2_of_M1 Ψ htMN htoT
    have htk : t = y ^ k * j := by
      calc t = t * j * j := by rw [mul_assoc, hjj, mul_one]
        _ = y ^ k * j := by rw [← hk]
    rw [htk]
    exact Ψ.L2.mul_mem (Ψ.L2.zpow_mem hyL₂ k) hjL2
  have hw1 : t * j ≠ 1 := by
    intro h1
    apply hwY
    rw [h1]
    exact Subgroup.one_mem _
  have hw3 : orderOf (t * j) = 3 := orderOf_eq_prime htj hw1
  exact Ψ.frame_product_bound_map hHN (MulAut.conj g⁻¹) hxH hy3 hw3
    (kuClose_mul_comm_of_inv hty hjy) hwY ht₀t₀ ht₀y hjj hjy

end KuHyp

theorem leafKuCloseHolds
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafHInfCentralizerKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    [KuLeaf LeafExistsIsParabolicL1] [KuLeaf LeafKuNEqL2DoubleCoset] [KuLeaf LeafExistsY2TJ]
    : LeafKuCloseHolds := by
  intro G _ _ T M H P z h Ψ
  obtain ⟨y, t, j, t₀, hyL, hy3, htMN, htoT, htt, hty, hjL2, hjoT, hjj, hjy, htj, ht₀L, ht₀N,
    ht₀t₀, ht₀y⟩ := h.exists_y₂_t_j Ψ
  have hyL₁ : y ∈ oTwoUpper M := (Subgroup.mem_inf.mp hyL).1
  have hyN : y ∈ kuN P H := Ψ.pre_le_N lamS (Subgroup.mem_inf.mp hyL).2
  rcases h.closeHolds_frame_bound Ψ hyL hy3 htMN htoT hty hjL2 hjj hjy htj ht₀t₀ ht₀y with
    hsq | hcube
  ·
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hsq
    have hy31 : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy3] at this
    have hy' : y ^ (n - 2 * (2 * n)) = 1 := by
      have e : n - 2 * (2 * n) = 3 * (-n) := by ring
      rw [e, zpow_mul]
      simp [hy31]
    obtain ⟨hs1, hs2, hs3⟩ := kuClose_adjust hy' ht₀t₀ ht₀y hjj hjy hn.symm
    refine ⟨y, t, j, t₀ * y ^ (2 * n), hyL, hy3, htMN, htoT, htt, hty, hjL2, hjoT, hjj, hjy, htj,
      ?_, ?_, hs1, hs2, ?_⟩
    · exact mul_mem ht₀L ((oTwoUpper M).zpow_mem hyL₁ _)
    · intro hmem
      apply ht₀N
      have := (kuN P H).mul_mem hmem ((kuN P H).inv_mem ((kuN P H).zpow_mem hyN (2 * n)))
      rwa [mul_inv_cancel_right] at this
    · exact (orderOf_le_of_pow_eq_one (by norm_num) hs3).trans (by norm_num)
  · exact ⟨y, t, j, t₀, hyL, hy3, htMN, htoT, htt, hty, hjL2, hjoT, hjj, hjy, htj, ht₀L, ht₀N,
      ht₀t₀, ht₀y, orderOf_le_of_pow_eq_one (by norm_num) hcube⟩

end CFSG.GH74.QTGen4.Ku
