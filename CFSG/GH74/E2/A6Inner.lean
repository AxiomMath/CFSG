module

public import CFSG.GH74.E2.LocalLeaves
public import CFSG.GH74.E2.NonCentralProd
public import CFSG.GH74.E2.D8Cert
public import CFSG.GH74.E2.A6Sylow
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS CFSG.GH74.Generic

@[expose] def NoLocalA6Outer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Hyp G → ∀ (t : G) (K : Subgroup G) (c : G),
    LocalData t K c → ShapeA6 ↥K →
    (¬ ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) → False

theorem two_le_pRank_of_sd16
    {H : Type} [Group H] [Finite H] (P : Subgroup H)
    (e : ↥P ≃* CFSG.Open.SemidihedralGroup 4) : 2 ≤ CFSG.pRank 2 H := by
  let eM : ↥P ≃* SD16M := e.trans (CFSG.Semidihedral.presentationEquivModel 4 (by norm_num))
  obtain ⟨x, y, hx2, hy2, hx1, hy1, hxy, hne⟩ := sd16_two_involutions
  have hx : orderOf (eM.symm x : H) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hy : orderOf (eM.symm y : H) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  have hcomm : (eM.symm x : H) * (eM.symm y : H) = (eM.symm y : H) * (eM.symm x : H) := by
    have : eM.symm x * eM.symm y = eM.symm y * eM.symm x := by
      rw [← map_mul, ← map_mul, hxy]
    exact congrArg Subtype.val this
  have hne' : (eM.symm x : H) ≠ (eM.symm y : H) := fun h =>
    hne (eM.symm.injective (Subtype.ext h))
  obtain ⟨V, -, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      hx hy hcomm hne'
  exact CFSG.LieType.SteinbergBR.le_pRank_of_card one_lt_two V hV (by rw [hVcard]; norm_num)

theorem isCentralInvolution_of_sylow_le_cen {G : Type} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ Cen t) :
    IsCentralInvolution t := by
  refine ⟨ht, S, ?_, fun s hs => (mem_Cen.1 (hS hs)).symm⟩
  have hcen : t ∈ Subgroup.centralizer (S : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun q hq => (mem_Cen.1 (hS hq)).symm
  have hZp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (S : Subgroup G) :=
    (Subgroup.zpowers_le.mpr hcen).trans (Subgroup.centralizer_le_normalizer (S : Set G))
  have hsup : IsPGroup 2 (Subgroup.zpowers t ⊔ (S : Subgroup G) : Subgroup G) :=
    hZp.to_sup_of_normal_right' S.isPGroup' hnorm
  have hEq : Subgroup.zpowers t ⊔ (S : Subgroup G) = S := S.is_maximal' hsup le_sup_right
  change t ∈ (S : Subgroup G)
  rw [← hEq]
  exact (le_sup_left : Subgroup.zpowers t ≤ Subgroup.zpowers t ⊔ (S : Subgroup G))
    (Subgroup.mem_zpowers t)

theorem noLocalA6_inner
    (hComp : ComponentList) (hD3 : K0Data3) (hP : PumpUpData) {G : Type}
    [Group G] [Finite G] (hH : Hyp G) {t : G} {K : Subgroup G} {c : G}
    (hd : LocalData t K c) (hsh : ShapeA6 ↥K)
    (hinner : ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, huniq⟩ := hComp G hH t hd.order_t K hd.comp
  have hcen : Subgroup.center ↥K = ⊥ := hD3.center_bot ↥K (Or.inr (Or.inr (Or.inl hsh)))
  obtain ⟨-, hncen, hrk⟩ := a6_terminal_facts hComp hP hH hd.order_t hd.comp hsh
  obtain ⟨P, hDC, hDK, hcomm, hdisj, hCKD, htSD, hcases⟩ :=
    inner_split hH hd.order_t hd.comp huniq hcen hinner hd.quat hd.order_c hd.mem_cen
      hd.centralizes (D := Cen t ⊓ Subgroup.centralizer (K : Set G)) rfl
  have hnc : ∀ S : Sylow 2 G, ¬ ((S : Subgroup G) ≤ Cen t) := fun S hS =>
    hncen (isCentralInvolution_of_sylow_le_cen hd.order_t S hS)
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥K) := inferInstance
  let eK : ↥((T : Subgroup ↥K).map K.subtype) ≃* D8M :=
    (sylowMapEquiv K T).symm.trans (sylow_two_of_shapeA6 hsh T).some
  rcases hcases with hQ8' | hQ16' | hSD
  · exact noncentral_direct_product hnc hd.comp.1 hDC hcomm hdisj hCKD (sylow_map_le K T)
      (sylow_map_isPGroup K T) (sylow_map_max K T) (sylow_map_le _ P) (sylow_map_isPGroup _ P)
      (sylow_map_max _ P) htSD eK hQ8'.some
      (by rw [eD_t_eq_a htSD hd.order_t (Or.inl rfl) hQ8'.some]; exact fix_D8_quat (Or.inl rfl))
  · exact noncentral_direct_product hnc hd.comp.1 hDC hcomm hdisj hCKD (sylow_map_le K T)
      (sylow_map_isPGroup K T) (sylow_map_max K T) (sylow_map_le _ P) (sylow_map_isPGroup _ P)
      (sylow_map_max _ P) htSD eK hQ16'.some
      (by rw [eD_t_eq_a htSD hd.order_t (Or.inr rfl) hQ16'.some]; exact fix_D8_quat (Or.inr rfl))
  ·
    have e' := (((P : Subgroup ↥(Cen t ⊓ Subgroup.centralizer (K : Set G))).equivMapOfInjective
      (Subgroup.inclusion hDK) (Subgroup.inclusion_injective hDK)).symm.trans hSD.some)
    have := two_le_pRank_of_sd16 _ e'
    rw [hrk] at this
    exact absurd this (by norm_num)

theorem noLocalA6_of
    (hComp : ComponentList) (hD3 : K0Data3) (hP : PumpUpData)
    (hOut : NoLocalA6Outer) : NoLocalA6 := by
  intro G _ _ hH t K c hd hsh
  by_cases hinner : ∀ g ∈ Cen t, ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹
  · exact noLocalA6_inner hComp hD3 hP hH hd hsh hinner
  · exact hOut G hH t K c hd hsh hinner

end CFSG.GH74.E2
