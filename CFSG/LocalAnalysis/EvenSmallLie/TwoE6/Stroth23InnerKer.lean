module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerLevi
public import CFSG.Monster.B.GSide.TriangleData
public import CFSG.Monster.B.GSide.HSylowBetaRank
public import CFSG.Monster.B.GSide.EdgeHom
public import CFSG.Monster.B.TwoA.Amalgam.TriangleCore
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate16042
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3032
public import Certificates.Certificate3068
public import Certificates.Certificate3069

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.B.GSide CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.LieType.Chevalley.C2E6Std CFSG.Blueprint.Chevalley

@[expose] noncomputable def HS : Subgroup Shat := (commutator (vStab cv0)).map (vStab cv0).subtype

theorem coe_mem_HS_iff (y : vStab cv0) : (y : Shat) ∈ HS ↔ y ∈ commutator (vStab cv0) :=
  Subgroup.mem_map_iff_mem (vStab cv0).subtype_injective

theorem HS_le : HS ≤ vStab cv0 := Subgroup.map_subtype_le _

theorem mul_mem_HS_iff {x y : Shat} (hx : x ∈ vStab cv0) (hy : y ∈ vStab cv0) :
    x * y ∈ HS ↔ (x ∈ HS ↔ y ∈ HS) := by
  have h := Subgroup.mul_mem_iff_of_index_two index_commutator_H (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  rw [← coe_mem_HS_iff, ← coe_mem_HS_iff, ← coe_mem_HS_iff] at h
  exact h

theorem mul_mem_HS_of_not_mem {x y : Shat} (hx : x ∈ vStab cv0) (hy : y ∈ vStab cv0)
    (hx' : x ∉ HS) (hy' : y ∉ HS) : x * y ∈ HS :=
  (mul_mem_HS_iff hx hy).2 (iff_of_false hx' hy')

theorem clabelS_cv0_mem_HS : clabelS cv0 ∈ HS :=
  (coe_mem_HS_iff cV0).2 cV0_mem_commutator_H.1

theorem clabelS_mem_HS_of_adj {w : CVert} (hw : cgraph.Adj cv0 w) : clabelS w ∈ HS := by
  have hy : (⟨clabelS w, clabelS_mem_vStab_cv0_of_adj hw⟩ : vStab cv0) ∈ RA := ⟨w, hw, rfl⟩
  obtain ⟨h, hh⟩ := isConj_iff.1 ((mem_RA_iff_isConj _).1 hy)
  refine (coe_mem_HS_iff ⟨clabelS w, clabelS_mem_vStab_cv0_of_adj hw⟩).2 ?_
  rw [← hh]
  exact (commutator_normal ⊤ ⊤).conj_mem _ cV0_mem_commutator_H.2 h

theorem clabelS_not_mem_HS_of_dist_three {u : CVert} (hu : cgraph.dist cv0 u = 3)
    (hmem : clabelS u ∈ vStab cv0) : clabelS u ∉ HS := by
  rw [show clabelS u = ((⟨clabelS u, hmem⟩ : vStab cv0) : Shat) from rfl, coe_mem_HS_iff]
  exact beta_not_mem_commutator hu rfl

theorem triLab_le_HS (j : Fin 2) : triLab j ≤ HS := by
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl | rfl)
  · exact clabelS_cv0_mem_HS
  · exact clabelS_mem_HS_of_adj cgraph_adj_cv0_cw0
  · exact clabelS_mem_HS_of_adj (cgraph_adj_cu j).1

noncomputable abbrev nw0 : cgraph.neighborSet cv0 := ⟨cw0, cgraph_adj_cv0_cw0⟩

noncomputable abbrev nu (j : Fin 2) : cgraph.neighborSet cv0 := ⟨cu j, (cgraph_adj_cu j).1⟩

theorem exists_compat_rootInv : ∃ (ρ : vStab cv0 →* GStar)
    (iv : cgraph.neighborSet cv0 ≃ rootClass),
    IsCompatLocal cv0 ρ iv ∧ (iv nw0 : stdGroup) = rootInv := by
  obtain ⟨ρ, iv, hρ⟩ := exists_isCompatLocal cv0
  obtain ⟨h, hh⟩ := isConj_iff.1 (iv nw0).2
  refine ⟨conjRho h ρ, iv.trans (rootClassConj h), hρ.conj h, ?_⟩
  rw [Equiv.trans_apply, coe_rootClassConj, ← hh]
  group

section Compat

variable {ρ : vStab cv0 →* GStar} {iv : cgraph.neighborSet cv0 ≃ rootClass}

theorem commute_iff (hρ : IsCompatLocal cv0 ρ iv) (y : vStab cv0)
    (z : cgraph.neighborSet cv0) :
    Commute (ρ y) (SemidirectProduct.inl (iv z : stdGroup)) ↔ (y : Shat) ∈ vStab z := by
  have h := hρ.2.2.1 y z
  constructor
  · intro hc
    have e : (ρ y)⁻¹ * SemidirectProduct.inl (iv z : stdGroup) * ρ y =
        SemidirectProduct.inl (iv z : stdGroup) := by
      rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]
    rw [e] at h
    have h2 : stabAct y z = z :=
      iv.injective (Subtype.ext (SemidirectProduct.inl_injective h))
    exact mem_vStab.2 (congrArg Subtype.val h2)
  · intro hy
    have h2 : stabAct y z = z := Subtype.ext (mem_vStab.1 hy)
    rw [h2] at h
    change ρ y * SemidirectProduct.inl (iv z : stdGroup) =
      SemidirectProduct.inl (iv z : stdGroup) * ρ y
    calc ρ y * SemidirectProduct.inl (iv z : stdGroup) =
        ρ y * ((ρ y)⁻¹ * SemidirectProduct.inl (iv z : stdGroup) * ρ y) := by rw [← h]
      _ = SemidirectProduct.inl (iv z : stdGroup) * ρ y := by group

theorem eq_one_or_eq_cV0 (hρ : IsCompatLocal cv0 ρ iv) {y : vStab cv0} (hy : ρ y = 1) :
    y = 1 ∨ y = cV0 :=
  CFSG.Monster.B.CTIB.eq_one_or_eq_of_mem_zpowers (orderOf_cStab cv0)
    (ker_eq_zpowers_cStab hρ.2.1 ▸ MonoidHom.mem_ker.2 hy)

theorem mem_commutator_iff (hρ : IsCompatLocal cv0 ρ iv) (y : vStab cv0) :
    y ∈ commutator (vStab cv0) ↔ (ρ y).right = 1 := by
  have hmap : (commutator (vStab cv0)).map ρ = CFSG.Monster.B.E6.Ginl := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.2 hρ.1, ← _root_.commutator_def,
      CFSG.Monster.B.E6.commutator_GStar]
  constructor
  · intro hy
    have hmem : ρ y ∈ (commutator (vStab cv0)).map ρ := mem_map_of_mem _ hy
    rw [hmap] at hmem
    obtain ⟨x, hx⟩ := hmem
    rw [← hx, SemidirectProduct.right_inl]
  · intro hr
    have hmem : ρ y ∈ CFSG.Monster.B.E6.Ginl := ⟨(ρ y).left, by
      conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right (ρ y), hr, map_one, mul_one]⟩
    rw [← hmap] at hmem
    obtain ⟨w, hw, hwy⟩ := hmem
    have hk : ρ (w⁻¹ * y) = 1 := by rw [map_mul, map_inv, hwy, inv_mul_cancel]
    have hy' : y = w * (w⁻¹ * y) := (mul_inv_cancel_left w y).symm
    rcases eq_one_or_eq_cV0 hρ hk with h | h
    · rw [hy', h, mul_one]
      exact hw
    · rw [hy', h]
      exact mul_mem hw cV0_mem_commutator_H.1

def rootModelOf (hρ : IsCompatLocal cv0 ρ iv) : RootModel cv0 where
  iv := iv
  adj_iff := hρ.2.2.2.1
  exists_act γ := by
    obtain ⟨y, rfl⟩ := hρ.1 γ
    exact ⟨y, y.2, fun v => ⟨(stabAct y v).2, hρ.2.2.1 y v⟩⟩
  act y hy := ⟨ρ ⟨y, hy⟩, fun v => ⟨(stabAct ⟨y, hy⟩ v).2, hρ.2.2.1 ⟨y, hy⟩ v⟩⟩

theorem iv_cu_one_mem (hρ : IsCompatLocal cv0 ρ iv) (hw : (iv nw0 : stdGroup) = rootInv) :
    (iv (nu 1) : stdGroup) ∈ levPoints (repLevel 2) := by
  have h := (rootModelOf hρ).triType_eq_orbSize nw0 (nu 1)
  rw [triType_cu.2] at h
  obtain ⟨g, hg⟩ := (mem_rootClass_iff _).1 (iv (nu 1)).2
  obtain ⟨i, hi⟩ := exists_repLevel g
  have h2 : orbSize ((rootModelOf hρ).pt nw0) ((rootModelOf hρ).pt (nu 1)) = repSize i := by
    change (conjOrbit (centralizer {SemidirectProduct.inl (iv nw0 : stdGroup)})
      (SemidirectProduct.inl (iv (nu 1) : stdGroup))).ncard = repSize i
    rw [hw, ← hg, show (SemidirectProduct.inl rootInv : GStar) = rootStar from rfl,
      centralizer_rootStar, conjOrbit_parStar_rootMap,
      Set.ncard_image_of_injective _ SemidirectProduct.inl_injective, hi, ncard_levPoints]
  have hi2 : i = 2 := repSize_injective ((h2.symm.trans h.symm).trans (by decide))
  rw [← hg, ← hi2, ← hi]
  exact rootMap_mem_levPoints g

end Compat

theorem exists_triKer_not_mem (j : Fin 2) : ∃ k ∈ triKer j, k ∉ HS := by
  obtain ⟨ρ, iv, hρ, hw⟩ := exists_compat_rootInv
  obtain ⟨g, hg⟩ := (mem_rootClass_iff _).1 (iv (nu j)).2
  have hx₀ : leviEmb phiL ∈ parStar firstJ := by
    rw [← centralizer_rootStar]
    exact leviEmb_mem_centralizer _
  have hx₀r : (leviEmb phiL).right ≠ 1 :=
    leviEmb_right_ne_one (by rw [phiL]; exact ofAdd_one_ne_one)
  have hmem : leviEmb phiL * SemidirectProduct.inl (rootMap g) * (leviEmb phiL)⁻¹ ∈
      conjOrbit (parStar firstJ) (SemidirectProduct.inl (rootMap g)) := ⟨_, hx₀, rfl⟩
  rw [conjOrbit_parStar_rootMap, ← conjOrbit_PJ_rootMap] at hmem
  obtain ⟨_, ⟨p, hp, rfl⟩, hpx⟩ := hmem
  have hpS : SemidirectProduct.inl p ∈ parStar firstJ :=
    mem_parStar.2 (by rw [SemidirectProduct.left_inl]; exact Subgroup.mem_subgroupOf.1 hp)
  have hx₁ : (SemidirectProduct.inl p)⁻¹ * leviEmb phiL ∈ parStar firstJ :=
    mul_mem (inv_mem hpS) hx₀
  have hx₁r : ((SemidirectProduct.inl p)⁻¹ * leviEmb phiL).right ≠ 1 := by
    simpa only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, inv_one, one_mul] using hx₀r
  have hx₁c : Commute ((SemidirectProduct.inl p)⁻¹ * leviEmb phiL)
      (SemidirectProduct.inl (iv (nu j) : stdGroup)) := by
    rw [← hg]
    refine mul_inv_eq_iff_eq_mul.1 ?_
    calc (SemidirectProduct.inl p)⁻¹ * leviEmb phiL * SemidirectProduct.inl (rootMap g) *
          ((SemidirectProduct.inl p)⁻¹ * leviEmb phiL)⁻¹ =
        (SemidirectProduct.inl p)⁻¹ * (leviEmb phiL * SemidirectProduct.inl (rootMap g) *
          (leviEmb phiL)⁻¹) * SemidirectProduct.inl p := by group
      _ = SemidirectProduct.inl (rootMap g) := by
          rw [← hpx, map_mul, map_mul, map_inv]
          group
  obtain ⟨y, hy⟩ := hρ.1 ((SemidirectProduct.inl p)⁻¹ * leviEmb phiL)
  have hyw : (y : Shat) ∈ vStab cw0 := by
    refine (commute_iff hρ y nw0).1 ?_
    rw [hy, hw]
    rw [← centralizer_rootStar] at hx₁
    exact mem_centralizer_singleton_iff.1 hx₁
  have hyu : (y : Shat) ∈ vStab (cu j) := by
    refine (commute_iff hρ y (nu j)).1 ?_
    rw [hy]
    exact hx₁c
  refine ⟨y, ⟨⟨y.2, hyw⟩, hyu⟩, fun h => hx₁r ?_⟩
  rw [← hy]
  exact (mem_commutator_iff hρ y).1 ((coe_mem_HS_iff y).1 h)

theorem mem_HS_of_centralizes_zero {k : Shat} (hk : k ∈ triKer 0)
    (hc : ∀ x ∈ triKer 0, x ∈ HS → Commute k x) : k ∈ HS := by
  by_contra hkH
  have hz : k ∈ (center (triKer 0)).map (triKer 0).subtype := by
    refine mem_map_center_iff.2 ⟨hk, fun x hx => ?_⟩
    by_cases hxH : x ∈ HS
    · exact (hc x hx hxH).eq.symm
    · have h1 : k⁻¹ * x ∈ HS := mul_mem_HS_of_not_mem (inv_mem hk.1.1) hx.1.1
        (fun h => hkH (by simpa using inv_mem h)) hxH
      have h2 := (hc _ (mul_mem (inv_mem hk) hx) h1).eq
      calc x * k = k * ((k⁻¹ * x) * k) := by group
        _ = k * (k * (k⁻¹ * x)) := by rw [← h2]
        _ = k * x := by group
  rw [center_triKer_zero] at hz
  exact hkH (triLab_le_HS 0 hz)

theorem mem_HS_of_centralizes_one {k : Shat} (hk : k ∈ triKer 1)
    (hc : ∀ x ∈ triKer 1, x ∈ HS → Commute k x) : k ∈ HS := by
  by_contra hkH
  obtain ⟨ρ, iv, hρ, hw⟩ := exists_compat_rootInv
  obtain ⟨y', hyt, hyr, hno⟩ := exists_inner_not_commute_outer (iv_cu_one_mem hρ hw)
  have hyc : ρ ⟨k, hk.1.1⟩ ∈ parStar firstJ := by
    rw [← centralizer_rootStar, mem_centralizer_singleton_iff]
    have h := (commute_iff hρ ⟨k, hk.1.1⟩ nw0).2 hk.1.2
    rw [hw] at h
    exact h.eq
  have hyr1 : (ρ ⟨k, hk.1.1⟩).right ≠ 1 := fun h =>
    hkH ((coe_mem_HS_iff _).2 ((mem_commutator_iff hρ _).2 h))
  obtain ⟨z, hz⟩ := hρ.1 (SemidirectProduct.inl y')
  have hzw : (z : Shat) ∈ vStab cw0 := by
    refine (commute_iff hρ z nw0).1 ?_
    rw [hz, hw]
    exact hyt.map SemidirectProduct.inl
  have hzu : (z : Shat) ∈ vStab (cu 1) := by
    refine (commute_iff hρ z (nu 1)).1 ?_
    rw [hz]
    exact hyr.map SemidirectProduct.inl
  have hzH : (z : Shat) ∈ HS :=
    (coe_mem_HS_iff z).2 ((mem_commutator_iff hρ z).2 (by rw [hz, SemidirectProduct.right_inl]))
  have hkz := hc z ⟨⟨z.2, hzw⟩, hzu⟩ hzH
  have hyz : Commute (⟨k, hk.1.1⟩ : vStab cv0) z := Subtype.ext hkz.eq
  apply hno _ hyc hyr1
  rw [← hz]
  exact hyz.map ρ

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
