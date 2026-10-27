module

public import CFSG.GroupTheory.QuasiDihedralFusion.SimpleNormal

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.GorensteinWalter

universe u

variable {H : Type u} [Group H]

section General

theorem map_conj_centralizer_singleton (c z : H) :
    (Subgroup.centralizer ({z} : Set H)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * z * c⁻¹} : Set H) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    calc c * w * c⁻¹ * (c * z * c⁻¹) = c * (w * z) * c⁻¹ := by group
      _ = c * (z * w) * c⁻¹ := by rw [hw]
      _ = c * z * c⁻¹ * (c * w * c⁻¹) := by group
  · intro hy
    refine ⟨c⁻¹ * y * c, ?_, by group⟩
    calc c⁻¹ * y * c * z = c⁻¹ * (y * (c * z * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * z * c⁻¹ * y) * c := by rw [hy]
      _ = z * (c⁻¹ * y * c) := by group

theorem nonempty_centralizer_conj_equiv (c z : H) :
    Nonempty (Subgroup.centralizer ({z} : Set H) ≃*
      Subgroup.centralizer ({c * z * c⁻¹} : Set H)) :=
  ⟨((Subgroup.centralizer ({z} : Set H)).equivMapOfInjective (MulAut.conj c).toMonoidHom
    (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr (map_conj_centralizer_singleton c z))⟩

theorem le_centralizer_of_mem_centerOf {S : Subgroup H} {z : H} (hz : z ∈ centerOf S) :
    S ≤ Subgroup.centralizer ({z} : Set H) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s hs

theorem mem_center_centralizer_singleton (z : H) :
    (⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({z} : Set H)) ∈
        Subgroup.center (Subgroup.centralizer ({z} : Set H)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.property)

theorem eq_of_isConj_of_mem_center {G : Type*} [Group G] {y z : G}
    (hz : z ∈ Subgroup.center G) (h : IsConj y z) : y = z := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have hy : y = c⁻¹ * z * c := by
    rw [← hc]
    group
  rw [hy, Subgroup.mem_center_iff.mp hz c⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem centralizer_subgroupOf {C V : Subgroup H} (hVC : V ≤ C) :
    Subgroup.centralizer ((V.subgroupOf C : Subgroup C) : Set C) =
      (Subgroup.centralizer (V : Set H)).subgroupOf C := by
  ext c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    exact congrArg Subtype.val (h ⟨v, hVC hv⟩ hv)
  · intro h w hw
    exact Subtype.ext (h w hw)

theorem outerAutomizerIndex_subgroupOf {C V : Subgroup H} (hVC : V ≤ C)
    (hN : Subgroup.normalizer (V : Set H) ≤ C) :
    outerAutomizerIndex (V.subgroupOf C) = outerAutomizerIndex V := by
  have hcent : Subgroup.centralizer (V : Set H) ≤ C :=
    (Subgroup.centralizer_le_normalizer _).trans hN
  unfold outerAutomizerIndex
  rw [← Subgroup.subgroupOf_normalizer_eq hVC, centralizer_subgroupOf hVC,
    ← Subgroup.subgroupOf_sup hVC hcent, Subgroup.relIndex_subgroupOf hN]

end General

section Semidihedral

variable [Finite H] {n : ℕ}

theorem sdV_sq_eq_z (hn : 4 ≤ n) : (r n ^ (2 ^ (n - 3))) ^ 2 = z n := by
  rw [← pow_mul, z, half_eq_two_mul_quarter (by omega), mul_comm]

theorem rs_sq_eq_z (hn : 4 ≤ n) : (r n * s n) ^ 2 = z n := by
  simpa only [pow_one] using reflection_square_nat n (by omega) 1

theorem semidihedral_centralizer_isQGroup (hH : IsQDGroup H) (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    IsQGroup (Subgroup.centralizer
      ({FocalFusion.ambientHom n (S : Subgroup H) f (z n)} : Set H)) := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  set C := Subgroup.centralizer ({ι (z n)} : Set H) with hC
  have hzS : ι (z n) ∈ centerOf (S : Subgroup H) := by
    rw [centerOf_eq_zpowers_z hn (S : Subgroup H) f]
    exact Subgroup.mem_zpowers _
  have hSC : (S : Subgroup H) ≤ C := le_centralizer_of_mem_centerOf hzS
  let SC : Sylow 2 C := S.subtype hSC
  let fC : SemidihedralGroup n ≃* SC := f.trans (Subgroup.subgroupOfEquivOfLe hSC).symm
  set ιC := FocalFusion.ambientHom n (SC : Subgroup C) fC with hιC
  have hzcen : ιC (z n) ∈ Subgroup.center C := mem_center_centralizer_singleton (ι (z n))
  have ha : ¬ IsConj (ιC (s n)) (ιC (z n)) := by
    intro h
    exact s_ne_z hn (FocalFusion.ambientHom_injective n _ fC
      (eq_of_isConj_of_mem_center hzcen h))
  have hQD : SemidihedralFusionQD S f := (semidihedral_isQDGroup_iff hn S f).mp hH
  have hb : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3)))) :=
    isConj_of_conjClassCountOfOrder_eq_one hQD.orderFourClasses _ _
      (by rw [orderOf_ambientHom, orderOf_rs hn]) (by rw [orderOf_ambientHom, orderOf_sdV hn])
  have hbC : IsConj (ιC (r n * s n)) (ιC (r n ^ (2 ^ (n - 3)))) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hb
    have hconj : c * ι (z n) * c⁻¹ = ι (z n) := by
      calc c * ι (z n) * c⁻¹ = c * ι (r n * s n) ^ 2 * c⁻¹ := by
            rw [← map_pow, rs_sq_eq_z hn]
        _ = (c * ι (r n * s n) * c⁻¹) ^ 2 := conj_pow.symm
        _ = ι (r n ^ (2 ^ (n - 3))) ^ 2 := by rw [hc]
        _ = ι (z n) := by rw [← map_pow, sdV_sq_eq_z hn]
    have hcC : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hconj)
    exact isConj_iff.mpr ⟨⟨c, hcC⟩, Subtype.ext hc⟩
  rcases semidihedral_two_fusion_classification hn SC fC with hC1 | hC2 | hC3 | hC4
  · have h := hC1.involutionClasses
    rw [involutionClassCount_eq_two hn SC fC ha] at h
    omega
  · exact isQGroup_of_semidihedralFusionQ hn SC fC hC2
  · have h := hC3.orderFourClasses
    rw [orderFourClassCount_eq_one hn SC fC hbC] at h
    omega
  · have h := hC4.orderFourClasses
    rw [orderFourClassCount_eq_one hn SC fC hbC] at h
    omega

end Semidihedral

section Wreathed

variable [Finite H] {n : ℕ}

theorem wreathed_centralizer_isQGroup (hH : IsQDGroup H) (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    IsQGroup (Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set H)) := by
  set z0 := wreathModelHom S e (Original.x (2 ^ n)) with hz0
  set C := Subgroup.centralizer ({z0} : Set H) with hC
  have hzS : z0 ∈ centerOf (S : Subgroup H) := by
    rw [centerOf_eq_modelCenter hn S e]
    exact wreath_x_mem_modelCenter S e
  have hSC : (S : Subgroup H) ≤ C := le_centralizer_of_mem_centerOf hzS
  let SC : Sylow 2 C := S.subtype hSC
  let eC : (SC : Subgroup C) ≃* Wreath (2 ^ n) := (Subgroup.subgroupOfEquivOfLe hSC).trans e
  have hzcen : wreathModelHom SC eC (Original.x (2 ^ n)) ∈ Subgroup.center C :=
    mem_center_centralizer_singleton z0
  have ha : ¬ IsConj (wreathModelHom SC eC (Original.x2 (2 ^ n)))
      (wreathModelHom SC eC (Original.x (2 ^ n))) := by
    intro h
    exact modelHom_x_ne_x2 SC eC (by omega) (eq_of_isConj_of_mem_center hzcen h).symm
  have hQD : WreathedFusionQD S e := (wreathed_isQDGroup_iff hn S e).mp hH
  have hVS : modelV S e ≤ C := (modelV_le_sylow S e).trans hSC
  have hVC : modelV SC eC = (modelV S e).subgroupOf C := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVS]
    change ((Original.V (2 ^ n)).map (wreathModelHom SC eC)).map C.subtype =
      (Original.V (2 ^ n)).map (wreathModelHom S e)
    rw [Subgroup.map_map]
    rfl
  have hxZ : Original.x (2 ^ n) ∈ Original.Z (2 ^ n) :=
    (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _
  have hNC : Subgroup.normalizer (modelV S e : Set H) ≤ C := by
    intro g hg
    have h := modelVNormalizer_centralizes_original_center n hn S e g hg _ hxZ
    exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h)
  have hidx : outerAutomizerIndex (modelV SC eC) = 6 := by
    rw [hVC, outerAutomizerIndex_subgroupOf hVS hNC, hQD.quaternionIndex]
  rcases wreathed_two_fusion_classification hn SC eC with hC1 | hC2 | hC3 | hC4
  · exact (ha (isConj_of_conjClassCountOfOrder_eq_one hC1.involutionClasses _ _
      (orderOf_wreath_x2 hn SC eC) (orderOf_wreath_x hn SC eC))).elim
  · exact isQGroup_of_wreathedFusionQ hn SC eC hC2
  · have h := hC3.quaternionIndex
    rw [hidx] at h
    omega
  · have h := hC4.quaternionIndex
    rw [hidx] at h
    omega

end Wreathed

section Main

variable [Finite H]

theorem IsQDGroup.centralizer_isQGroup (hH : IsQDGroup H) (x : H) (hx : orderOf x = 2) :
    IsQGroup (Subgroup.centralizer ({x} : Set H)) ∧
      ∀ h : ℕ, HasQDOrWreathedSylowOfHeight H h →
        HasQDOrWreathedSylowOfHeight (Subgroup.centralizer ({x} : Set H)) h := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨z0, hz0, hSC, hQ⟩ : ∃ z0 : H, orderOf z0 = 2 ∧
      (S : Subgroup H) ≤ Subgroup.centralizer ({z0} : Set H) ∧
      IsQGroup (Subgroup.centralizer ({z0} : Set H)) := by
    obtain ⟨h, hh⟩ := hH.sylow
    rcases hh with ⟨-, n, hn⟩ | hw
    · obtain ⟨f⟩ := hn.2 S
      refine ⟨FocalFusion.ambientHom n (S : Subgroup H) f (z n), ?_, ?_,
        semidihedral_centralizer_isQGroup hH hn.1 S f⟩
      · rw [orderOf_ambientHom, orderOf_z n (by have := hn.1; omega)]
      · apply le_centralizer_of_mem_centerOf
        rw [centerOf_eq_zpowers_z hn.1 (S : Subgroup H) f]
        exact Subgroup.mem_zpowers _
    · obtain ⟨e⟩ := hw.2 S
      refine ⟨wreathModelHom S e (Original.x (2 ^ h)), orderOf_wreath_x hw.1 S e, ?_,
        wreathed_centralizer_isQGroup hH hw.1 S e⟩
      apply le_centralizer_of_mem_centerOf
      rw [centerOf_eq_modelCenter hw.1 S e]
      exact wreath_x_mem_modelCenter S e
  obtain ⟨c, hc⟩ := isConj_iff.mp (hH.involutions_isConj z0 x hz0 hx)
  subst hc
  obtain ⟨σ⟩ := nonempty_centralizer_conj_equiv c z0
  exact ⟨IsQGroup.of_mulEquiv σ hQ, fun h hh => (hh.of_le S hSC).of_mulEquiv σ⟩

end Main

end CFSG.QuasiDihedralFusion
