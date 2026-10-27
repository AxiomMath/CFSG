module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralB4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameB4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralC3

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD (hiF4 isRoot_hiF4 rankOneHiF4 commutes_rankOneHiF4
  commutes_iSup_left)
open scoped MatrixGroups

theorem eq_of_isComponent_le_sup_of_isSolvable {G : Type*} [Group G] {D L₁ L₂ : Subgroup G}
    (hD : D = L₁ ⊔ L₂) (hq₁ : IsQuasisimple L₁) (hs₂ : Group.IsSolvable L₂)
    (hn₁ : (L₁.subgroupOf D).Normal) {M : Subgroup G} (hM : IsComponent M) (hMD : M ≤ D) :
    M = L₁ := by
  have hL₁D : L₁ ≤ D := hD ▸ le_sup_left
  have hL₂D : L₂ ≤ D := hD ▸ le_sup_right
  have hM' : IsComponent (M.subgroupOf D) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMD).symm hM.1,
      hM.2.subgroupOf⟩
  have hq : IsQuasisimple (L₁.subgroupOf D) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL₁D).symm hq₁
  have htop : L₁.subgroupOf D ⊔ L₂.subgroupOf D = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hL₁D hL₂D, ← hD, Subgroup.subgroupOf_self]
  have hs : Group.IsSolvable (L₂.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hL₂D).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hL₂D).injective
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (L₁.subgroupOf D)).comp (L₂.subgroupOf D).subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, eq_top_iff]
    have h := congrArg (Subgroup.map (QuotientGroup.mk' (L₁.subgroupOf D))) htop
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    rw [← h]
    refine sup_le ?_ le_rfl
    rintro _ ⟨x, hx, rfl⟩
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  have hsolv : Group.IsSolvable (D ⧸ L₁.subgroupOf D) := Group.isSolvable_of_surjective hsurj
  have h := eq_of_isComponent_of_normal_quasisimple hq hsolv hM'
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hMD, inf_of_le_left hL₁D] at h
  exact h

theorem f4_toral_C3_component_three
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h3 : Nat.card K = 3)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsC3))} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
  have : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .F4 K f4LeviC3 with hH_def
  set Q := rootSubgroup .F4 K hiF4 ⊔ rootSubgroup .F4 K (-hiF4) with hQ_def
  have hS : rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3)) = H ⊔ Q := by
    rw [rootCharKernel_f4BitsC3 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hSX' : H ⊔ Q ≤ (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := hS ▸ hSX
  have hHX : H ≤ (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := le_sup_left.trans hSX'
  have hQX : Q ≤ (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := le_sup_right.trans hSX'
  have hD : (rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
        (toralCentralizer .F4 K (bitsTuple f4BitsC3)) =
      H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3)) ⊔
        Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3)) := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hHX hQX
  obtain ⟨-, -, -, hqH, hlieH⟩ := f4_levi_C3_recognition_frame hp hp2 hK h2
  obtain ⟨-, -, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .F4 K hK2 isRoot_hiF4
  have hsQ : Group.IsSolvable Q := (hfin.1 h3).1
  have hQmap : (rankOneHiF4 K).map (adjointGroup .F4 K).subtype = Q := by
    rw [rankOneHiF4, Subgroup.map_sup]
    simp only
    rw [map_subtype_rootGroup _ isRoot_hiF4, map_subtype_rootGroup _ (IsRoot.neg isRoot_hiF4)]
  have hcomm' : Commutes (⨆ k, rankOne (f4Datum K).rootGroup (c3Node k)) (rankOneHiF4 K) :=
    commutes_iSup_left.2 fun k => (commutes_rankOneHiF4 (c3Node_val_ne_zero k)).symm
  have hcomm : Commutes H Q := by
    rw [hH_def, ← map_subtype_iSup_c3, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  have hq₁ : IsQuasisimple (H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHX).symm hqH
  have hs₂ : Group.IsSolvable (Q.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQX).injective
  have hn₁ : ((H.subgroupOf (toralCentralizer .F4 K (bitsTuple f4BitsC3))).subgroupOf
      ((rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3))).subgroupOf
        (toralCentralizer .F4 K (bitsTuple f4BitsC3)))).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subtype.ext (hcomm x.1 hx y.1 hy))
  have h := eq_of_isComponent_le_sup_of_isSolvable hD hq₁ hs₂ hn₁ hM
    (le_of_isComponent_of_solvable_quotient hsolv hM)
  let e : M ≃* H := (MulEquiv.subgroupCongr h).trans (Subgroup.subgroupOfEquivOfLe hHX)
  exact ⟨.PSp, 3, f, hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlieH⟩

theorem f4_toral_B4_component_frame
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsB4))} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨hp, hf, by norm_num, hp2⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _
      (bitsTuple_mem (K := K) f4BitsB4)
  have hker : rootCharKernel (bitsTuple (K := K) f4BitsB4) =
      kernelRoots (maskChar (τ := .F4) f4BitsB4) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_B4_F4_frame hp hp2 hK h2
  have hSim : (⨆ k, b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    rw [map_subtype_iSup_b4Chain, hker]
  let e₁ : ↥(⨆ k, b4Chain K k) ≃* rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) :=
    ((⨆ k, b4Chain K k).equivMapOfInjective _ (adjointGroup .F4 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hSim)
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* ↥(⨆ k, b4Chain K k) := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁.symm)
  exact ⟨.POmegaOdd, 4, f, hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie⟩

end CFSG.ComponentClassification.CatLeafProof
