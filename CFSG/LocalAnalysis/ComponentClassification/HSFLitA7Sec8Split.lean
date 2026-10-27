module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Local
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8Elem
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Section3
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitExclusion
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TBLitIntrinsicTypes
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallAbelianModels
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.Sporadic.Schreier.J4SOrder
public import CFSG.Sporadic.Th.Max3.Relations
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

theorem inv_mul_mem_T (h4 : S.Sec4 F T₁) {n₁ n₂ : X} (h₁ : n₁ ∈ T₁) (h₂ : n₂ ∈ T₁)
    (h : n₁ * S.t * n₁⁻¹ = n₂ * S.t * n₂⁻¹) : n₁⁻¹ * n₂ ∈ S.data.T := by
  refine S.data.mem_T_of_commute h4.isPGroup h4.le (mul_mem (inv_mem h₁) h₂) ?_
  calc n₁⁻¹ * n₂ * S.t = n₁⁻¹ * (n₂ * S.t * n₂⁻¹) * n₂ := by group
    _ = n₁⁻¹ * (n₁ * S.t * n₁⁻¹) * n₂ := by rw [h]
    _ = S.t * (n₁⁻¹ * n₂) := by group

theorem conj_eq_of_mem_T {τ a : X} (hτ : τ ∈ S.data.T) (ha : a ∈ S.data.T) :
    τ * a * τ⁻¹ = a ∨ τ * a * τ⁻¹ = S.z * a := by
  rcases S.commutator_eq hτ ha with h | h
  · left
    calc τ * a * τ⁻¹ = τ * a * τ⁻¹ * a⁻¹ * a := by group
      _ = a := by rw [h, one_mul]
  · right
    calc τ * a * τ⁻¹ = τ * a * τ⁻¹ * a⁻¹ * a := by group
      _ = S.z * a := by rw [h]

variable {yi ki ui : X}

theorem ki_not_mem_z (hk : IsK (S := S) ki) : ki ≠ 1 ∧ ki ≠ S.z :=
  ⟨hk.ne_one, fun h => hk.not_mem (h ▸ mem_sup_left (mem_zpowers _))⟩

theorem u_comm_v (D : S.Sec6 T₁ yi ki ui) : D.u * D.v = D.v * D.u :=
  D.u_comm_C D.v (D.C_eq ▸ subset_closure (by simp))

theorem v_mem_T₁ (D : S.Sec6 T₁ yi ki ui) : D.v ∈ T₁ :=
  D.T₁_eq.symm.le (mem_sup_left (mem_sup_right (mem_zpowers _)))

theorem w₁_mem_T₁ (D : S.Sec6 T₁ yi ki ui) : D.w₁ ∈ T₁ :=
  D.T₁_eq.symm.le (mem_sup_right (mem_zpowers _))

theorem conj_ui_of_eq (h4 : S.Sec4 F T₁) (hui : ui ∈ S.data.T) (D : S.Sec6 T₁ yi ki ui)
    (hvz : D.v * S.z = S.z * D.v) {n : X} (hn : n ∈ T₁)
    (hnt : n * S.t * n⁻¹ = D.v * S.t * D.v⁻¹) :
    n * ui * n⁻¹ = D.v * ui * D.v⁻¹ ∨ n * ui * n⁻¹ = S.z * (D.v * ui * D.v⁻¹) := by
  have hτ := inv_mul_mem_T h4 (v_mem_T₁ D) hn hnt.symm
  set τ := D.v⁻¹ * n with hτdef
  have hn' : n = D.v * τ := by rw [hτdef]; group
  rcases conj_eq_of_mem_T hτ hui with h | h
  · left
    rw [hn', show D.v * τ * ui * (D.v * τ)⁻¹ = D.v * (τ * ui * τ⁻¹) * D.v⁻¹ by group, h]
  · right
    rw [hn', show D.v * τ * ui * (D.v * τ)⁻¹ = D.v * (τ * ui * τ⁻¹) * D.v⁻¹ by group, h]
    calc D.v * (S.z * ui) * D.v⁻¹ = (D.v * S.z) * ui * D.v⁻¹ := by group
      _ = S.z * (D.v * ui * D.v⁻¹) := by rw [hvz]; group

theorem u_eq_of_act (h4 : S.Sec4 F T₁) (hk : IsK (S := S) ki) (hui : ui ∈ S.data.T)
    (D : S.Sec6 T₁ yi ki ui) (hvt : D.v * S.t * D.v⁻¹ = S.t * ki) (hvz : D.v * S.z = S.z * D.v)
    {n : X} (hn : n ∈ T₁) (hnt : n * S.t * n⁻¹ = S.t * ki)
    (hnu : n * ui * n⁻¹ = ui ∨ n * ui * n⁻¹ = S.z * ui) : D.u = ui := by
  rcases D.u_eq with h | h
  · exact h
  exfalso
  have hkT : ki ∈ S.data.T := S.B_le_T hk.mem
  have hvu : D.v * ui * D.v⁻¹ = ki * ui := by
    have hc := u_comm_v D
    rw [h] at hc
    have h1 : D.v * (S.t * ui) * D.v⁻¹ = S.t * ui := by rw [← hc]; group
    have h2 : D.v * (S.t * ui) * D.v⁻¹ = (D.v * S.t * D.v⁻¹) * (D.v * ui * D.v⁻¹) := by group
    rw [h2, hvt] at h1
    have hki : ki * ki = 1 := by rw [← pow_two, hk.sq]
    calc D.v * ui * D.v⁻¹ = (S.t * ki)⁻¹ * (S.t * ki * (D.v * ui * D.v⁻¹)) := by group
      _ = ki * ui := by
        rw [h1, mul_inv_rev, show ki⁻¹ = ki by rw [inv_eq_iff_mul_eq_one, hki], mul_assoc,
          inv_mul_cancel_left]
  rcases conj_ui_of_eq h4 hui D hvz hn (hnt.trans hvt.symm) with h3 | h3 <;>
    rw [h3, hvu] at hnu <;>
    rcases hnu with h4' | h4'
  · exact (ki_not_mem_z hk).1 (mul_eq_right.mp h4')
  · exact (ki_not_mem_z hk).2 (mul_right_cancel h4')
  · apply (ki_not_mem_z hk).2
    have := mul_right_cancel
      (show S.z * ki * ui = 1 * ui by rw [one_mul, ← mul_assoc] at *; exact h4')
    calc ki = S.z⁻¹ * (S.z * ki) := by group
      _ = S.z := by rw [this, mul_one, inv_eq_iff_mul_eq_one, ← pow_two, z_sq]
  · apply (ki_not_mem_z hk).1
    have := mul_right_cancel (show S.z * ki * ui = S.z * ui by rw [← mul_assoc] at h4'; exact h4')
    exact mul_left_cancel (this.trans (mul_one S.z).symm)

theorem u_eq_t_mul_of_act (h4 : S.Sec4 F T₁) (hk : IsK (S := S) ki) (hui : ui ∈ S.data.T)
    (D : S.Sec6 T₁ yi ki ui) (hvt : D.v * S.t * D.v⁻¹ = S.t * ki) (hvz : D.v * S.z = S.z * D.v)
    {n : X} (hn : n ∈ T₁) (hnt : n * S.t * n⁻¹ = S.t * ki)
    (hnu : n * ui * n⁻¹ = ki * ui ∨ n * ui * n⁻¹ = S.z * (ki * ui)) : D.u = S.t * ui := by
  rcases D.u_eq with h | h
  · exfalso
    have hvu : D.v * ui * D.v⁻¹ = ui := by
      have hc := u_comm_v D
      rw [h] at hc
      rw [← hc]; group
    rcases conj_ui_of_eq h4 hui D hvz hn (hnt.trans hvt.symm) with h3 | h3 <;>
      rw [h3, hvu] at hnu <;>
      rcases hnu with h4' | h4'
    · exact (ki_not_mem_z hk).1 (mul_eq_right.mp h4'.symm)
    · apply (ki_not_mem_z hk).2
      have h5 := h4'.symm
      rw [← mul_assoc] at h5
      have h6 : S.z * ki = 1 := mul_right_cancel (h5.trans (one_mul ui).symm)
      calc ki = S.z * (S.z * ki) := by rw [← mul_assoc, ← pow_two, z_sq, one_mul]
        _ = S.z := by rw [h6, mul_one]
    · apply (ki_not_mem_z hk).2
      exact mul_right_cancel h4'.symm
    · apply (ki_not_mem_z hk).1
      have h5 := h4'.symm
      rw [← mul_assoc] at h5
      exact mul_left_cancel ((mul_right_cancel h5).trans (mul_one S.z).symm)
  · exact h

theorem z_mem_E0 (yi ki : X) : S.z ∈ S.E0 yi ki := subset_closure (by simp)

theorem yi_mem_E0 (yi ki : X) : yi ∈ S.E0 yi ki := subset_closure (by simp)

theorem ki_mem_E0 (yi ki : X) : ki ∈ S.E0 yi ki := subset_closure (by simp)

theorem v_conj_E0 (D : S.Sec6 T₁ yi ki ui) {e : X} (he : e ∈ S.E0 yi ki) :
    D.v * e * D.v⁻¹ = e := by
  have h := D.act_holds
  cases hact : D.act <;> rw [hact] at h
  · exact (h.1 e he).1
  · exact h.1 e he

theorem v_conj_t (D : S.Sec6 T₁ yi ki ui) : D.v * S.t * D.v⁻¹ = S.t * ki := by
  have h := D.act_holds
  cases hact : D.act <;> rw [hact] at h
  · exact h.2.1
  · exact h.2.1

theorem v_comm_z (D : S.Sec6 T₁ yi ki ui) : D.v * S.z = S.z * D.v := by
  have h := v_conj_E0 D (z_mem_E0 yi ki)
  calc D.v * S.z = D.v * S.z * D.v⁻¹ * D.v := by group
    _ = S.z * D.v := by rw [h]

theorem z_mem_Q0 (yi ki w₁ w₂ : X) : S.z ∈ S.Q0 yi ki w₁ w₂ :=
  mem_sup_left (mem_sup_left (z_mem_E0 yi ki))

theorem w₂_mem_Q0 (yi ki w₁ w₂ : X) : w₂ ∈ S.Q0 yi ki w₁ w₂ := mem_sup_right (mem_zpowers _)

theorem w₁_mem_Q0 (yi ki w₁ w₂ : X) : w₁ ∈ S.Q0 yi ki w₁ w₂ :=
  mem_sup_left (mem_sup_right (mem_zpowers _))

theorem act_eq_one_of_comm (hk : IsK (S := S) ki) (D : S.Sec6 T₁ yi ki ui)
    (hab : ∀ a ∈ S.Q0 yi ki D.w₁ D.w₂, ∀ b ∈ S.Q0 yi ki D.w₁ D.w₂, a * b = b * a) :
    D.act = .one := by
  cases hact : D.act
  · rfl
  · exfalso
    have h := D.act_holds
    rw [hact] at h
    have hz := h.2.2.2.2.2.2.1
    have hc := hab _ (w₂_mem_Q0 yi ki D.w₁ D.w₂) _ (z_mem_Q0 yi ki D.w₁ D.w₂)
    rw [hc, mul_inv_cancel_right] at hz
    exact hk.ne_one (mul_eq_left.mp hz.symm)

theorem comm_of_q0 (D : S.Sec6 T₁ yi ki ui) (h : D.q0 = .elem ∨ D.q0 = .homocyclic) :
    ∀ a ∈ S.Q0 yi ki D.w₁ D.w₂, ∀ b ∈ S.Q0 yi ki D.w₁ D.w₂, a * b = b * a := by
  have hq := D.q0_holds
  rcases h with h | h <;> rw [h] at hq
  · exact hq.1
  · exact hq.2.2.1

theorem act_two_of_q0 (D : S.Sec6 T₁ yi ki ui) (h : D.q0 = .extraspecial) :
    S.ActHolds yi ki D.v D.w₁ D.w₂ .two := by
  have hq := D.q0_holds
  rw [h] at hq
  exact hq.2.2.1

theorem xy_mem_T (F : S.Frame) : F.xF * F.yF ∈ S.data.T := (xyF_mem_R F).1

theorem zy_mem_T (F : S.Frame) : S.z * F.yF ∈ S.data.T := mul_mem z_mem_T (yF_mem_T F)

theorem ki_comm_z (hk : IsK (S := S) ki) : ki * S.z = S.z * ki := commute_of_mem_B hk.mem z_mem_B

theorem vw_conj (hk : IsK (S := S) ki) (D : S.Sec6 T₁ yi ki ui) (hact : D.act = .one) :
    (D.v * D.w₁) * S.t * (D.v * D.w₁)⁻¹ = S.t * (S.z * ki) ∧
      ∀ e ∈ S.E0 yi ki, (D.v * D.w₁) * e * (D.v * D.w₁)⁻¹ = e := by
  have h := D.act_holds
  rw [hact] at h
  refine ⟨?_, fun e he => ?_⟩
  · calc (D.v * D.w₁) * S.t * (D.v * D.w₁)⁻¹ = D.v * (D.w₁ * S.t * D.w₁⁻¹) * D.v⁻¹ := by group
      _ = (D.v * S.t * D.v⁻¹) * (D.v * S.z * D.v⁻¹) := by rw [h.2.2.1]; group
      _ = S.t * (S.z * ki) := by
        rw [h.2.1, v_conj_E0 D (z_mem_E0 yi ki), mul_assoc, ki_comm_z hk]
  · calc (D.v * D.w₁) * e * (D.v * D.w₁)⁻¹ = D.v * (D.w₁ * e * D.w₁⁻¹) * D.v⁻¹ := by group
      _ = e := by rw [(h.1 e he).2.1, (h.1 e he).1]

theorem zy_mem_E0 (F : S.Frame) : S.z * F.yF ∈ S.E0 F.yF F.kF :=
  mul_mem (z_mem_E0 _ _) (yi_mem_E0 _ _)

theorem xy_mem_E0 (F : S.Frame) : F.xF * F.yF ∈ S.E0 (F.xF * F.yF) (S.z * F.kF) :=
  yi_mem_E0 _ _

theorem u₂_eq_of_one (h4 : S.Sec4 F T₁) (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
    (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)) (hact : D₁.act = .one) :
    D₂.u = S.z * F.yF := by
  obtain ⟨h1, h2⟩ := vw_conj (isK_kF F) D₁ hact
  exact u_eq_of_act h4 (isK_zkF F) (zy_mem_T F) D₂ (v_conj_t D₂) (v_comm_z D₂)
    (mul_mem (v_mem_T₁ D₁) (w₁_mem_T₁ D₁)) h1 (Or.inl (h2 _ (zy_mem_E0 F)))

theorem u₁_eq_of_one (h4 : S.Sec4 F T₁) (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
    (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)) (hact : D₂.act = .one) :
    D₁.u = F.xF * F.yF := by
  obtain ⟨h1, h2⟩ := vw_conj (isK_zkF F) D₂ hact
  refine u_eq_of_act h4 (isK_kF F) (xy_mem_T F) D₁ (v_conj_t D₁) (v_comm_z D₁)
    (mul_mem (v_mem_T₁ D₂) (w₁_mem_T₁ D₂)) ?_ (Or.inl (h2 _ (xy_mem_E0 F)))
  rw [h1, ← mul_assoc S.z, ← pow_two, z_sq, one_mul]

theorem u₂_eq_of_two (h4 : S.Sec4 F T₁) (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
    (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF))
    (h : S.ActHolds F.yF F.kF D₁.v D₁.w₁ D₁.w₂ .two) : D₂.u = S.t * (S.z * F.yF) := by
  obtain ⟨-, -, hw₁t, -, hw₁z, -, -, hw₁y, -, -⟩ := h
  refine u_eq_t_mul_of_act h4 (isK_zkF F) (zy_mem_T F) D₂ (v_conj_t D₂) (v_comm_z D₂)
    (w₁_mem_T₁ D₁) (by rw [hw₁t, mul_assoc]) (Or.inr ?_)
  have h1 : S.z * F.kF = F.kF * S.z := (ki_comm_z (isK_kF F)).symm
  have h2 : F.kF * F.yF = F.yF * F.kF := kF_comm F (yF_mem_T F)
  calc D₁.w₁ * (S.z * F.yF) * D₁.w₁⁻¹ = (D₁.w₁ * S.z * D₁.w₁⁻¹) * (D₁.w₁ * F.yF * D₁.w₁⁻¹) := by
        group
    _ = S.z * (F.kF * F.yF) := by rw [hw₁z, hw₁y, h2]
    _ = S.z * (S.z * F.kF * (S.z * F.yF)) := by
      congr 1
      calc F.kF * F.yF = F.kF * (S.z * S.z) * F.yF := by rw [← pow_two, z_sq, mul_one]
        _ = S.z * F.kF * (S.z * F.yF) := by rw [h1]; group

theorem u₁_eq_of_two (h4 : S.Sec4 F T₁) (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
    (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF))
    (h : S.ActHolds (F.xF * F.yF) (S.z * F.kF) D₂.v D₂.w₁ D₂.w₂ .two) :
    D₁.u = S.t * (F.xF * F.yF) := by
  obtain ⟨-, -, hw₁t, -, hw₁z, -, -, hw₁y, -, -⟩ := h
  refine u_eq_t_mul_of_act h4 (isK_kF F) (xy_mem_T F) D₁ (v_conj_t D₁) (v_comm_z D₁)
    (w₁_mem_T₁ D₂) ?_ (Or.inr ?_)
  · rw [hw₁t, mul_assoc, ← mul_assoc S.z S.z, ← pow_two, z_sq, one_mul]
  · rw [hw₁y, ← S.central_of_mem_B (mul_mem z_mem_B (kF_mem_B F)) (xy_mem_T F), mul_assoc]

theorem xyF_conj_yF (F : S.Frame) :
    (F.xF * F.yF) * F.yF * (F.xF * F.yF)⁻¹ = S.z * F.yF := by
  rw [show (F.xF * F.yF) * F.yF * (F.xF * F.yF)⁻¹ = F.xF * (F.yF * F.yF * F.yF⁻¹) * F.xF⁻¹ by
    group, mul_inv_cancel_right, xF_conj_yF]

theorem zyF_sq (F : S.Frame) : (S.z * F.yF) * (S.z * F.yF) = 1 := by
  rw [show S.z * F.yF * (S.z * F.yF) = S.z * (F.yF * S.z) * F.yF by group,
    ← S.central_of_mem_B z_mem_B (yF_mem_T F),
    show S.z * (S.z * F.yF) * F.yF = (S.z * S.z) * (F.yF * F.yF) by group, ← pow_two, ← pow_two,
    z_sq, F.yF_sq, one_mul]

theorem zyF_conj_xyF (F : S.Frame) :
    (S.z * F.yF) * (F.xF * F.yF) * (S.z * F.yF)⁻¹ = S.z * (F.xF * F.yF) := by
  have hz : S.z⁻¹ = S.z := by rw [inv_eq_iff_mul_eq_one, ← pow_two, z_sq]
  calc (S.z * F.yF) * (F.xF * F.yF) * (S.z * F.yF)⁻¹ =
      S.z * (F.yF * F.xF * F.yF⁻¹) * F.yF * S.z⁻¹ := by group
    _ = (S.z * S.z) * (F.xF * F.yF) * S.z⁻¹ := by rw [F.yF_inv, xF_inv F]; group
    _ = (F.xF * F.yF) * S.z⁻¹ := by rw [← pow_two, z_sq, one_mul]
    _ = S.z⁻¹ * (F.xF * F.yF) := by rw [← S.central_of_mem_B (inv_mem z_mem_B) (xy_mem_T F)]
    _ = S.z * (F.xF * F.yF) := by rw [hz]

theorem w₂_mem_S₁_of (D : S.Sec6 T₁ yi ki ui) : D.w₂ ∈ D.S₁ := by
  rw [D.S₁_eq]; exact mem_sup_left (mem_sup_right (mem_zpowers _))

theorem u_mem_S₁_of (D : S.Sec6 T₁ yi ki ui) : D.u ∈ D.S₁ := by
  rw [D.S₁_eq]; exact mem_sup_right (mem_zpowers _)

theorem u_conj_w₁_of_one (hk : IsK (S := S) ki) (hyi : IsRefl F yi) (D : S.Sec6 T₁ yi ki ui)
    (hact : D.act = .one) (hq : D.q0 = .elem ∨ D.q0 = .homocyclic) (hu2 : D.u * D.u = 1)
    (huT : D.u ∈ S.data.T) (huy : D.u * yi * D.u⁻¹ = S.z * yi) :
    ∃ c ∈ zpowers S.z, D.u * D.w₁ * D.u⁻¹ = c * D.w₁ := by
  have hA := D.act_holds
  rw [hact] at hA
  obtain ⟨hE0, -, hw₁t, hw₂t⟩ := hA
  have hE := hyi.elemAbelianTwo_E
  have hw₁sq : D.w₁ * D.w₁ ∈ zpowers S.z := by
    have hq0 := D.q0_holds
    rcases hq with h | h <;> rw [h] at hq0
    · rw [← pow_two, hq0.2.1 _ (w₁_mem_Q0 yi ki D.w₁ D.w₂)]; exact one_mem _
    · rw [← pow_two, hq0.1]; exact mem_zpowers _
  have hw₁E0 : ∀ e ∈ S.E0 yi ki, D.w₁ * e * D.w₁⁻¹ = e := fun e he => (hE0 e he).2.1
  have hN : D.w₁ ∈ normalizer (S.E0 yi ki : Set X) := by
    rw [mem_normalizer_iff]
    intro e
    refine ⟨fun he => by rw [hw₁E0 e he]; exact he, fun he => ?_⟩
    have h1 := hw₁E0 _ he
    have : e = D.w₁ * e * D.w₁⁻¹ := by
      calc e = D.w₁⁻¹ * (D.w₁ * e * D.w₁⁻¹) * D.w₁ := by group
        _ = D.w₁⁻¹ * (D.w₁ * (D.w₁ * e * D.w₁⁻¹) * D.w₁⁻¹) * D.w₁ := by rw [h1]
        _ = D.w₁ * e * D.w₁⁻¹ := by group
    rw [this]; exact he
  have hw₁2 : D.w₁ ^ 2 ∈ S.E0 yi ki := by
    rw [pow_two]
    rcases eq_one_or_eq_of_mem_zpowers z_sq hw₁sq with h | h <;> rw [h]
    · exact one_mem _
    · exact z_mem_E0 yi ki
  have hc : D.w₂ * D.u * D.w₂⁻¹ * D.u⁻¹ ∈ S.E0 yi ki ⊔ zpowers D.w₁ :=
    D.S₁_commutator_mem _ (w₂_mem_S₁_of D) _ (u_mem_S₁_of D)
  have hut : D.u * S.t * D.u⁻¹ = S.t := by
    rw [S.data.commute_t huT, mul_inv_cancel_right]
  have htyi : S.t * yi ∈ S.E yi := mul_mem (t_mem_E yi) (mem_E_self yi)
  rcases mem_or_of_mem_sup_zpowers hN hw₁2 hc with h | h
  ·
    exfalso
    set c := D.w₂ * D.u * D.w₂⁻¹ * D.u⁻¹ with hcdef
    have hwu : D.w₂ * D.u * D.w₂⁻¹ = c * D.u := by rw [hcdef]; group
    have hcE := E0_le_E hk yi h
    have h1 : (D.w₂ * D.u * D.w₂⁻¹) * (D.w₂ * S.t * D.w₂⁻¹) * (D.w₂ * D.u * D.w₂⁻¹)⁻¹ =
        D.w₂ * S.t * D.w₂⁻¹ := by
      rw [show (D.w₂ * D.u * D.w₂⁻¹) * (D.w₂ * S.t * D.w₂⁻¹) * (D.w₂ * D.u * D.w₂⁻¹)⁻¹ =
        D.w₂ * (D.u * S.t * D.u⁻¹) * D.w₂⁻¹ by group, hut]
    rw [hwu, hw₂t] at h1
    have h2 : c * D.u * (S.t * yi) * (c * D.u)⁻¹ = S.z * (S.t * yi) := by
      rw [show c * D.u * (S.t * yi) * (c * D.u)⁻¹ = c * ((D.u * S.t * D.u⁻¹) *
        (D.u * yi * D.u⁻¹)) * c⁻¹ by group, hut, huy,
        hE.comm _ hcE _ (mul_mem (t_mem_E yi) (mul_mem (z_mem_E yi) (mem_E_self yi))),
        mul_inv_cancel_right, ← mul_assoc, ← S.data.commute_t z_mem_T, mul_assoc]
    rw [h2] at h1
    exact S.z_ne_one (mul_eq_right.mp h1)
  · set e := D.w₂ * D.u * D.w₂⁻¹ * D.u⁻¹ * D.w₁⁻¹ with hedef
    have hwu : D.w₂ * D.u * D.w₂⁻¹ = e * D.w₁ * D.u := by rw [hedef]; group
    have heE : e ∈ S.E yi := E0_le_E hk yi h
    have hsq : e * D.w₁ * D.u * (e * D.w₁ * D.u) = 1 := by
      rw [← hwu, show D.w₂ * D.u * D.w₂⁻¹ * (D.w₂ * D.u * D.w₂⁻¹) = D.w₂ * (D.u * D.u) * D.w₂⁻¹
        by group, hu2, mul_one, mul_inv_cancel]
    have hue : D.u * e * D.u⁻¹ * e ∈ zpowers S.z ∧ D.u * e * D.u⁻¹ * e = e * (D.u * e * D.u⁻¹) := by
      rw [E0_eq] at h
      rcases mem_or_of_mem_sup (elemAbelianTwo_zk hk) hyi.sq
          (fun _ hb => hyi.comm_B (zk_le_B hk hb)) h with h' | h'
      · have hB := zk_le_B hk h'
        rw [← S.central_of_mem_B hB huT, mul_inv_cancel_right]
        exact ⟨by rw [← pow_two, S.sq_of_mem_B hB]; exact one_mem _, rfl⟩
      · set c := e * yi with hcd
        have hec : e = c * yi := by
          rw [hcd, mul_assoc, ← pow_two, hyi.sq, mul_one]
        have hB := zk_le_B hk h'
        have hcE := B_le_E yi hB
        rw [hec, show D.u * (c * yi) * D.u⁻¹ = (D.u * c * D.u⁻¹) * (D.u * yi * D.u⁻¹) by group,
          ← S.central_of_mem_B hB huT, mul_inv_cancel_right, huy]
        have hzE := z_mem_E (S := S) yi
        have hyE := mem_E_self (S := S) yi
        obtain ⟨φ, e0, e1, e2, e3⟩ := exists_evHom4 (hE.comm _ hcE _ hzE) (hE.comm _ hcE _ hyE)
          (hE.comm _ hcE _ (t_mem_E yi)) (hE.comm _ hzE _ hyE) (hE.comm _ hzE _ (t_mem_E yi))
          (hE.comm _ hyE _ (t_mem_E yi)) (by rw [← pow_two]; exact S.sq_of_mem_B hB)
          (by rw [← pow_two]; exact z_sq) (by rw [← pow_two]; exact hyi.sq)
          (by rw [← pow_two]; exact S.t_sq)
        refine ⟨?_, by elem_eq φ e0 e1 e2 e3⟩
        have : c * (S.z * yi) * (c * yi) = S.z := by elem_eq φ e0 e1 e2 e3
        rw [this]; exact mem_zpowers _
    have hw₁e : D.w₁ * e = e * D.w₁ := by
      calc D.w₁ * e = (D.w₁ * e * D.w₁⁻¹) * D.w₁ := by group
        _ = e * D.w₁ := by rw [hw₁E0 e h]
    have hu' : D.u⁻¹ = D.u := inv_eq_of_mul_eq_one_right hu2
    have h1 : D.u * (e * D.w₁) * D.u⁻¹ = (e * D.w₁)⁻¹ := by
      rw [hu']
      calc D.u * (e * D.w₁) * D.u = (e * D.w₁)⁻¹ * ((e * D.w₁ * D.u) * (e * D.w₁ * D.u)) := by
            group
        _ = (e * D.w₁)⁻¹ := by rw [hsq, mul_one]
    refine ⟨D.u * D.w₁ * D.u⁻¹ * D.w₁⁻¹, ?_, by group⟩
    have h2 : D.u * D.w₁ * D.u⁻¹ * D.w₁⁻¹ =
        (D.u * e * D.u⁻¹)⁻¹ * (D.u * (e * D.w₁) * D.u⁻¹) * D.w₁⁻¹ := by group
    have h3 : (D.u * e * D.u⁻¹)⁻¹ * (e * D.w₁)⁻¹ * D.w₁⁻¹ =
        (D.u * e * D.u⁻¹ * e)⁻¹ * (D.w₁ * D.w₁)⁻¹ := by
      rw [hue.2, mul_inv_rev e D.w₁, show D.w₁⁻¹ * e⁻¹ = e⁻¹ * D.w₁⁻¹ by
        rw [← mul_inv_rev, ← hw₁e, mul_inv_rev]]
      group
    rw [h2, h1, h3]
    exact mul_mem (inv_mem hue.1) (inv_mem hw₁sq)

theorem mixed_false (h4 : S.Sec4 F T₁) (hk : IsK (S := S) ki) (hyi : IsRefl F yi)
    (D : S.Sec6 T₁ yi ki ui) (hact : D.act = .one) (hq : D.q0 = .elem ∨ D.q0 = .homocyclic)
    (huiT : ui ∈ S.data.T) (hui2 : ui * ui = 1) (huiy : ui * yi * ui⁻¹ = S.z * yi)
    (hu : D.u = S.t * ui) {n : X} (hn : n ∈ T₁) (hnt : n * S.t * n⁻¹ = S.t * (S.z * ki))
    (hnu : n * ui * n⁻¹ = ui) : False := by
  have htui : S.t * ui = ui * S.t := (S.data.commute_t huiT).symm
  have huT : D.u ∈ S.data.T := by rw [hu]; exact mul_mem S.data.t_mem_T huiT
  have hu2 : D.u * D.u = 1 := by
    rw [hu, show S.t * ui * (S.t * ui) = S.t * (ui * S.t) * ui by group, ← htui,
      show S.t * (S.t * ui) * ui = (S.t * S.t) * (ui * ui) by group, ← pow_two, S.t_sq, hui2,
      one_mul]
  have huy : D.u * yi * D.u⁻¹ = S.z * yi := by
    rw [hu, show S.t * ui * yi * (S.t * ui)⁻¹ = S.t * (ui * yi * ui⁻¹) * S.t⁻¹ by group, huiy,
      S.data.commute_t (mul_mem z_mem_T hyi.mem_T) |>.symm, mul_inv_cancel_right]
  obtain ⟨c, hc, hcw⟩ := u_conj_w₁_of_one hk hyi D hact hq hu2 huT huy
  have hA := D.act_holds
  rw [hact] at hA
  have hw₁u : D.w₁ * D.u * D.w₁⁻¹ = c⁻¹ * D.u := by
    calc D.w₁ * D.u * D.w₁⁻¹ = c⁻¹ * (c * D.w₁) * D.u * D.w₁⁻¹ := by group
      _ = c⁻¹ * D.u := by rw [← hcw]; group
  have hct : c * S.t = S.t * c := by
    rcases eq_one_or_eq_of_mem_zpowers z_sq hc with rfl | rfl
    · group
    · exact (S.data.commute_t z_mem_T)
  have hw₁ui : D.w₁ * ui * D.w₁⁻¹ = (S.z⁻¹ * c⁻¹) * ui := by
    have h1 : D.w₁ * D.u * D.w₁⁻¹ = (D.w₁ * S.t * D.w₁⁻¹) * (D.w₁ * ui * D.w₁⁻¹) := by
      rw [hu]; group
    rw [hw₁u, hA.2.2.1] at h1
    calc D.w₁ * ui * D.w₁⁻¹ = (S.t * S.z)⁻¹ * (S.t * S.z * (D.w₁ * ui * D.w₁⁻¹)) := by group
      _ = (S.t * S.z)⁻¹ * (c⁻¹ * (S.t * ui)) := by rw [← h1, hu]
      _ = (S.z⁻¹ * c⁻¹) * ui := by
          have hct' : c⁻¹ * S.t = S.t * c⁻¹ := by
            calc c⁻¹ * S.t = c⁻¹ * (S.t * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * S.t) * c⁻¹ := by rw [hct]
              _ = S.t * c⁻¹ := by group
          rw [show c⁻¹ * (S.t * ui) = S.t * c⁻¹ * ui by rw [← mul_assoc, hct']]
          group
  have hvui : D.v * ui * D.v⁻¹ = ki * ui := by
    have hcv := u_comm_v D
    rw [hu] at hcv
    have h1 : D.v * (S.t * ui) * D.v⁻¹ = S.t * ui := by rw [← hcv]; group
    rw [show D.v * (S.t * ui) * D.v⁻¹ = (D.v * S.t * D.v⁻¹) * (D.v * ui * D.v⁻¹) by group,
      v_conj_t D] at h1
    calc D.v * ui * D.v⁻¹ = (S.t * ki)⁻¹ * (S.t * ki * (D.v * ui * D.v⁻¹)) := by group
      _ = ki * ui := by
          rw [h1, mul_inv_rev, show ki⁻¹ = ki by
            rw [inv_eq_iff_mul_eq_one, ← pow_two, hk.sq], mul_assoc, inv_mul_cancel_left]
  obtain ⟨hvwt, -⟩ := vw_conj hk D hact
  have hτ := inv_mul_mem_T h4 (mul_mem (v_mem_T₁ D) (w₁_mem_T₁ D)) hn (hvwt.trans hnt.symm)
  set τ := (D.v * D.w₁)⁻¹ * n with hτdef
  have hn' : n = D.v * D.w₁ * τ := by rw [hτdef]; group
  have hvz : ∀ d ∈ zpowers S.z, D.v * d * D.v⁻¹ = d := by
    intro d hd
    rcases eq_one_or_eq_of_mem_zpowers z_sq hd with rfl | rfl
    · group
    · exact v_conj_E0 D (z_mem_E0 yi ki)
  have hw₁z : ∀ d ∈ zpowers S.z, D.w₁ * d * D.w₁⁻¹ = d := by
    intro d hd
    rcases eq_one_or_eq_of_mem_zpowers z_sq hd with rfl | rfl
    · group
    · exact (hA.1 _ (z_mem_E0 yi ki)).2.1
  have hd : S.z⁻¹ * c⁻¹ ∈ zpowers S.z := mul_mem (inv_mem (mem_zpowers _)) (inv_mem hc)
  have key : ∀ a ∈ zpowers S.z, n * ui * n⁻¹ = (a * (S.z⁻¹ * c⁻¹)) * (ki * ui) →
      False := by
    intro a ha h
    rw [hnu] at h
    apply hk.not_mem
    have : ki = (a * (S.z⁻¹ * c⁻¹))⁻¹ := by
      have h1 : (a * (S.z⁻¹ * c⁻¹)) * ki = 1 := by
        calc (a * (S.z⁻¹ * c⁻¹)) * ki = ((a * (S.z⁻¹ * c⁻¹)) * (ki * ui)) * ui⁻¹ := by group
          _ = 1 := by rw [← h, mul_inv_cancel]
      exact eq_inv_of_mul_eq_one_right h1
    rw [this]
    exact mem_sup_left (inv_mem (mul_mem ha hd))
  rcases conj_eq_of_mem_T hτ huiT with h | h
  · apply key 1 (one_mem _)
    rw [hn', show D.v * D.w₁ * τ * ui * (D.v * D.w₁ * τ)⁻¹ =
      D.v * (D.w₁ * (τ * ui * τ⁻¹) * D.w₁⁻¹) * D.v⁻¹ by group, h, hw₁ui,
      show D.v * (S.z⁻¹ * c⁻¹ * ui) * D.v⁻¹ = (D.v * (S.z⁻¹ * c⁻¹) * D.v⁻¹) * (D.v * ui * D.v⁻¹)
        by group, hvz _ hd, hvui, one_mul]
  · apply key S.z (mem_zpowers _)
    rw [hn', show D.v * D.w₁ * τ * ui * (D.v * D.w₁ * τ)⁻¹ =
      D.v * (D.w₁ * (τ * ui * τ⁻¹) * D.w₁⁻¹) * D.v⁻¹ by group, h,
      show D.w₁ * (S.z * ui) * D.w₁⁻¹ = (D.w₁ * S.z * D.w₁⁻¹) * (D.w₁ * ui * D.w₁⁻¹) by group,
      hw₁z _ (mem_zpowers _), hw₁ui,
      show D.v * (S.z * (S.z⁻¹ * c⁻¹ * ui)) * D.v⁻¹ =
        (D.v * (S.z * (S.z⁻¹ * c⁻¹)) * D.v⁻¹) * (D.v * ui * D.v⁻¹) by group,
      hvz _ (mul_mem (mem_zpowers _) hd), hvui]

theorem split (h4 : S.Sec4 F T₁) (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
    (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF))
    (h1 : D₁.q0 = .elem ∨ D₁.q0 = .homocyclic ∨ D₁.q0 = .extraspecial)
    (h2 : D₂.q0 = .elem ∨ D₂.q0 = .homocyclic ∨ D₂.q0 = .extraspecial) :
    ((D₁.q0 = .elem ∨ D₁.q0 = .homocyclic) ∧ (D₂.q0 = .elem ∨ D₂.q0 = .homocyclic) ∧
        D₁.act = .one ∧ D₂.act = .one ∧ D₁.u = F.xF * F.yF ∧ D₂.u = S.z * F.yF) ∨
      (D₁.q0 = .extraspecial ∧ D₂.q0 = .extraspecial ∧ D₁.u = S.t * (F.xF * F.yF) ∧
        D₂.u = S.t * (S.z * F.yF)) := by
  have ht : ∀ a : X, S.t * a ≠ a := fun a h => S.t_ne_one (mul_eq_right.mp h)
  rcases (show (D₁.q0 = .elem ∨ D₁.q0 = .homocyclic) ∨ D₁.q0 = .extraspecial by tauto) with
    hq₁ | hq₁ <;>
    rcases (show (D₂.q0 = .elem ∨ D₂.q0 = .homocyclic) ∨ D₂.q0 = .extraspecial by tauto) with
    hq₂ | hq₂
  · have ha₁ := act_eq_one_of_comm (isK_kF F) D₁ (comm_of_q0 D₁ hq₁)
    have ha₂ := act_eq_one_of_comm (isK_zkF F) D₂ (comm_of_q0 D₂ hq₂)
    exact Or.inl ⟨hq₁, hq₂, ha₁, ha₂, u₁_eq_of_one h4 D₁ D₂ ha₂, u₂_eq_of_one h4 D₁ D₂ ha₁⟩
  · exfalso
    exact mixed_false h4 (isK_kF F) (isRefl_yF F) D₁
      (act_eq_one_of_comm (isK_kF F) D₁ (comm_of_q0 D₁ hq₁)) hq₁ (xy_mem_T F)
      (by rw [← pow_two]; exact xyF_sq F) (xyF_conj_yF F)
      (u₁_eq_of_two h4 D₁ D₂ (act_two_of_q0 D₂ hq₂)) (v_mem_T₁ D₂) (v_conj_t D₂)
      (v_conj_E0 D₂ (xy_mem_E0 F))
  · exfalso
    exact mixed_false h4 (isK_zkF F) (isRefl_xyF F) D₂
      (act_eq_one_of_comm (isK_zkF F) D₂ (comm_of_q0 D₂ hq₂)) hq₂ (zy_mem_T F)
      (zyF_sq F) (zyF_conj_xyF F)
      (u₂_eq_of_two h4 D₁ D₂ (act_two_of_q0 D₁ hq₁)) (v_mem_T₁ D₁)
      (by rw [v_conj_t D₁, ← mul_assoc S.z, ← pow_two, z_sq, one_mul])
      (v_conj_E0 D₁ (zy_mem_E0 F))
  · exact Or.inr ⟨hq₁, hq₂, u₁_eq_of_two h4 D₁ D₂ (act_two_of_q0 D₂ hq₂),
      u₂_eq_of_two h4 D₁ D₂ (act_two_of_q0 D₁ hq₁)⟩

end Sec8

end CFSG.ComponentClassification.HSFLit
