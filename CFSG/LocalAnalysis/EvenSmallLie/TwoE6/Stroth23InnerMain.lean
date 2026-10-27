module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerEdge
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.InvolutionsN1
import CFSG.Monster.B.GSide.TriangleHom1782
public import CFSG.LieType.Multipliers.U62Sylow

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open Subgroup CFSG.Monster CFSG.Monster.B CFSG.Monster.B.GSide CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Sp8

theorem isTriA_mul {j : Fin 2} {a k : Shat} (ha : IsTriA j a) (hk : k ∈ triKer j) :
    IsTriA j (a * k) :=
  show cvMul cv0 (a * k) = cv0 ∧ cvMul cw0 (a * k) = cu j ∧ cvMul (cu j) (a * k) = cw0 from
    ⟨by rw [cvMul_mul, ha.1, mem_vStab.1 hk.1.1], by rw [cvMul_mul, ha.2.1, mem_vStab.1 hk.2],
      by rw [cvMul_mul, ha.2.2, mem_vStab.1 hk.1.2]⟩

theorem isTriB_mul {j : Fin 2} {b k : Shat} (hb : IsTriB j b) (hk : k ∈ triKer j) :
    IsTriB j (b * k) :=
  show cvMul cv0 (b * k) = cw0 ∧ cvMul cw0 (b * k) = cv0 ∧ cvMul (cu j) (b * k) = cu j from
    ⟨by rw [cvMul_mul, hb.1, mem_vStab.1 hk.1.2], by rw [cvMul_mul, hb.2.1, mem_vStab.1 hk.1.1],
      by rw [cvMul_mul, hb.2.2, mem_vStab.1 hk.2]⟩

theorem pow_three_eq_one_of_labels {j : Fin 2} {x x' : CVert} (ha : IsTriA j (clabelS x))
    (hb : IsTriB j (clabelS x')) : (clabelS x * clabelS x') ^ 3 = 1 :=
  pow_three_eq_one_of_cycle cv0_ne_cw0 (cv0_ne_cu j) (by rw [cvMul_mul, ha.1, hb.1])
    (by rw [cvMul_mul, ha.2.1, hb.2.2]) (by rw [cvMul_mul, ha.2.2, hb.2.1])

theorem clabelS_mul_self (v : CVert) : clabelS v * clabelS v = 1 :=
  mul_eq_one_iff_eq_inv.2 (clabelS_inv v).symm

theorem false_of_localData {G : Type*} [Group G] {Φ : Shat → G} {g : G} {y : Shat}
    (hD : LocalData Φ g y) : False := by
  obtain ⟨x₀, hx₀, ha₀⟩ := exists_isTriA_adj
  obtain ⟨x₀', -, hb₀⟩ := exists_isTriB_adj
  obtain ⟨x₁, hx₁, ha₁⟩ := exists_isTriA_dist_three
  obtain ⟨x₁', -, hb₁⟩ := exists_isTriB_dist_three
  have h₀ := pow_three_eq_one_of_labels ha₀ hb₀
  have h₁ := pow_three_eq_one_of_labels ha₁ hb₁
  have ha₀H : clabelS x₀ ∈ HS := clabelS_mem_HS_of_adj hx₀
  have ha₁H : clabelS x₁ ∉ HS := clabelS_not_mem_HS_of_dist_three hx₁ (mem_vStab.2 ha₁.1)
  have hT := inv_mul_mem_HS ha₀ hb₀ ha₁ hb₁ h₀ h₁ (clabelS_mul_self x₀') ha₀H ha₁H
  have hyb₀ : y⁻¹ * clabelS x₀' ∈ HS := by
    by_contra hne
    obtain ⟨k, hk, hkH⟩ := exists_triKer_not_mem 0
    have hb' := isTriB_mul hb₀ hk
    have hyb' : y⁻¹ * (clabelS x₀' * k) ∈ HS := by
      rw [← mul_assoc]
      exact mul_mem_HS_of_not_mem (hD.inv_mul_mem_cEdgeFix hb₀).1 hk.1.1 hne hkH
    have hc := (pow_three_mem_HS_iff ha₀ hb₀ h₀ ha₀ hb').1
      (hD.pow_three_mem_HS ha₀ ha₀H hb' hyb')
    rw [inv_mul_cancel, inv_mul_cancel_left] at hc
    exact hkH (hc.1 (one_mem _))
  have hyb₁ : y⁻¹ * clabelS x₁' ∈ HS := by
    have e : y⁻¹ * clabelS x₁' = (y⁻¹ * clabelS x₀') * ((clabelS x₀')⁻¹ * clabelS x₁') := by
      group
    rw [e]
    exact mul_mem hyb₀ hT
  obtain ⟨k, hk, hkH⟩ := exists_triKer_not_mem 1
  have ha' := isTriA_mul ha₁ hk
  have ha'H : clabelS x₁ * k ∈ HS := mul_mem_HS_of_not_mem (mem_vStab.2 ha₁.1) hk.1.1 ha₁H hkH
  have hc := (pow_three_mem_HS_iff ha₁ hb₁ h₁ ha' hb₁).1 (hD.pow_three_mem_HS ha' ha'H hb₁ hyb₁)
  rw [inv_mul_cancel_left, inv_mul_cancel] at hc
  exact hkH (hc.2 (one_mem _))

theorem mul_mul_self_cancel {X : Type*} [Group X] {a b : X} (h : a * a = 1) :
    a * (a * b) = b := by
  rw [← mul_assoc, h, one_mul]

theorem mul_self_of_comm {X : Type*} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [hab]
    _ = 1 := by rw [← mul_assoc, ha, one_mul, hb]

@[expose] noncomputable def hsToComm : HS ≃* commutator (vStab cv0) where
  toFun x := ⟨⟨x, HS_le x.2⟩, (coe_mem_HS_iff ⟨x, HS_le x.2⟩).1 x.2⟩
  invFun y := ⟨y, (coe_mem_HS_iff y).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def hsEquiv : HS ≃* commutator Eam :=
  hsToComm.trans ((MulEquiv.subgroupMap vStabEam (commutator (vStab cv0))).trans
    (MulEquiv.subgroupCongr (map_commutator_of_mulEquiv vStabEam)))

theorem hsEquiv_cv0 : hsEquiv ⟨clabelS cv0, clabelS_cv0_mem_HS⟩ = cD :=
  Subtype.ext (Subtype.ext coe_lamV0)

theorem xhatS_mem_HS : clabelS cv0 * clabelS cw0 ∈ HS :=
  mul_mem clabelS_cv0_mem_HS clabelS_cw0_mem_HS

theorem hsEquiv_xhat : hsEquiv ⟨clabelS cv0 * clabelS cw0, xhatS_mem_HS⟩ = xD :=
  Subtype.ext (Subtype.ext (congrArg (fun p : P1 => (p : Dfull)) edgeFixEquivP1_lamV0_mul_lamW0))

section Phi

variable {G : Type*} [Group G] {L : Subgroup G}

open Classical in
@[expose] noncomputable def phiOf (ι : L ≃* commutator Eam) (x : Shat) : G :=
  if h : x ∈ HS then ((ι.symm (hsEquiv ⟨x, h⟩) : L) : G) else 1

theorem phiOf_of_mem (ι : L ≃* commutator Eam) {x : Shat} (h : x ∈ HS) :
    phiOf ι x = ((ι.symm (hsEquiv ⟨x, h⟩) : L) : G) :=
  dite_eq_left h

theorem phiOf_cv0 (ι : L ≃* commutator Eam) : phiOf ι (clabelS cv0) = dOf ι :=
  (phiOf_of_mem ι clabelS_cv0_mem_HS).trans
    (congrArg (fun z => ((ι.symm z : L) : G)) hsEquiv_cv0)

theorem phiOf_xhat (ι : L ≃* commutator Eam) :
    phiOf ι (clabelS cv0 * clabelS cw0) = zOf ι :=
  (phiOf_of_mem ι xhatS_mem_HS).trans (congrArg (fun z => ((ι.symm z : L) : G)) hsEquiv_xhat)

theorem phiOf_mul (ι : L ≃* commutator Eam) {x x' : Shat} (hx : x ∈ HS) (hx' : x' ∈ HS) :
    phiOf ι (x * x') = phiOf ι x * phiOf ι x' := by
  have e0 : phiOf ι (x * x') = ((ι.symm (hsEquiv ⟨x * x', mul_mem hx hx'⟩) : L) : G) :=
    phiOf_of_mem ι _
  have e1 : phiOf ι x = ((ι.symm (hsEquiv ⟨x, hx⟩) : L) : G) := phiOf_of_mem ι hx
  have e2 : phiOf ι x' = ((ι.symm (hsEquiv ⟨x', hx'⟩) : L) : G) := phiOf_of_mem ι hx'
  have e3 : (⟨x * x', mul_mem hx hx'⟩ : HS) = ⟨x, hx⟩ * ⟨x', hx'⟩ := rfl
  have e4 := map_mul hsEquiv ⟨x, hx⟩ ⟨x', hx'⟩
  have e5 := map_mul ι.symm (hsEquiv ⟨x, hx⟩) (hsEquiv ⟨x', hx'⟩)
  have e6 : ((ι.symm (hsEquiv ⟨x * x', mul_mem hx hx'⟩) : L) : G) =
      ((ι.symm (hsEquiv ⟨x, hx⟩) * ι.symm (hsEquiv ⟨x', hx'⟩) : L) : G) :=
    congrArg Subtype.val ((congrArg (fun z => ι.symm (hsEquiv z)) e3).trans
      ((congrArg ι.symm e4).trans e5))
  exact e0.trans (e6.trans (congrArg₂ (· * ·) e1.symm e2.symm))

theorem phiData_phiOf [Finite G] (hL : CFSG.Open.standardComponentIsStandard L)
    (ι : L ≃* commutator Eam) (hN : ∀ x ∈ normalizer (L : Set G), x ∈ L) :
    PhiData (phiOf ι) where
  mul _ hx _ hx' := phiOf_mul ι hx hx'
  inj x hx x' hx' h := congrArg Subtype.val (hsEquiv.injective (ι.symm.injective
    (Subtype.ext ((phiOf_of_mem ι hx).symm.trans (h.trans (phiOf_of_mem ι hx'))))))
  cent x hx := by
    have hxN : x ∈ normalizer (L : Set G) := by
      rw [← centralizer_dOf hL ι]
      exact mem_centralizer_singleton_iff.2 ((congrArg (Commute x) (phiOf_cv0 ι)).mp hx).eq
    have hxL := hN x hxN
    exact ⟨(hsEquiv.symm (ι ⟨x, hxL⟩) : Shat), (hsEquiv.symm (ι ⟨x, hxL⟩)).2,
      (phiOf_of_mem ι (hsEquiv.symm (ι ⟨x, hxL⟩)).2).trans (congrArg Subtype.val
        ((congrArg ι.symm (hsEquiv.apply_symm_apply (ι ⟨x, hxL⟩))).trans
          (ι.symm_apply_apply ⟨x, hxL⟩)))⟩

end Phi

theorem phiOf_cw0 {G : Type*} [Group G] {L : Subgroup G} [Finite G]
    (hL : CFSG.Open.standardComponentIsStandard L) (ι : L ≃* commutator Eam)
    (hN : ∀ x ∈ normalizer (L : Set G), x ∈ L) :
    phiOf ι (clabelS cw0) = dOf ι * zOf ι ∧ zOf ι * zOf ι = 1 := by
  have hΦ := phiData_phiOf hL ι hN
  have e1 : clabelS cv0 * (clabelS cv0 * clabelS cw0) = clabelS cw0 :=
    mul_mul_self_cancel (clabelS_mul_self cv0)
  have hcomm : clabelS cv0 * clabelS cw0 = clabelS cw0 * clabelS cv0 :=
    congrArg Subtype.val lamV0_mul_comm
  have e2 : clabelS cv0 * clabelS cw0 * (clabelS cv0 * clabelS cw0) = 1 :=
    mul_self_of_comm (clabelS_mul_self cv0) (clabelS_mul_self cw0) hcomm
  refine ⟨(congrArg (phiOf ι) e1).symm.trans ((hΦ.mul _ clabelS_cv0_mem_HS _ xhatS_mem_HS).trans
    (congrArg₂ (· * ·) (phiOf_cv0 ι) (phiOf_xhat ι))), ?_⟩
  exact (congrArg₂ (· * ·) (phiOf_xhat ι) (phiOf_xhat ι)).symm.trans
    ((hΦ.mul _ xhatS_mem_HS _ xhatS_mem_HS).symm.trans ((congrArg (phiOf ι) e2).trans hΦ.map_one))

theorem stroth23Inner : Stroth23Inner := by
  intro G _ _ L hset hZ ι
  by_contra hcon
  have hN : ∀ x ∈ normalizer (L : Set G), x ∈ L := fun x hx => by
    by_contra hxL
    exact hcon ⟨x, hx, hxL⟩
  have hΦ := phiData_phiOf hset.standard ι hN
  obtain ⟨hw0, hzz⟩ := phiOf_cw0 hset.standard ι hN
  obtain ⟨-, g, -, hg1, hg2⟩ := stroth22 G L hset hZ ι
  have hv : g * phiOf ι (clabelS cv0) * g⁻¹ = phiOf ι (clabelS cw0) :=
    (congrArg (fun t => g * t * g⁻¹) (phiOf_cv0 ι)).trans (hg1.trans hw0.symm)
  have hw : g * phiOf ι (clabelS cw0) * g⁻¹ = phiOf ι (clabelS cv0) := by
    refine (congrArg (fun t => g * t * g⁻¹) hw0).trans (Eq.trans ?_ (phiOf_cv0 ι).symm)
    calc g * (dOf ι * zOf ι) * g⁻¹ = g * dOf ι * g⁻¹ * (g * zOf ι * g⁻¹) := by group
      _ = dOf ι * zOf ι * zOf ι := by rw [hg1, hg2]
      _ = dOf ι := by rw [mul_assoc, hzz, mul_one]
  obtain ⟨y, hD⟩ := hΦ.exists_localData hv hw
  exact false_of_localData hD

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
