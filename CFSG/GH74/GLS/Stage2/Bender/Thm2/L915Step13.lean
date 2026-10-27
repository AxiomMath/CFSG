module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der613
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Steps

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace L915

section L613

theorem step9_13_of (h94 : Prop9_4) (h916 : Lemma9_16) (h611 : Step9_11) (h612 : Step9_12)
    (h911 : Prop9_11c) (hplane : OddNoncyclicPlane) : Step9_13 := by
  intro G _ _ z k S M p hC Q X hmin
  have hp := hC.prime
  have hp2 := hC.odd
  have : Fact p.Prime := ⟨hp⟩
  have hz2 : z * z = 1 := hC.z_mul_z
  have hPp : IsPGroup p ↥(Op p M) := hC.P_pgroup
  have hQP : Q ≤ Op p M := hmin.Q_mem.1
  have hQp : IsPGroup p ↥Q := hPp.to_le hQP
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op' p M) hmin.Q_mem
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hexp : ∀ x ∈ Q, x ^ p = 1 := hmin.Q_mem.2.2.1
  have hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := hmin.Q_mem.2.2.2.1
  have hXQ : X ≤ Q := hmin.X_le
  obtain ⟨⟨hXcard, hXinv⟩, -, -, -, he, -⟩ := h611 G z k S M p hC Q X hmin
  have hE : ExtraG p Q := extraG_of_isExtraspecial (h612 G z k S M p hC Q X hmin)
  have hRQ : ⁅Q, zpowers z⁆ ≤ Q := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzQ)
  have hR0 : ⁅Q, zpowers z⁆ ≠ ⊥ := fun h =>
    hmin.Q_mem.2.2.2.2.2 (commutator_zpowers_eq_bot_iff.mp h)
  have hRc : ⁅⁅Q, zpowers z⁆, zpowers z⁆ = ⁅Q, zpowers z⁆ :=
    commutator_zpowers_idem hC.orderOf_z hp hp2 hQp hzQ
  have hRN : NN z p (Op p M) ⁅Q, zpowers z⁆ := nn_commutator_QP h94 hC hmin.Q_mem
  by_contra hne
  obtain ⟨y, hyQ, hyz, hyZ⟩ : ∃ y ∈ Q, z * y * z⁻¹ = y ∧ y ∉ zOf Q := by
    by_contra hno
    push Not at hno
    exact hne (eq_commutator_of_fixed hp hp2 hz2 hzQ hexp hE.comm_eq hno)
  have hRy : ⁅Q, zpowers z⁆ ≤ centralizer ({y} : Set G) :=
    commutator_le_centralizer_of_fixed hp hp2 hz2 hzQ hexp hcl he hyQ hyz
  have hyCen : y ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * z = z * y * z⁻¹ * z := by rw [hyz]
      _ = z * y := by group
  have hyR : y ∈ centralizer ((⁅Q, zpowers z⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_singleton_iff.mp (hRy hr)
  have hZQ : zOf Q ≤ Q := inf_le_left
  have hZc : zOf Q ≤ centralizer (Q : Set G) := inf_le_right
  have hAQ : zOf Q ⊔ zpowers y ≤ Q := sup_le hZQ (Subgroup.zpowers_le.mpr hyQ)
  have hAz : zOf Q ⊔ zpowers y ≤ Cen z := sup_le he (Subgroup.zpowers_le.mpr hyCen)
  have hAR : zOf Q ⊔ zpowers y ≤ centralizer ((⁅Q, zpowers z⁆ : Subgroup G) : Set G) :=
    sup_le (hZc.trans (Subgroup.centralizer_le (fun x hx => hRQ hx)))
      (Subgroup.zpowers_le.mpr hyR)
  obtain ⟨V, hVA, hVe, hV2⟩ := hplane G p hp hp2 (zOf Q ⊔ zpowers y) (hQp.to_le hAQ)
    (not_isCyclic_sup hp hexp hE.card_Z hyQ hyZ)
  have hVQ : V ≤ Q := hVA.trans hAQ
  have hVz : V ≤ Cen z := hVA.trans hAz
  have hVR : V ≤ centralizer ((⁅Q, zpowers z⁆ : Subgroup G) : Set G) := hVA.trans hAR
  have hXR : X ≤ ⁅Q, zpowers z⁆ := le_commutator_of_inverts hp hp2 hXQ hexp hXinv
  have hVX : V ≤ normalizer (X : Set G) :=
    hVR.trans ((Subgroup.centralizer_le (fun x hx => hXR hx)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hXc : ⁅X, zpowers z⁆ = X := commutator_eq_self_of_card_inverts hp hp2 hXcard hXinv
  apply hmin.X_not
  refine h911 G z k S M p hC V X (le_inf (hVQ.trans hQP) hVz) hVe hV2 ?_ (hXQ.trans hQP)
    hmin.X_ne hXc (sup_le hVX (Subgroup.zpowers_le.mpr hmin.X_inv))
  intro v hvV hv1
  by_contra hnot
  have hvR : v ∈ centralizer ((⁅Q, zpowers z⁆ : Subgroup G) : Set G) := hVR hvV
  have hvz : z * v = v * z := (Subgroup.mem_centralizer_singleton_iff.mp (hVz hvV)).symm
  have hv0 : zpowers v ≠ ⊥ := by
    intro h
    apply hv1
    have : v ∈ zpowers v := Subgroup.mem_zpowers v
    rw [h] at this
    exact Subgroup.mem_bot.mp this
  exact h916 G z k S M p hC (zpowers v) ⁅Q, zpowers z⁆
    (Subgroup.zpowers_le.mpr ((hVQ.trans hQP) hvV)) hv0 (mem_normalizer_zpowers_of_comm hvz) hnot
    (le_inf (hRQ.trans hQP) ((le_centralizer_zpowers_of_mem hvR).trans
      (Subgroup.centralizer_le_normalizer _))) hR0 hRc hRN

end L613

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
