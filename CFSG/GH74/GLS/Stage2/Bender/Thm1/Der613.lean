module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.ExtraInv
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Extra

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Aux613

variable {G : Type} [Group G] [Finite G]

theorem nf_commutator_QP (h61 : Prop6_1) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    (hC : Ctx6 G z k S M p) {Q : Subgroup G} (hQ : QP z p (Op p M) Q) : NF z M ⁅Q, zpowers z⁆ := by
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op p M) hQ
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hRQ : ⁅Q, zpowers z⁆ ≤ Q := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzQ)
  have hR0 : ⁅Q, zpowers z⁆ ≠ ⊥ := fun h => hQ.2.2.2.2.2 (commutator_zpowers_eq_bot_iff.mp h)
  have hRC : Cen z ≤ normalizer ((⁅Q, zpowers z⁆ : Subgroup G) : Set G) := fun c hc =>
    le_normalizer_commutator_zpowers (hQn (hC.cen_le hc)) hc
  exact h61 G z k S M p hC _ (hRQ.trans hQ.1) hR0 hRC

omit [Finite G] in
theorem le_centralizer_zpowers_of_mem {R : Subgroup G} {v : G} (h : v ∈ centralizer (R : Set G)) :
    R ≤ centralizer ((zpowers v : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hc : Commute r v := Subgroup.mem_centralizer_iff.mp h r hr
  exact (hc.symm.zpow_left n).eq

omit [Finite G] in
theorem le_commutator_of_inverts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : G} {Q X : Subgroup G}
    (hXQ : X ≤ Q) (hexp : ∀ x ∈ Q, x ^ p = 1) (hinv : Inverts z X) : X ≤ ⁅Q, zpowers z⁆ := by
  intro x hx
  have h1 : z * x * z⁻¹ = x⁻¹ := hinv x hx
  have h2 : z * x⁻¹ * z⁻¹ = x := by
    calc z * x⁻¹ * z⁻¹ = (z * x * z⁻¹)⁻¹ := by group
      _ = x := by rw [h1, inv_inv]
  have hcomm : ⁅x, z⁆ = x ^ 2 := by
    calc ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by simp [commutatorElement_def, mul_assoc]
      _ = x ^ 2 := by rw [h2, pow_two]
  have hmem : x ^ 2 ∈ ⁅Q, zpowers z⁆ := by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (hXQ hx) (Subgroup.mem_zpowers z)
  obtain ⟨m, hm⟩ := exists_two_pow hp hp2 (hexp x (hXQ hx))
  have h3 := Subgroup.pow_mem _ hmem m
  rwa [hm] at h3

end Aux613

section L613

variable {G : Type} [Group G] [Finite G]

theorem lemma6_13_of (h61 : Prop6_1) (h610 : Lemma6_10) (h611 : Lemma6_11) (h612 : Lemma6_12)
    (h67 : Prop6_7) (hplane : OddNoncyclicPlane) : Lemma6_13 := by
  intro G _ _ z k S M p hC Q X hmin
  have hp := hC.prime
  have hp2 := hC.p_ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_two hC.orderOf_z
  have hPp : IsPGroup p ↥(Op p M) := isPGroup_Op p hp M
  have hQP : Q ≤ Op p M := hmin.Q_mem.1
  have hQp : IsPGroup p ↥Q := hPp.to_le hQP
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op p M) hmin.Q_mem
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hexp : ∀ x ∈ Q, x ^ p = 1 := hmin.Q_mem.2.2.1
  have hcl : ⁅⁅Q, Q⁆, Q⁆ = ⊥ := hmin.Q_mem.2.2.2.1
  have hXQ : X ≤ Q := hmin.X_le
  obtain ⟨⟨-, hXinv⟩, -, -, -, he, -⟩ := h611 G z k S M p hC Q X hmin
  have hE : ExtraG p Q := extraG_of_isExtraspecial (h612 G z k S M p hC Q X hmin)
  have hRQ : ⁅Q, zpowers z⁆ ≤ Q := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzQ)
  have hR0 : ⁅Q, zpowers z⁆ ≠ ⊥ := fun h => hmin.Q_mem.2.2.2.2.2 (commutator_zpowers_eq_bot_iff.mp h)
  have hRc : ⁅⁅Q, zpowers z⁆, zpowers z⁆ = ⁅Q, zpowers z⁆ :=
    commutator_zpowers_idem hC.orderOf_z hp hp2 hQp hzQ
  have hRN : NF z M ⁅Q, zpowers z⁆ := nf_commutator_QP h61 hC hmin.Q_mem
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
  apply hmin.X_not
  refine h67 G z k S M p hC p V hp (le_inf (hVQ.trans hQP) hVz) hVe hV2 ?_ X
    (hXQ.trans (hQP.trans (Op_le_Fm p hp M))) hmin.X_ne (sup_le hVX (Subgroup.zpowers_le.mpr hmin.X_inv))
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
  exact h610 G z k S M p hC (zpowers v) ⁅Q, zpowers z⁆
    (Subgroup.zpowers_le.mpr ((hVQ.trans hQP) hvV)) hv0 (mem_normalizer_zpowers_of_comm hvz) hnot
    (le_inf (hRQ.trans hQP) ((le_centralizer_zpowers_of_mem hvR).trans
      (Subgroup.centralizer_le_normalizer _))) hR0 hRc hRN

end L613

end CFSG.GH74.GLS.Stage2.Bender.Thm1
