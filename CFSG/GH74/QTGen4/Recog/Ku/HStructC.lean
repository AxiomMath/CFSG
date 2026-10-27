module

public import CFSG.GH74.QTGen4.Recog.Ku.Hyp
public import CFSG.GH74.QTGen4.Recog.Ku.HStructB

public section

namespace CFSG.GH74.QTGen4.Ku

namespace KuHyp

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H P : Subgroup G} {z : G}

theorem zP_mem (h : KuHyp G T M H P z) : z ∈ P := by
  have hz : z ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
    rw [h.pCentP]
    exact Subgroup.mem_zpowers z
  exact (Subgroup.mem_inf.mp hz).1

theorem zP_pc (h : KuHyp G T M H P z) : z ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
  rw [h.pCentP]
  exact Subgroup.mem_zpowers z

theorem zP_comm (h : KuHyp G T M H P z) {a : G} (ha : a ∈ P) : a * z = z * a :=
  Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h.zP_pc).2 a ha

theorem center_P_le (h : KuHyp G T M H P z) :
    Subgroup.center ↥P ≤ Subgroup.zpowers (⟨z, h.zP_mem⟩ : ↥P) := by
  intro c hc
  have hcP : (c : G) ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
    refine ⟨c.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro a ha
    have e := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨a, ha⟩)
    simpa using e
  have hcz : (c : G) ∈ Subgroup.zpowers z := by
    rw [← h.pCentP]
    exact hcP
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨k, Subtype.ext ?_⟩
  simpa using hk

theorem zpowers_le_center_P (h : KuHyp G T M H P z) :
    Subgroup.zpowers (⟨z, h.zP_mem⟩ : ↥P) ≤ Subgroup.center ↥P := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.mem_center_iff.mpr fun a => Subtype.ext ?_
  have hz : (a : G) * z = z * (a : G) := h.zP_comm a.2
  simpa using hz

theorem center_P_eq (h : KuHyp G T M H P z) :
    Subgroup.center ↥P = Subgroup.zpowers (⟨z, h.zP_mem⟩ : ↥P) :=
  le_antisymm h.center_P_le h.zpowers_le_center_P

theorem card_center_P (h : KuHyp G T M H P z) : Nat.card (Subgroup.center ↥P) = 2 := by
  have hEx := h.pExtra.1
  haveI := hEx
  exact CFSG.IsExtraspecial.center_order_p 2 ↥P

theorem orderOf_zP (h : KuHyp G T M H P z) : orderOf (⟨z, h.zP_mem⟩ : ↥P) = 2 := by
  have hc := h.card_center_P
  rw [h.center_P_eq, Nat.card_zpowers] at hc
  exact hc

theorem zP_ne (h : KuHyp G T M H P z) : z ≠ 1 := by
  intro h1
  have hord := h.orderOf_zP
  have e : (⟨z, h.zP_mem⟩ : ↥P) = 1 := Subtype.ext (by simp [h1])
  rw [e, orderOf_one] at hord
  norm_num at hord

theorem zP_sq (h : KuHyp G T M H P z) : z * z = 1 := by
  have hord := h.orderOf_zP
  have hp : (⟨z, h.zP_mem⟩ : ↥P) ^ 2 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hG : z ^ 2 = 1 := by
    have e := congrArg Subtype.val hp
    simpa using e
  rw [← pow_two]
  exact hG

theorem quot_P_comm (h : KuHyp G T M H P z) :
    ∀ u v : ↥P ⧸ Subgroup.center ↥P, u * v = v * u := by
  have hEx := h.pExtra.1
  haveI := hEx
  intro u v
  have hA : CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P) :=
    CFSG.IsExtraspecial.quotient_elementary_abelian 2 ↥P
  exact hA.toIsMulCommutative.is_comm.comm u v

theorem isEA_quot_P (h : KuHyp G T M H P z) :
    CFSG.IsElementaryAbelian 2 (↥P ⧸ Subgroup.center ↥P) := by
  have hEx := h.pExtra.1
  haveI := hEx
  exact CFSG.IsExtraspecial.quotient_elementary_abelian 2 ↥P

theorem sq_quot_P (h : KuHyp G T M H P z) (u : ↥P ⧸ Subgroup.center ↥P) : u ^ 2 = 1 := by
  haveI := h.isEA_quot_P
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (CFSG.IsElementaryAbelian.exponent_dvd_p 2 (↥P ⧸ Subgroup.center ↥P)) u

theorem kuZCore_P (h : KuHyp G T M H P z) : KuZCore (↥P) (⟨z, h.zP_mem⟩ : ↥P) := by
  have hne : (⟨z, h.zP_mem⟩ : ↥P) ≠ 1 := by
    intro h1
    have hord := h.orderOf_zP
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have hsq : (⟨z, h.zP_mem⟩ : ↥P) * (⟨z, h.zP_mem⟩ : ↥P) = 1 := by
    rw [← pow_two, ← h.orderOf_zP]
    exact pow_orderOf_eq_one _
  exact ⟨hne, hsq, h.center_P_eq, fun a b => comm_mem_of_quot_comm h.quot_P_comm a b,
    fun a => sq_mem_of_quot_sq h.sq_quot_P a⟩

theorem mem_P_of_acts_trivially_aux (h : KuHyp G T M H P z) {g : G} (hg : g ∈ H)
    (hgP : ∀ p ∈ P, g * p * g⁻¹ * p⁻¹ ∈ Subgroup.zpowers z) : g ∈ P := by
  have hC : KuZCore (↥P) (⟨z, h.zP_mem⟩ : ↥P) := h.kuZCore_P
  haveI := h.isEA_quot_P
  have hz : z ≠ 1 := h.zP_ne
  have hz2 : z * z = 1 := h.zP_sq
  have hcoe : ∀ a b : ↥P, ((⁅a, b⁆ : ↥P) : G) = ⁅(a : G), (b : G)⁆ := fun a b => by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  have hgC : g ∈ Subgroup.centralizer ({z} : Set G) := by
    have hg' := hg
    rw [h.hCz] at hg'
    exact hg'
  have hgz : z * g = g * z := Subgroup.mem_centralizer_iff.mp hgC z (Set.mem_singleton z)
  have hconj : ∀ a ∈ P, ∀ w ∈ Subgroup.zpowers z, a * w * a⁻¹ = w := by
    intro a ha w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : Commute a z := h.zP_comm ha
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  let χ : ↥P → ZMod 2 := fun p => sgn (g * (p : G) * g⁻¹ * (p : G)⁻¹)
  have hmul : ∀ a b : ↥P, χ (a * b) = χ a + χ b := by
    intro a b
    have ha := hgP (a : G) a.2
    have hb := hgP (b : G) b.2
    have e : g * ((a * b : ↥P) : G) * g⁻¹ * ((a * b : ↥P) : G)⁻¹ =
        (g * (a : G) * g⁻¹ * (a : G)⁻¹) *
          ((a : G) * (g * (b : G) * g⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    have hcb : (a : G) * (g * (b : G) * g⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
        g * (b : G) * g⁻¹ * (b : G)⁻¹ :=
      hconj (a : G) a.2 _ hb
    show sgn (g * ((a * b : ↥P) : G) * g⁻¹ * ((a * b : ↥P) : G)⁻¹) =
      sgn (g * (a : G) * g⁻¹ * (a : G)⁻¹) + sgn (g * (b : G) * g⁻¹ * (b : G)⁻¹)
    rw [e, hcb]
    exact sgn_mul_of hz hz2 (KuZCore.mem_zpowers_cases hz2 ha)
      (KuZCore.mem_zpowers_cases hz2 hb)
  have hcen : ∀ c ∈ Subgroup.center ↥P, χ c = 0 := by
    intro c hc
    rw [h.center_P_eq] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hck : (c : G) = z ^ k := by
      rw [← hk]
      simp
    have hcg : Commute g z := hgz.symm
    have hcomm : g * z ^ k = z ^ k * g := (hcg.zpow_right k).eq
    show sgn (g * (c : G) * g⁻¹ * (c : G)⁻¹) = 0
    rw [hck]
    have e1 : g * z ^ k * g⁻¹ * (z ^ k)⁻¹ = 1 := by
      rw [hcomm]
      group
    rw [e1]
    exact sgn_one_gen
  obtain ⟨u, hu⟩ := hC.exists_pair_eq χ hmul hcen
  have hEq : ∀ v : ↥P, sgn ⁅(u : G), (v : G)⁆ = sgn (g * (v : G) * g⁻¹ * (v : G)⁻¹) := by
    intro v
    have hv : sgn ⁅u, v⁆ = χ v := hu v
    rw [← hcoe, sgn_coe]
    exact hv
  have hEqG : ∀ v ∈ P, ⁅(u : G), v⁆ = g * v * g⁻¹ * v⁻¹ := by
    intro v hv
    have hcu : ⁅(u : G), v⁆ = 1 ∨ ⁅(u : G), v⁆ = z := by
      rcases hC.comm_pair u ⟨v, hv⟩ with e | e
      · left
        have e2 := congrArg Subtype.val e
        rw [hcoe] at e2
        simpa using e2
      · right
        have e2 := congrArg Subtype.val e
        rw [hcoe] at e2
        simpa using e2
    have hdv : g * v * g⁻¹ * v⁻¹ = 1 ∨ g * v * g⁻¹ * v⁻¹ = z :=
      KuZCore.mem_zpowers_cases hz2 (hgP v hv)
    exact sgn_inj_of hz hcu hdv (hEq ⟨v, hv⟩)
  have hvconj : ∀ v ∈ P, (u : G) * v * (u : G)⁻¹ = g * v * g⁻¹ := by
    intro v hv
    have e := hEqG v hv
    rw [commutatorElement_def] at e
    exact mul_right_cancel e
  have hkC : (u : G)⁻¹ * g ∈ Subgroup.centralizer (P : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro v hv
    have hv' := hvconj v hv
    calc v * ((u : G)⁻¹ * g) = (u : G)⁻¹ * ((u : G) * v * (u : G)⁻¹) * g := by group
      _ = (u : G)⁻¹ * (g * v * g⁻¹) * g := by rw [hv']
      _ = (u : G)⁻¹ * g * v := by group
  have hkH : (u : G)⁻¹ * g ∈ H := H.mul_mem (H.inv_mem (h.pH u.2)) hg
  have hkP : (u : G)⁻¹ * g ∈ P := h.hCentP ⟨hkH, hkC⟩
  have := P.mul_mem u.2 hkP
  rwa [mul_inv_cancel_left] at this

end KuHyp

end CFSG.GH74.QTGen4.Ku
