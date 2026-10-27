module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13d

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

theorem c13_CQ_w (hc : Ctx13B t L S x₁ x₂ lam rho tau om) {w : G}
    (hw : w ∈ ctxM t tau x₁ x₂) (hw2 : w * w = 1) (hwρ : w * rho = rho * w)
    (hwY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, w * a = a * w)
    (hnt : ∃ a ∈ ctxQ t tau x₁ x₂ rho, a⁻¹ * (w * a * w⁻¹) ∉ fourGrp x₁ x₂) :
    ctxQ t tau x₁ x₂ rho ⊓ centralizer ({w} : Set G) = ctxYq t tau x₁ x₂ rho := by
  apply le_antisymm
  · have hCP : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({w} : Set G) ≤
        ctxQ t tau x₁ x₂ rho := inf_le_left
    have hCρ : ∀ x ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({w} : Set G),
        rho * x * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({w} : Set G) := by
      intro x hx
      have hxQ : x ∈ ctxQ t tau x₁ x₂ rho := hx.1
      have hxw : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      have hwρi : w * rho⁻¹ = rho⁻¹ * w := (show Commute w rho from hwρ).inv_right.eq
      refine ⟨hc.normal_Q.2 rho (l12_rho_lam_mem_M hc.toCtx11).1 x hxQ, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc (rho * x * rho⁻¹) * w
            = rho * x * (rho⁻¹ * w) := by group
          _ = rho * x * (w * rho⁻¹) := by rw [← hwρi]
          _ = rho * (x * w) * rho⁻¹ := by group
          _ = rho * (w * x) * rho⁻¹ := by rw [hxw]
          _ = (rho * w) * x * rho⁻¹ := by group
          _ = (w * rho) * x * rho⁻¹ := by rw [hwρ]
          _ = w * (rho * x * rho⁻¹) := by group)
    rcases hc.fpf_QY.sup_eq hCP hCρ with hCY | hcover
    · exact hCY
    · exfalso
      obtain ⟨a, haQ, haV⟩ := hnt
      obtain ⟨c, hcC, hcx⟩ := hcover a haQ
      have hcw : c * w = w * c := Subgroup.mem_centralizer_singleton_iff.mp hcC.2
      have hyw : (c⁻¹ * a) * w = w * (c⁻¹ * a) := (hwY (c⁻¹ * a) hcx).symm
      have haw : a * w = w * a := by
        calc a * w = (c * (c⁻¹ * a)) * w := by group
          _ = c * ((c⁻¹ * a) * w) := by group
          _ = c * (w * (c⁻¹ * a)) := by rw [hyw]
          _ = (c * w) * (c⁻¹ * a) := by group
          _ = (w * c) * (c⁻¹ * a) := by rw [hcw]
          _ = w * a := by group
      have hmain : w * a * w⁻¹ = a := by rw [← haw]; group
      exact haV (by rw [hmain]; simp)
  · intro a ha
    exact ⟨ctxYq_le_ctxQ ha, Subgroup.mem_centralizer_singleton_iff.mpr (hwY a ha).symm⟩

theorem c13_comm_w (hc : Ctx13B t L S x₁ x₂ lam rho tau om) {w : G}
    (hw : w ∈ ctxM t tau x₁ x₂) (hw2 : w * w = 1) (hwρ : w * rho = rho * w)
    (hwY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, w * a = a * w)
    (hnt : ∃ a ∈ ctxQ t tau x₁ x₂ rho, a⁻¹ * (w * a * w⁻¹) ∉ fourGrp x₁ x₂) :
    ⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ ≤ ctxYq t tau x₁ x₂ rho ∧
      Nat.card ↥(⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆) = 4 ∧
      ⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ ⊓ fourGrp x₁ x₂ = ⊥ ∧
      ∀ q ∈ ctxQ t tau x₁ x₂ rho, q⁻¹ * (w * q * w⁻¹) ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ := by
  set Cw : Subgroup G := ⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ with hCw
  obtain ⟨hmem, hcard⟩ := comm_zpowers_inv (A := ctxQ t tau x₁ x₂ rho) (g := w)
    hc.Q_comm hw2 (fun a ha => hc.normal_Q.2 w hw a ha)
  rw [← hCw] at hmem hcard
  have hleY : Cw ≤ ctxYq t tau x₁ x₂ rho := by
    intro n hn
    obtain ⟨a, haQ, rfl⟩ := (hmem n).mp hn
    have h := c13_triv_QY hc hw hw2 hwρ a⁻¹ (Subgroup.inv_mem _ haQ)
    have he : a * w * a⁻¹ * w⁻¹ = (a⁻¹)⁻¹ * (w * a⁻¹ * w⁻¹) := by group
    rw [he]
    exact h
  have hmem4 : ∀ q ∈ ctxQ t tau x₁ x₂ rho,
      q⁻¹ * (w * q * w⁻¹) ∈ Cw := by
    intro q hq
    have he : q⁻¹ * (w * q * w⁻¹) = q⁻¹ * w * (q⁻¹)⁻¹ * w⁻¹ := by group
    rw [he]
    exact (hmem _).mpr ⟨q⁻¹, Subgroup.inv_mem _ hq, rfl⟩
  have hcard2 : Nat.card ↥Cw = 4 := by
    have h := hcard
    rw [c13_CQ_w hc hw hw2 hwρ hwY hnt, card_ctxYq hc.q_iso,
      IsZ4Z4E4.card hc.q_iso] at h
    omega
  have hCwρ : ∀ x ∈ Cw, rho * x * rho⁻¹ ∈ Cw := by
    intro x hx
    obtain ⟨a, haQ, rfl⟩ := (hmem x).mp hx
    have hra : rho * a * rho⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
      hc.normal_Q.2 rho (l12_rho_lam_mem_M hc.toCtx11).1 a haQ
    have hrom : rho * w * rho⁻¹ = w := by rw [← hwρ]; group
    have hromi : rho * w⁻¹ * rho⁻¹ = w⁻¹ := by
      have hcomm : rho * w = w * rho := by
        calc rho * w = rho * w * rho⁻¹ * rho := by group
          _ = w * rho := by rw [hrom]
      have h : Commute rho w := hcomm
      rw [h.inv_right.eq]
      group
    refine (hmem _).mpr ⟨rho * a * rho⁻¹, hra, ?_⟩
    calc rho * (a * w * a⁻¹ * w⁻¹) * rho⁻¹
        = (rho * a * rho⁻¹) * (rho * w * rho⁻¹) * (rho * a⁻¹ * rho⁻¹)
            * (rho * w⁻¹ * rho⁻¹) := by group
      _ = (rho * a * rho⁻¹) * w * (rho * a * rho⁻¹)⁻¹ * w⁻¹ := by
            have hai : rho * a⁻¹ * rho⁻¹ = (rho * a * rho⁻¹)⁻¹ := by group
            rw [hrom, hromi, hai]
  have hinf : Cw ⊓ fourGrp x₁ x₂ = ⊥ := by
    rcases hc.fpf_YV.sup_eq hleY hCwρ with hCV | hcover
    · obtain ⟨a, haQ, haV⟩ := hnt
      exact absurd (hCV (hmem4 a haQ)) haV
    · have hYle : ctxYq t tau x₁ x₂ rho ≤ Cw ⊔ fourGrp x₁ x₂ := by
        intro x hx
        obtain ⟨c, hcC, hcv⟩ := hcover x hx
        have hm : c * (c⁻¹ * x) ∈ Cw ⊔ fourGrp x₁ x₂ := Subgroup.mul_mem_sup hcC hcv
        rwa [show c * (c⁻¹ * x) = x by group] at hm
      have hsup_le : Cw ⊔ fourGrp x₁ x₂ ≤ ctxYq t tau x₁ x₂ rho :=
        sup_le hleY hc.V_le_Y
      have hsup : Cw ⊔ fourGrp x₁ x₂ = ctxYq t tau x₁ x₂ rho :=
        le_antisymm hsup_le hYle
      have hcommc : ∀ h ∈ Cw, ∀ k ∈ fourGrp x₁ x₂, h * k = k * h :=
        fun h hh k hk => hc.Q_comm h (ctxYq_le_ctxQ (hleY hh)) k
          (ctxYq_le_ctxQ (hc.V_le_Y hk))
      have hcard' := card_sup_mul_card_inf (H := Cw) (K := fourGrp x₁ x₂) hcommc
      rw [hsup, card_ctxYq hc.q_iso, hcard2, hc.wreath.fourGrp_eq_omega.2.2] at hcard'
      have h1 : Nat.card ↥(Cw ⊓ fourGrp x₁ x₂) = 1 := by omega
      exact Subgroup.card_eq_one.mp h1
  exact ⟨hleY, hcard2, hinf, hmem4⟩

theorem c13_inv_coset (hc : Ctx13B t L S x₁ x₂ lam rho tau om) {w : G}
    (hw : w ∈ ctxM t tau x₁ x₂) (hw2 : w * w = 1) (hwρ : w * rho = rho * w)
    (hwY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, w * a = a * w)
    (hnt : ∃ a ∈ ctxQ t tau x₁ x₂ rho, a⁻¹ * (w * a * w⁻¹) ∉ fourGrp x₁ x₂)
    (hwQ : w ∉ ctxQ t tau x₁ x₂ rho) :
    InvIn (w • (ctxQ t tau x₁ x₂ rho : Set G)) = w • (ctxYq t tau x₁ x₂ rho : Set G) := by
  obtain ⟨hleY, hcard, hinf, hmem4⟩ := c13_comm_w hc hw hw2 hwρ hwY hnt
  ext u
  constructor
  · intro hu
    rw [InvIn, Set.mem_setOf_eq] at hu
    obtain ⟨huQ, hu2, hu1⟩ := hu
    obtain ⟨q, hqQ, hwq⟩ := Set.mem_smul_set.mp huQ
    have hwq' : w * q = u := by simpa using hwq
    have huu : w * q * w * q = 1 := by
      have h : (w * q) * (w * q) = 1 := by
        rw [← hwq', pow_two] at hu2
        exact hu2
      simpa only [mul_assoc] using h
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hinv : w * q * w⁻¹ = q⁻¹ := by
      rw [hwi]
      calc w * q * w = w * q * w * q * q⁻¹ := by group
        _ = (w * q * w * q) * q⁻¹ := by group
        _ = 1 * q⁻¹ := by rw [huu]
        _ = q⁻¹ := one_mul _
    have hqC : q⁻¹ * (w * q * w⁻¹) ∈ ⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ :=
      hmem4 q hqQ
    have hqV : q⁻¹ * (w * q * w⁻¹) ∈ fourGrp x₁ x₂ := by
      rw [hinv]
      simpa [pow_two, mul_inv_rev] using (fourGrp x₁ x₂).inv_mem (hc.sq_V q hqQ)
    have hqbot : q⁻¹ * (w * q * w⁻¹) ∈ (⊥ : Subgroup G) := by
      rw [← hinf]
      exact ⟨hqC, hqV⟩
    have hqeq : q⁻¹ * (w * q * w⁻¹) = 1 := Subgroup.mem_bot.mp hqbot
    have h11 : q⁻¹ * q⁻¹ = 1 := by rwa [hinv] at hqeq
    have hq2 : q * q = 1 := by
      have h := congrArg Inv.inv h11
      simpa [mul_inv_rev] using h
    have hqY : q ∈ ctxYq t tau x₁ x₂ rho :=
      (mem_ctxYq_iff hc.q_iso q).mpr ⟨hqQ, by simpa [pow_two] using hq2⟩
    exact Set.mem_smul_set.mpr ⟨q, hqY, by simpa using hwq⟩
  · intro hu
    obtain ⟨y, hyY, hwy⟩ := Set.mem_smul_set.mp hu
    have hwy' : w * y = u := by simpa using hwy
    have hyQ : y ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hyY
    have hy2 : y * y = 1 := by
      have h := (mem_ctxYq_iff hc.q_iso y).mp hyY
      simpa [pow_two] using h.2
    have hyw : w * y = y * w := hwY y hyY
    have hu2 : u ^ 2 = 1 := by
      rw [← hwy', pow_two]
      calc (w * y) * (w * y) = w * (y * w) * y := by group
        _ = w * (w * y) * y := by rw [← hyw]
        _ = (w * w) * (y * y) := by group
        _ = 1 := by rw [hw2, hy2, mul_one]
    have hune : u ≠ 1 := by
      intro hu1
      apply hwQ
      have hwy1 : w * y = 1 := by rw [hwy', hu1]
      have hw_eq : w = y⁻¹ := by
        calc w = w * y * y⁻¹ := by group
          _ = 1 * y⁻¹ := by rw [hwy1]
          _ = y⁻¹ := one_mul _
      rw [hw_eq]
      exact (ctxQ t tau x₁ x₂ rho).inv_mem hyQ
    rw [InvIn, Set.mem_setOf_eq]
    exact ⟨Set.mem_smul_set.mpr ⟨y, hyQ, by simpa using hwy⟩, hu2, hune⟩

theorem c13_Q_om_of (hc : Ctx13B t L S x₁ x₂ lam rho tau om) {w : G}
    (hw : w ∈ ctxM t tau x₁ x₂) (hw2 : w * w = 1) (hwρ : w * rho = rho * w)
    (hwY : ∀ a ∈ ctxYq t tau x₁ x₂ rho, w * a = a * w)
    (hnt : ∃ a ∈ ctxQ t tau x₁ x₂ rho, a⁻¹ * (w * a * w⁻¹) ∉ fourGrp x₁ x₂)
    (hwQ : w ∉ ctxQ t tau x₁ x₂ rho) : Ctx13Om t tau x₁ x₂ rho w := by
  obtain ⟨hleY, hcard, hinf, hmem4⟩ := c13_comm_w hc hw hw2 hwρ hwY hnt
  have hYcomm : ∀ a ∈ ctxYq t tau x₁ x₂ rho, ∀ b ∈ ctxYq t tau x₁ x₂ rho,
      a * b = b * a := by
    haveI : IsMulCommutative ↥(ctxYq t tau x₁ x₂ rho) := hc.Y_elem.1
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : ↥(ctxYq t tau x₁ x₂ rho)) ⟨b, hb⟩)
  refine ⟨⟨IsMulCommutative.of_comm
      (fun x y : ↥⁅ctxQ t tau x₁ x₂ rho, zpowers w⁆ =>
        Subtype.ext (hYcomm x.1 (hleY x.2) y.1 (hleY y.2))),
      fun x hx => hc.Y_elem.2 x (hleY hx)⟩,
    hcard, hinf, c13_CQ_w hc hw hw2 hwρ hwY hnt,
    c13_inv_coset hc hw hw2 hwρ hwY hnt hwQ⟩

theorem c13_om_not_mem_Q (hc : Ctx13A t L S x₁ x₂ lam rho tau om) :
    om ∉ ctxQ t tau x₁ x₂ rho ∧ om * tau ∉ ctxQ t tau x₁ x₂ rho := by
  have hom_mem := hc.om_mem
  have hom_cent : om ∈ centralizer ({rho} : Set G) := hom_mem.2
  have hτ2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have hτcent : tau * rho = rho * tau := hc.tau_rho
  refine ⟨?_, ?_⟩
  · intro homQ
    have hom_rho : om * rho = rho * om :=
      Subgroup.mem_centralizer_singleton_iff.mp hom_cent
    have homeq : om = 1 := l12_cent_Q_rho hc.toCtx11 om homQ hom_rho
    exact hc.om_not_mem (by rw [homeq]; exact Subgroup.one_mem _)
  · intro homτQ
    have hom_rho : om * rho = rho * om :=
      Subgroup.mem_centralizer_singleton_iff.mp hom_cent
    have hcomm : (om * tau) * rho = rho * (om * tau) := by
      calc (om * tau) * rho = om * (tau * rho) := by group
        _ = om * (rho * tau) := by rw [hτcent]
        _ = (om * rho) * tau := by group
        _ = (rho * om) * tau := by rw [hom_rho]
        _ = rho * (om * tau) := by group
    have homeq : om * tau = 1 := l12_cent_Q_rho hc.toCtx11 (om * tau) homτQ hcomm
    have homeq' : om = tau := by
      calc om = om * (tau * tau) := by rw [hτ2, mul_one]
        _ = (om * tau) * tau := by group
        _ = 1 * tau := by rw [homeq]
        _ = tau := one_mul _
    exact hc.om_not_mem (by rw [homeq']; exact Subgroup.subset_closure (by simp))

theorem c13_omtau_data (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    om * tau ∈ ctxM t tau x₁ x₂ ∧ (om * tau) * (om * tau) = 1 ∧
      (om * tau) * rho = rho * (om * tau) ∧
      ∀ a ∈ ctxYq t tau x₁ x₂ rho, (om * tau) * a = a * (om * tau) := by
  have hA := c13_om_data hc.toCtx13A
  have hT := c13_tau_data hc.toCtx13A
  have hτ2 : tau * tau = 1 := hT.2.1
  have homτcomm : om * tau = tau * om := by
    have hmem : tau ∈ ctxCO t tau x₁ x₂ rho ⊓
        centralizer ((ctxCO t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [hc.CO_center]
      exact Subgroup.mem_zpowers tau
    exact (Subgroup.mem_centralizer_iff.mp hmem.2) om hc.om_mem
  refine ⟨Subgroup.mul_mem _ hA.1 hT.1, ?_, ?_, ?_⟩
  · calc (om * tau) * (om * tau) = om * (tau * om) * tau := by group
      _ = om * (om * tau) * tau := by rw [← homτcomm]
      _ = (om * om) * (tau * tau) := by group
      _ = 1 := by rw [hc.om_sq, hτ2, mul_one]
  · calc (om * tau) * rho = om * (tau * rho) := by group
      _ = om * (rho * tau) := by rw [hT.2.2]
      _ = (om * rho) * tau := by group
      _ = (rho * om) * tau := by rw [hA.2.2]
      _ = rho * (om * tau) := by group
  · intro a ha
    calc (om * tau) * a = om * (tau * a) := by group
      _ = om * (a * tau) := by rw [hc.tau_cent_Y a ha]
      _ = (om * a) * tau := by group
      _ = (a * om) * tau := by rw [hc.om_cent_Y a ha]
      _ = a * (om * tau) := by group

theorem c13_omtau_nontriv (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    ∃ a ∈ ctxQ t tau x₁ x₂ rho,
      a⁻¹ * ((om * tau) * a * (om * tau)⁻¹) ∉ fourGrp x₁ x₂ := by
  obtain ⟨a, haQ, haV⟩ := c13_om_nontriv hc.toCtx13B
  refine ⟨a, haQ, ?_⟩
  set c : G := a⁻¹ * (om * a * om⁻¹) with hc_def
  have hcY : c ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hc_def]
    exact c13_triv_QY hc.toCtx13B (c13_om_data hc.toCtx13A).1 hc.om_sq
      (c13_om_data hc.toCtx13A).2.2 a haQ
  have hcQ : c ∈ ctxQ t tau x₁ x₂ rho := ctxYq_le_ctxQ hcY
  have hacomm : a * c = c * a := hc.Q_comm a haQ c hcQ
  have hom_inv : om⁻¹ = om := inv_eq_of_mul_eq_one_right hc.om_sq
  have hτ2 : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have hτ_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hτ2
  have hwt2 : (om * tau) * (om * tau) = 1 := (c13_omtau_data hc).2.1
  have h1 : (om * tau) * a * (om * tau)⁻¹ = (a * c)⁻¹ := by
    have htau : tau * a * tau⁻¹ = a⁻¹ := hc.tau_inv_Q a haQ
    calc (om * tau) * a * (om * tau)⁻¹ = om * (tau * a * tau⁻¹) * om⁻¹ := by group
      _ = om * a⁻¹ * om⁻¹ := by rw [htau]
      _ = (om * a * om⁻¹)⁻¹ := by group
      _ = (a * c)⁻¹ := by
          have h : om * a * om⁻¹ = a * c := by rw [hc_def]; group
          rw [h]
  intro heV
  have heq : a⁻¹ * ((om * tau) * a * (om * tau)⁻¹) = a⁻¹ * a⁻¹ * c⁻¹ := by
    rw [h1]
    have hcc : c⁻¹ * a⁻¹ = a⁻¹ * c⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hacomm]
    calc a⁻¹ * (a * c)⁻¹ = a⁻¹ * (c⁻¹ * a⁻¹) := by rw [mul_inv_rev]
      _ = a⁻¹ * (a⁻¹ * c⁻¹) := by rw [hcc]
      _ = a⁻¹ * a⁻¹ * c⁻¹ := by group
  rw [heq] at heV
  have hae : a * a * (a⁻¹ * a⁻¹ * c⁻¹) ∈ fourGrp x₁ x₂ :=
    (fourGrp x₁ x₂).mul_mem (by simpa [pow_two] using hc.sq_V a haQ) heV
  have hc_eq : c = (a * a * (a⁻¹ * a⁻¹ * c⁻¹))⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv]
    group
  have hcV : c ∉ fourGrp x₁ x₂ := by rw [hc_def]; exact haV
  exact hcV (by rw [hc_eq]; exact (fourGrp x₁ x₂).inv_mem hae)

theorem c13_Q_om (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    Ctx13Om t tau x₁ x₂ rho om := by
  exact c13_Q_om_of hc.toCtx13B (c13_om_data hc.toCtx13A).1
    (c13_om_data hc.toCtx13A).2.1 (c13_om_data hc.toCtx13A).2.2 hc.om_cent_Y
    (c13_om_nontriv hc.toCtx13B) (c13_om_not_mem_Q hc.toCtx13A).1

theorem c13_Q_omtau (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    Ctx13Om t tau x₁ x₂ rho (om * tau) := by
  exact c13_Q_om_of hc.toCtx13B (c13_omtau_data hc).1 (c13_omtau_data hc).2.1
    (c13_omtau_data hc).2.2.1 (c13_omtau_data hc).2.2.2 (c13_omtau_nontriv hc)
    (c13_om_not_mem_Q hc.toCtx13A).2

theorem ctx13d_of_c (hc : Ctx13C t L S x₁ x₂ lam rho tau om) :
    Ctx13D t L S x₁ x₂ lam rho tau om :=
  { toCtx13C := hc, lam_om := c13_lam_om hc, Q_om := c13_Q_om hc, Q_omtau := c13_Q_omtau hc }

end CFSG.OddStandard.SmallF3.HarrisU33.S4B