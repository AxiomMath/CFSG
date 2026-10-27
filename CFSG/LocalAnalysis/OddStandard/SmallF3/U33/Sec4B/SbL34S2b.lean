module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S0i
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutZmodProd

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


private theorem mem_sup_of_commute {H K : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ K, Commute a b) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  rw [← Subgroup.closure_eq H, ← Subgroup.closure_eq K, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · exact ⟨y, hy, 1, K.one_mem, (mul_one y).symm⟩
      · exact ⟨1, H.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, H.one_mem, 1, K.one_mem, (mul_one 1).symm⟩
  | mul y z _ _ hy hz =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      obtain ⟨a', ha', b', hb', rfl⟩ := hz
      refine ⟨a * a', H.mul_mem ha ha', b * b', K.mul_mem hb hb', ?_⟩
      have hba : b * a' = a' * b := (hcomm a' ha' b hb).eq.symm
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [hba]
        _ = a * a' * (b * b') := by group
  | inv y _ hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      exact ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb, (hcomm a ha b hb).mul_inv⟩

section Base

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
include hc

theorem base_eq_sup : baseGrp x₁ x₂ = zpowers x₁ ⊔ zpowers x₂ := by
  rw [baseGrp]
  have hset : ({x₁, x₂} : Set G) = {x₁} ∪ {x₂} := by ext; simp [or_comm]
  rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]

theorem card_base : Nat.card (baseGrp x₁ x₂) = 2 ^ 4 := by
  rw [base_eq_sup hc]
  rw [Outside.card_zpowers_sup_zpowers x₁ x₂ hc.wreath.comm 4 hc.wreath.ord_x₁
    hc.wreath.ord_x₂ hc.wreath.inf_eq_bot]
  norm_num

theorem base_comm : ∀ a ∈ baseGrp x₁ x₂, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := by
    refine isMulCommutative_closure (k := ({x₁, x₂} : Set G)) ?_
    intro u hu v hv _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Commute.refl _
    · exact hc.wreath.comm
    · exact hc.wreath.comm.symm
    · exact Commute.refl _
  intro a ha b hb
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : baseGrp x₁ x₂) ⟨b, hb⟩)

private theorem base_decomp {b : G} (hb : b ∈ baseGrp x₁ x₂) :
    ∃ i j : ℤ, b = x₁ ^ i * x₂ ^ j := by
  rw [base_eq_sup hc] at hb
  have hcomm : ∀ a ∈ zpowers x₁, ∀ c ∈ zpowers x₂, Commute a c := by
    intro a ha c hc'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    have hcc : Commute x₁ x₂ := hc.wreath.comm
    exact Commute.zpow_zpow hcc i j
  obtain ⟨a, ha, c, hcmem, rfl⟩ :=
    mem_sup_of_commute (H := zpowers x₁) (K := zpowers x₂) hcomm hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hcmem
  exact ⟨i, j, rfl⟩

theorem tau_inv_base : ∀ k ∈ baseGrp x₁ x₂, tau * k * tau⁻¹ = k⁻¹ := by
  intro k hk
  have hbc := base_comm hc
  have key : k ∈ baseGrp x₁ x₂ ∧ tau * k * tau⁻¹ = k⁻¹ := by
    rw [baseGrp] at hk ⊢
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
        refine ⟨subset_closure hx, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hc.tau_x₁
        · exact hc.tau_x₂
    | one => exact ⟨one_mem _, by simp⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨hxA, hx'⟩ := ihx
        obtain ⟨hyA, hy'⟩ := ihy
        refine ⟨mul_mem hxA hyA, ?_⟩
        calc tau * (x * y) * tau⁻¹ = (tau * x * tau⁻¹) * (tau * y * tau⁻¹) := by group
          _ = x⁻¹ * y⁻¹ := by rw [hx', hy']
          _ = (x * y)⁻¹ := by rw [hbc x hxA y hyA, mul_inv_rev]
    | inv x _ ihx =>
        obtain ⟨hxA, hx'⟩ := ihx
        refine ⟨inv_mem hxA, ?_⟩
        rw [show tau * x⁻¹ * tau⁻¹ = (tau * x * tau⁻¹)⁻¹ by group, hx']
  exact key.2

theorem base_sq_eq_one {b : G} (hb : b ∈ baseGrp x₁ x₂) (h : b * b = 1) : b ∈ fourGrp x₁ x₂ := by
  obtain ⟨i, j, rfl⟩ := base_decomp hc hb
  have hcc : Commute x₁ x₂ := hc.wreath.comm
  have hc12 : Commute (x₁ ^ i) (x₂ ^ j) := Commute.zpow_zpow hcc i j
  have h2 : x₁ ^ (i * 2) * x₂ ^ (j * 2) = 1 := by
    have hp : (x₁ ^ i * x₂ ^ j) ^ 2 = 1 := by rw [pow_two]; exact h
    rw [hc12.mul_pow 2, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at hp
    exact hp
  have hx1 : x₁ ^ (i * 2) = 1 := by
    have hmem : x₁ ^ (i * 2) ∈ zpowers x₁ ⊓ zpowers x₂ := by
      refine ⟨Subgroup.zpow_mem_zpowers x₁ (i * 2), ?_⟩
      rw [eq_inv_of_mul_eq_one_left h2]
      exact (zpowers x₂).inv_mem (Subgroup.zpow_mem_zpowers x₂ (j * 2))
    rw [hc.wreath.inf_eq_bot] at hmem
    simpa using hmem
  have hx2 : x₂ ^ (j * 2) = 1 := by
    rw [hx1, one_mul] at h2; exact h2
  have h4i : (4 : ℤ) ∣ i * 2 := by
    have hh := (orderOf_dvd_iff_zpow_eq_one (x := x₁) (i := i * 2)).mpr hx1
    rwa [hc.wreath.ord_x₁] at hh
  have h4j : (4 : ℤ) ∣ j * 2 := by
    have hh := (orderOf_dvd_iff_zpow_eq_one (x := x₂) (i := j * 2)).mpr hx2
    rwa [hc.wreath.ord_x₂] at hh
  obtain ⟨k, hk⟩ := h4i
  obtain ⟨l, hl⟩ := h4j
  have hik : i = 2 * k := by omega
  have hjl : j = 2 * l := by omega
  rw [hik, hjl, zpow_mul, zpow_mul]
  have hx1sq : x₁ ^ (2 : ℤ) ∈ fourGrp x₁ x₂ := by
    have h : x₁ ^ (2 : ℕ) ∈ fourGrp x₁ x₂ := subset_closure (by simp)
    simpa using h
  have hx2sq : x₂ ^ (2 : ℤ) ∈ fourGrp x₁ x₂ := by
    have h : x₂ ^ (2 : ℕ) ∈ fourGrp x₁ x₂ := by
      rw [hc.wreath.x₂_sq]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    simpa using h
  exact mul_mem ((fourGrp x₁ x₂).zpow_mem hx1sq k) ((fourGrp x₁ x₂).zpow_mem hx2sq l)

theorem CQ_t_eq_base : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) = baseGrp x₁ x₂ := by
  have hle : baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
    intro k hk
    refine ⟨hc.base_le_Q hk, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h' := t_comm_base hc hk
    calc t * k = (t * k * t⁻¹) * t := by group
      _ = k * t := by rw [h']
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_CQ_t hc, card_base hc])).symm

theorem rho_norm_base : ∀ k ∈ baseGrp x₁ x₂, rho * k * rho⁻¹ ∈ baseGrp x₁ x₂ := by
  intro k hk
  rw [← CQ_t_eq_base hc]
  refine ⟨hc.normal_Q.2 rho hc.rho_mem_M k (hc.base_le_Q hk), ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  have hkt : Commute t k := by
    have h' := t_comm_base hc hk
    show t * k = k * t
    calc t * k = (t * k * t⁻¹) * t := by group
      _ = k * t := by rw [h']
  have htr : Commute t rho := hc.rho_comm_t.symm
  calc t * (rho * k * rho⁻¹) = (t * rho) * k * rho⁻¹ := by group
    _ = (rho * t) * k * rho⁻¹ := by rw [htr.eq]
    _ = rho * (t * k) * rho⁻¹ := by group
    _ = rho * (k * t) * rho⁻¹ := by rw [hkt.eq]
    _ = rho * k * (t * rho⁻¹) := by group
    _ = rho * k * (rho⁻¹ * t) := by rw [htr.inv_right.eq]
    _ = (rho * k * rho⁻¹) * t := by group

theorem CQ_t_tau : ctxQ t tau x₁ x₂ rho ⊓ centralizer ((closure {t, tau} : Subgroup G) : Set G) =
    fourGrp x₁ x₂ := by
  apply le_antisymm
  · intro b hb
    obtain ⟨hbQ, hbC⟩ := hb
    have hbt : b ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) := by
      refine ⟨hbQ, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (Subgroup.mem_centralizer_iff.mp hbC) t (subset_closure (by simp))
    rw [CQ_t_eq_base hc] at hbt
    have hbtau : tau * b * tau⁻¹ = b := by
      have h' := (Subgroup.mem_centralizer_iff.mp hbC) tau (subset_closure (by simp))
      rw [h', mul_assoc, mul_inv_cancel, mul_one]
    have hbinv : tau * b * tau⁻¹ = b⁻¹ := tau_inv_base hc b hbt
    have hbb : b * b = 1 := by
      have hbeq : b = b⁻¹ := by rw [← hbinv, hbtau]
      simpa [← hbeq] using mul_inv_cancel b
    exact base_sq_eq_one hc hbt hbb
  · intro v hv
    refine ⟨hc.V_le_Q hv, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    have hcomm : Commute h v := by
      induction hh using Subgroup.closure_induction with
      | mem x hx =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact V_comm_O hc hc.t_mem_O hv
          · exact V_comm_O hc hc.tau_mem_O hv
      | one => exact Commute.one_left v
      | mul x y _ _ ihx ihy => exact ihx.mul_left ihy
      | inv x _ ihx => exact ihx.inv_left
    exact hcomm.eq

theorem x₁_not_mem_V : x₁ ∉ fourGrp x₁ x₂ := by
  intro hx
  have h2 : x₁ ^ 2 = 1 := (fourGrp_elemAbelian hc).2 x₁ hx
  have hdvd : orderOf x₁ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  rw [hc.wreath.ord_x₁] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  omega

end Base

section Sylow

variable (hc : Ctx4Q t L S x₁ x₂ lam rho tau) (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho))
include hc hs

theorem CQ_base_eq : ctxQ t tau x₁ x₂ rho ⊓ centralizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) =
    baseGrp x₁ x₂ := by
  apply le_antisymm
  · intro b hb
    obtain ⟨hbQ, hbC⟩ := hb
    have hbCx : b ∈ centralizer ({x₁} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (Subgroup.mem_centralizer_iff.mp hbC) x₁ (subset_closure (by simp))
    have hle : baseGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({x₁} : Set G) := by
      intro a ha
      refine ⟨hc.base_le_Q ha, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact base_comm hc x₁ (subset_closure (by simp)) a ha
    have heq : ctxQ t tau x₁ x₂ rho ⊓ centralizer ({x₁} : Set G) = baseGrp x₁ x₂ :=
      (Subgroup.eq_of_le_of_card_ge hle (by
        rw [card_CQ_of_noncentral hc hs (hc.base_le_Q (subset_closure (by simp)))
          (x₁_not_mem_V hc), card_base hc])).symm
    exact heq ▸ ⟨hbQ, hbCx⟩
  · intro a ha
    refine ⟨hc.base_le_Q ha, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    exact base_comm hc h hh a ha

end Sylow

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
