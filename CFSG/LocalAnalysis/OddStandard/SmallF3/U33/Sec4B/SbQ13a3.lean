module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17CosB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGHVI218B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a1

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open CFSG.GH74.GLS.Bg.TwoGroups
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13a_comm_mem (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ * (om * x₁ * om⁻¹) * x₁⁻¹ * (om * x₁ * om⁻¹)⁻¹ ∈ fourGrp x₁ x₂ := by
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := (q13a_x₁_facts h).1
  have hx'Q : om * x₁ * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    q13a_conj_Q h (q13a_mem_M h).2.2.2.2 hx₁Q
  exact l12_comm_mem_V h.c11 (l12_Q_le_R h.c11 hx₁Q) (l12_Q_le_R h.c11 hx'Q)

private lemma q13a_comm_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (x₁ * (om * x₁ * om⁻¹) * x₁⁻¹ * (om * x₁ * om⁻¹)⁻¹) ^ 2 = 1 := by
  rw [pow_two]
  exact CFSG.Open.IsElemAbelian.mul_self_eq_one
    (h.c11.wreath.fourGrp_eq_omega).2.1 (q13a_comm_mem h)

private lemma q13a_x'_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (om * x₁ * om⁻¹) * (om * x₁ * om⁻¹) = x₁ * x₁ := by
  have hx₁sqV : x₁ * x₁ ∈ fourGrp x₁ x₂ := by
    simpa [pow_two] using (q13a_x₁_facts h).2.2.2.2.1
  have hom := (q13a_om_comm h).2.2 (x₁ * x₁) hx₁sqV
  calc (om * x₁ * om⁻¹) * (om * x₁ * om⁻¹) = om * (x₁ * x₁) * om⁻¹ := by group
    _ = (x₁ * x₁) * om * om⁻¹ := by rw [hom]
    _ = x₁ * x₁ := by group

private lemma q13a_tau_conj_x' (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau * (om * x₁ * om⁻¹) * tau⁻¹ = (om * x₁ * om⁻¹)⁻¹ := by
  have htau_x₁ : tau * x₁ * tau⁻¹ = x₁⁻¹ := (q13a_x₁_facts h).2.2.2.1
  have homc : Commute tau om := (q13a_om_comm h).1.symm
  have hconj_om : tau * om * tau⁻¹ = om := by rw [homc.eq]; group
  have hconj_om_inv : tau * om⁻¹ * tau⁻¹ = om⁻¹ := by
    rw [(homc.inv_right).eq]; group
  calc tau * (om * x₁ * om⁻¹) * tau⁻¹
      = (tau * om * tau⁻¹) * (tau * x₁ * tau⁻¹) * (tau * om⁻¹ * tau⁻¹) := by group
    _ = om * x₁⁻¹ * om⁻¹ := by rw [hconj_om, htau_x₁, hconj_om_inv]
    _ = (om * x₁ * om⁻¹)⁻¹ := by group

private lemma q13a_sq_eq_comm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (x₁ * (om * x₁ * om⁻¹)) ^ 2 =
      x₁ * (om * x₁ * om⁻¹) * x₁⁻¹ * (om * x₁ * om⁻¹)⁻¹ := by
  set x' : G := om * x₁ * om⁻¹ with hx'def
  set c : G := x₁ * x' * x₁⁻¹ * x'⁻¹ with hcdef
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := (q13a_x₁_facts h).1
  have hx'Q : x' ∈ ctxQ t tau x₁ x₂ rho := by
    rw [hx'def]
    exact q13a_conj_Q h (q13a_mem_M h).2.2.2.2 hx₁Q
  have hx'sq : x' * x' = x₁ * x₁ := by
    rw [hx'def]
    exact q13a_x'_sq h
  have hcV : c ∈ fourGrp x₁ x₂ := by
    rw [hcdef]
    exact q13a_comm_mem h
  have hc_sq : c * c = 1 :=
    CFSG.Open.IsElemAbelian.mul_self_eq_one
      (h.c11.wreath.fourGrp_eq_omega).2.1 hcV
  have hc_inv_comm : x₁ * c⁻¹ = c⁻¹ * x₁ := by
    have hcomm : Commute x₁ c :=
      (commute_iff_eq x₁ c).mpr (q13a_V_central h c hcV x₁ hx₁Q).symm
    exact hcomm.inv_right.eq
  have hswap : x' * x₁ = c⁻¹ * (x₁ * x') := by
    have h1 : c * (x' * x₁) = x₁ * x' := by rw [hcdef]; group
    rw [← h1]
    group
  have hy2 : (x₁ * x₁) * (x₁ * x₁) = 1 := by
    have h4 : x₁ ^ 4 = 1 := by
      have := pow_orderOf_eq_one x₁
      rwa [(q13a_x₁_facts h).2.2.1] at this
    have h4' := h4
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul] at h4'
    simpa [pow_two] using h4'
  calc (x₁ * x') ^ 2 = x₁ * (x' * (x₁ * x')) := by rw [pow_two]; group
    _ = x₁ * ((x' * x₁) * x') := by group
    _ = x₁ * ((c⁻¹ * (x₁ * x')) * x') := by rw [hswap]
    _ = (x₁ * c⁻¹) * ((x₁ * x') * x') := by group
    _ = (c⁻¹ * x₁) * ((x₁ * x') * x') := by rw [hc_inv_comm]
    _ = c⁻¹ * ((x₁ * x₁) * (x' * x')) := by group
    _ = c⁻¹ * ((x₁ * x₁) * (x₁ * x₁)) := by rw [hx'sq]
    _ = c⁻¹ := by rw [hy2, mul_one]
    _ = c := mul_eq_one_iff_inv_eq.mp hc_sq

private lemma q13a_tau_conj_elt (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau * (x₁ * (om * x₁ * om⁻¹)) * tau⁻¹ =
      (x₁ * (om * x₁ * om⁻¹))⁻¹ *
        (x₁ * (om * x₁ * om⁻¹) * x₁⁻¹ * (om * x₁ * om⁻¹)⁻¹) := by
  have htau_x₁ : tau * x₁ * tau⁻¹ = x₁⁻¹ := (q13a_x₁_facts h).2.2.2.1
  have htau_x' := q13a_tau_conj_x' h
  calc tau * (x₁ * (om * x₁ * om⁻¹)) * tau⁻¹
      = (tau * x₁ * tau⁻¹) * (tau * (om * x₁ * om⁻¹) * tau⁻¹) := by group
    _ = x₁⁻¹ * (om * x₁ * om⁻¹)⁻¹ := by rw [htau_x₁, htau_x']
    _ = (x₁ * (om * x₁ * om⁻¹))⁻¹ *
        (x₁ * (om * x₁ * om⁻¹) * x₁⁻¹ * (om * x₁ * om⁻¹)⁻¹) := by group

private def q13aAddEquivZ4 : (ZMod 4 × ZMod 4) ≃+ (Fin 2 → ZMod 4) where
  toFun := fun p => fun i => if i = 0 then p.1 else p.2
  invFun := fun f => (f 0, f 1)
  left_inv := by
    intro p
    ext <;> simp
  right_inv := by
    intro f
    funext i
    fin_cases i <;> simp
  map_add' := by
    intro p q
    funext i
    fin_cases i <;> simp

private def q13aZ4Z4EquivZ4pow2 : Z4Z4 ≃* Outside.Z4pow 2 :=
  AddEquiv.toMultiplicative q13aAddEquivZ4

theorem q13a_fpfSetting_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    FpfSetting (q13A t tau x₁ x₂ rho) (fourGrp x₁ x₂) rho := by
  refine ⟨q13a_V_le_A h, ?_, q13a_rho_cube h, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq
    exact (q13a_V_central h q hq p (Subgroup.mem_inf.mp hp).1).symm
  · intro x hx
    exact (q13a_A_inv h x hx).1
  · intro x hx
    exact h.c11.normal_V.2 rho (q13a_mem_M h).2.2.1 x hx
  · intro x hx hfix
    apply l12_cent_Q_rho h.c11 x (Subgroup.mem_inf.mp hx).1
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  · rw [(h.c11.wreath.fourGrp_eq_omega).2.2]
  · have hmul := Subgroup.relIndex_mul_card (H := fourGrp x₁ x₂)
      (K := q13A t tau x₁ x₂ rho)
    rw [inf_eq_left.mpr (q13a_V_le_A h), q13a_card_A h,
      (h.c11.wreath.fourGrp_eq_omega).2.2] at hmul
    norm_num at hmul
    omega

theorem q13a_A_comm (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, ∀ b ∈ q13A t tau x₁ x₂ rho, a * b = b * a :=
  (q13a_fpfSetting_A h).comm

theorem q13a_elt_mem_A (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    x₁ * (om * x₁ * om⁻¹) ∈ q13A t tau x₁ x₂ rho := by
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := (q13a_x₁_facts h).1
  have hx'Q : om * x₁ * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    q13a_conj_Q h (q13a_mem_M h).2.2.2.2 hx₁Q
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hx₁Q hx'Q, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmain : tau * (x₁ * (om * x₁ * om⁻¹)) * tau⁻¹ = x₁ * (om * x₁ * om⁻¹) := by
    rw [q13a_tau_conj_elt h, ← q13a_sq_eq_comm h, pow_two]
    group
  have hcomm : tau * (x₁ * (om * x₁ * om⁻¹)) = (x₁ * (om * x₁ * om⁻¹)) * tau :=
    mul_inv_eq_iff_eq_mul.mp hmain
  exact hcomm.symm

theorem q13a_elt_sq_ne (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (x₁ * (om * x₁ * om⁻¹)) ^ 2 ≠ 1 := by
  intro hsq1
  have hc1 : x₁ * (om * x₁ * om⁻¹) * x₁⁻¹ * (om * x₁ * om⁻¹)⁻¹ = 1 := by
    rw [← q13a_sq_eq_comm h, hsq1]
  have hcomm1 : x₁ * (om * x₁ * om⁻¹) = (om * x₁ * om⁻¹) * x₁ := by
    calc x₁ * (om * x₁ * om⁻¹)
        = (x₁ * (om * x₁ * om⁻¹) * x₁⁻¹ * (om * x₁ * om⁻¹)⁻¹) *
            ((om * x₁ * om⁻¹) * x₁) := by group
      _ = 1 * ((om * x₁ * om⁻¹) * x₁) := by rw [hc1]
      _ = (om * x₁ * om⁻¹) * x₁ := one_mul _
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho := (q13a_x₁_facts h).1
  have hx₁base : x₁ ∈ baseGrp x₁ x₂ := (q13a_x₁_facts h).2.1
  have hx'Q : om * x₁ * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho :=
    q13a_conj_Q h (q13a_mem_M h).2.2.2.2 hx₁Q
  have hx'base : om * x₁ * om⁻¹ ∈ baseGrp x₁ x₂ := by
    have hmem : om * x₁ * om⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({x₁} : Set G) :=
      ⟨hx'Q, Subgroup.mem_centralizer_singleton_iff.mpr hcomm1.symm⟩
    rwa [q13a_CQ_x₁ h] at hmem
  have hx't : (om * x₁ * om⁻¹) * t = t * (om * x₁ * om⁻¹) := by
    have hle : baseGrp x₁ x₂ ≤ centralizer ({t} : Set G) := by
      rw [← l12_CQ_t h.c11]; exact inf_le_right
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx'base)
  have hx'ttau : (om * x₁ * om⁻¹) * (t * tau) = (t * tau) * (om * x₁ * om⁻¹) := by
    have h := (q13a_CQt_om h x₁ hx₁Q).mp hx₁base
    exact Subgroup.mem_centralizer_singleton_iff.mp h.2
  have htt : t * (t * tau) = tau := by
    rw [← mul_assoc, q13a_t_mul_self h, one_mul]
  have hx'tau : (om * x₁ * om⁻¹) * tau = tau * (om * x₁ * om⁻¹) := by
    calc (om * x₁ * om⁻¹) * tau
        = (om * x₁ * om⁻¹) * (t * (t * tau)) := by rw [htt]
      _ = ((om * x₁ * om⁻¹) * t) * (t * tau) := by group
      _ = (t * (om * x₁ * om⁻¹)) * (t * tau) := by rw [hx't]
      _ = t * ((om * x₁ * om⁻¹) * (t * tau)) := by group
      _ = t * ((t * tau) * (om * x₁ * om⁻¹)) := by rw [hx'ttau]
      _ = (t * (t * tau)) * (om * x₁ * om⁻¹) := by group
      _ = tau * (om * x₁ * om⁻¹) := by rw [htt]
  have htau_x'_comm : tau * (om * x₁ * om⁻¹) * tau⁻¹ = om * x₁ * om⁻¹ := by
    rw [← hx'tau, mul_assoc, mul_inv_cancel, mul_one]
  have hx'eq : om * x₁ * om⁻¹ = (om * x₁ * om⁻¹)⁻¹ := by
    have h := (q13a_tau_conj_x' h).symm
    rw [htau_x'_comm] at h
    exact h.symm
  have hx'sq1 : (om * x₁ * om⁻¹) * (om * x₁ * om⁻¹) = 1 := by
    nth_rewrite 1 [hx'eq]
    exact inv_mul_cancel (om * x₁ * om⁻¹)
  have hx'sq := q13a_x'_sq h
  exact (q13a_x₁_facts h).2.2.2.2.2 (by rw [pow_two, ← hx'sq, hx'sq1])

theorem q13a_elt_order (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    orderOf (x₁ * (om * x₁ * om⁻¹)) = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (x₁ * (om * x₁ * om⁻¹)) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, q13a_sq_eq_comm h, q13a_comm_sq h]
  have h2 : (x₁ * (om * x₁ * om⁻¹)) ^ 2 ≠ 1 := q13a_elt_sq_ne h
  have h := orderOf_eq_prime_pow (x := x₁ * (om * x₁ * om⁻¹)) (p := 2) (n := 1)
    (by simpa using h2) (by simpa using h4)
  simpa using h

theorem q13a_A_iso (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    IsZ4pow 2 (q13A t tau x₁ x₂ rho) := by
  have haA : x₁ * (om * x₁ * om⁻¹) ∈ q13A t tau x₁ x₂ rho := q13a_elt_mem_A h
  have haQ : x₁ * (om * x₁ * om⁻¹) ∈ ctxQ t tau x₁ x₂ rho := (Subgroup.mem_inf.mp haA).1
  let x : ctxQ t tau x₁ x₂ rho := ⟨x₁ * (om * x₁ * om⁻¹), haQ⟩
  have hx : orderOf x = 4 := by
    rw [Subgroup.orderOf_mk]
    exact q13a_elt_order h
  let ρ' : MulAut (ctxQ t tau x₁ x₂ rho) :=
    Outside.conjAut (ctxQ t tau x₁ x₂ rho) rho (q13a_rho_norm_Q h)
  have hF : Outside.FpfNonab (ctxQ t tau x₁ x₂ rho) ρ' := q13a_fpfNonab h
  let B : Subgroup (ctxQ t tau x₁ x₂ rho) := zpowers x ⊔ zpowers (ρ' x)
  obtain ⟨eB⟩ := hF.sup_equiv hx
  have hB1 : (zpowers x).map (ctxQ t tau x₁ x₂ rho).subtype ≤ q13A t tau x₁ x₂ rho := by
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    change (((x ^ n : ctxQ t tau x₁ x₂ rho)) : G) ∈ q13A t tau x₁ x₂ rho
    rw [Subgroup.coe_zpow]
    exact (q13A t tau x₁ x₂ rho).zpow_mem haA n
  have hB2 : (zpowers (ρ' x)).map (ctxQ t tau x₁ x₂ rho).subtype ≤ q13A t tau x₁ x₂ rho := by
    have hρ'a : rho * (x₁ * (om * x₁ * om⁻¹)) * rho⁻¹ ∈ q13A t tau x₁ x₂ rho :=
      (q13a_A_inv h _ haA).1
    have hρ'x : (((ρ' x : ctxQ t tau x₁ x₂ rho)) : G) =
        rho * (x₁ * (om * x₁ * om⁻¹)) * rho⁻¹ := by
      rw [Outside.conjAut_coe]
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    change ((((ρ' x) ^ n : ctxQ t tau x₁ x₂ rho)) : G) ∈ q13A t tau x₁ x₂ rho
    rw [Subgroup.coe_zpow, hρ'x]
    exact (q13A t tau x₁ x₂ rho).zpow_mem hρ'a n
  have hle : B.map (ctxQ t tau x₁ x₂ rho).subtype ≤ q13A t tau x₁ x₂ rho := by
    change (zpowers x ⊔ zpowers (ρ' x)).map (ctxQ t tau x₁ x₂ rho).subtype ≤
      q13A t tau x₁ x₂ rho
    rw [Subgroup.map_sup]
    exact sup_le hB1 hB2
  have hcardB : Nat.card B = 16 := hF.card_sup hx
  have hcardmap : Nat.card (B.map (ctxQ t tau x₁ x₂ rho).subtype) = 2 ^ 4 := by
    rw [Subgroup.card_map_of_injective (ctxQ t tau x₁ x₂ rho).subtype_injective, hcardB]
    norm_num
  have hBmapA : B.map (ctxQ t tau x₁ x₂ rho).subtype = q13A t tau x₁ x₂ rho :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardmap, q13a_card_A h])
  have eA : ↥(q13A t tau x₁ x₂ rho) ≃* Z4Z4 :=
    (MulEquiv.subgroupCongr hBmapA.symm).trans
      ((B.equivMapOfInjective (ctxQ t tau x₁ x₂ rho).subtype
        (ctxQ t tau x₁ x₂ rho).subtype_injective).symm.trans eB)
  exact ⟨eA.trans q13aZ4Z4EquivZ4pow2⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
