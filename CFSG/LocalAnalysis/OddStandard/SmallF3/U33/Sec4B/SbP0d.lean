module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private theorem E_comm (hc : Ctx8b t L S x₁ x₂ lam rho tau) {u v : G}
    (hu : u ∈ ctxE t x₁ x₂) (hv : v ∈ ctxE t x₁ x₂) : u * v = v * u := by
  haveI : IsMulCommutative ↥(ctxE t x₁ x₂) :=
    (hc.toCtx8a.toCtx8.toCtx10.toCtx4.toCtx).m2_PT_attained.1.1
  have key := mul_comm' (⟨u, hu⟩ : ↥(ctxE t x₁ x₂)) (⟨v, hv⟩ : ↥(ctxE t x₁ x₂))
  exact congrArg Subtype.val key

private theorem tau_commute_y (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    tau * x₁ ^ 2 = x₁ ^ 2 * tau := by
  have hx₁4 : x₁ ^ 4 = 1 := by
    rw [← hc.wreath.ord_x₁]
    exact pow_orderOf_eq_one x₁
  have hsq : x₁ ^ 2 * x₁ ^ 2 = 1 := by
    rw [← pow_add, show (2 + 2 : ℕ) = 4 from rfl, hx₁4]
  have hconj : tau * x₁ ^ 2 * tau⁻¹ = x₁ ^ 2 := by
    rw [← conj_pow (a := tau) (b := x₁) (i := 2), hc.tau_x₁, inv_pow,
      inv_eq_of_mul_eq_one_right hsq]
  exact mul_inv_eq_iff_eq_mul.mp hconj

private theorem tau_commute_z (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * tau := by
  have hcomm : Commute x₁ x₂ := hc.wreath.comm
  have hx₁4 : x₁ ^ 4 = 1 := by
    rw [← hc.wreath.ord_x₁]
    exact pow_orderOf_eq_one x₁
  have hx₂4 : x₂ ^ 4 = 1 := by
    rw [← hc.wreath.ord_x₂]
    exact pow_orderOf_eq_one x₂
  have hsq : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := by
    have h4 : (x₁ * x₂) ^ 4 = 1 := by
      rw [hcomm.mul_pow 4, hx₁4, hx₂4, one_mul]
    rw [← pow_add, show (2 + 2 : ℕ) = 4 from rfl, h4]
  have h1 : tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
    calc tau * (x₁ * x₂) * tau⁻¹
        = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
      _ = x₁⁻¹ * x₂⁻¹ := by rw [hc.tau_x₁, hc.tau_x₂]
      _ = (x₂ * x₁)⁻¹ := by rw [mul_inv_rev]
      _ = (x₁ * x₂)⁻¹ := by rw [← hcomm.eq]
  have hconj : tau * (x₁ * x₂) ^ 2 * tau⁻¹ = (x₁ * x₂) ^ 2 := by
    rw [← conj_pow (a := tau) (b := x₁ * x₂) (i := 2), h1, inv_pow,
      inv_eq_of_mul_eq_one_right hsq]
  exact mul_inv_eq_iff_eq_mul.mp hconj

private theorem fourGrp_le_centralizer_of (hc : Ctx8b t L S x₁ x₂ lam rho tau) {a : G}
    (hy : x₁ ^ 2 * a = a * x₁ ^ 2) (hz : (x₁ * x₂) ^ 2 * a = a * (x₁ * x₂) ^ 2) :
    fourGrp x₁ x₂ ≤ centralizer ({a} : Set G) := by
  rw [fourGrp]
  refine (Subgroup.closure_le _).mpr ?_
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hy
  · exact Subgroup.mem_centralizer_singleton_iff.mpr hz

private theorem mem_centralizer_fourGrp_of (hc : Ctx8b t L S x₁ x₂ lam rho tau) {a : G}
    (hy : x₁ ^ 2 * a = a * x₁ ^ 2) (hz : (x₁ * x₂) ^ 2 * a = a * (x₁ * x₂) ^ 2) :
    a ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (fourGrp_le_centralizer_of hc hy hz hv)

private theorem t_mem_centralizer_fourGrp (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    t ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hyE : x₁ ^ 2 ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)
  have hzE : (x₁ * x₂) ^ 2 ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)
  have htE : t ∈ ctxE t x₁ x₂ := Subgroup.subset_closure (by simp)
  exact mem_centralizer_fourGrp_of hc (E_comm hc hyE htE) (E_comm hc hzE htE)

private theorem tau_mem_centralizer_fourGrp (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    tau ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
  mem_centralizer_fourGrp_of hc (tau_commute_y hc).symm (tau_commute_z hc).symm

private theorem x₁_mem_centralizer_fourGrp (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    x₁ ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hcomm : Commute x₁ x₂ := hc.wreath.comm
  have hy : x₁ ^ 2 * x₁ = x₁ * x₁ ^ 2 := ((Commute.refl x₁).pow_right 2).eq.symm
  have hz : (x₁ * x₂) ^ 2 * x₁ = x₁ * (x₁ * x₂) ^ 2 :=
    (((Commute.refl x₁).mul_right hcomm).pow_right 2).eq.symm
  exact mem_centralizer_fourGrp_of hc hy hz

private theorem x₂_mem_centralizer_fourGrp (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    x₂ ∈ centralizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
  have hcomm : Commute x₁ x₂ := hc.wreath.comm
  have hy : x₁ ^ 2 * x₂ = x₂ * x₁ ^ 2 := (hcomm.symm.pow_right 2).eq.symm
  have hz : (x₁ * x₂) ^ 2 * x₂ = x₂ * (x₁ * x₂) ^ 2 :=
    ((hcomm.symm.mul_right (Commute.refl x₂)).pow_right 2).eq.symm
  exact mem_centralizer_fourGrp_of hc hy hz

theorem p0_card_U (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 ^ 10 := by
  have hlamM : lam ∈ ctxM t tau x₁ x₂ :=
    (p0_gens_mem_M hc.toCtx8a.toCtx8.toCtx10.toCtx4).2.2.2.2.2
  have hnorm : ∀ k ∈ zpowers lam, ∀ h ∈ ctxO t tau x₁ x₂, k * h * k⁻¹ ∈ ctxO t tau x₁ x₂ := by
    intro k hk h hh
    exact (p0_normal_O t tau x₁ x₂).2 k (Subgroup.zpowers_le.mpr hlamM hk) h hh
  have hdis : ctxO t tau x₁ x₂ ⊓ zpowers lam = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxO, hxL⟩ := hx
    change x ∈ Subgroup.zpowers lam at hxL
    obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff.mp hxL)
    have h2 : (orderOf lam : ℤ) = 2 := by
      rw [hc.wreath.ord_lam]
      norm_num
    have hkm : lam ^ (k % 2) = x := by
      have h := zpow_mod_orderOf lam k
      rw [h2] at h
      exact h.trans hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hkm
      exact hkm.symm
    · rw [h1, zpow_one] at hkm
      exact absurd (hkm.symm ▸ hxO) hc.lam_not_mem_O
  rw [ctxU, card_sup_eq_mul hnorm hdis, hc.card_O, Nat.card_zpowers, hc.wreath.ord_lam]
  norm_num

theorem p0_M_eq (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    ctxM t tau x₁ x₂ = ctxO t tau x₁ x₂ ⊔ closure {rho, lam} := by
  obtain ⟨htM, htauM, hx₁M, hx₂M, hrhoM, hlamM⟩ :=
    p0_gens_mem_M hc.toCtx8a.toCtx8.toCtx10.toCtx4
  set A : Subgroup G := closure {rho, lam} with hA
  have hle : ctxO t tau x₁ x₂ ⊔ A ≤ ctxM t tau x₁ x₂ := by
    refine sup_le (p0_O_le_M t tau x₁ x₂) ?_
    rw [hA]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hrhoM
    · exact hlamM
  have hzple : zpowers lam ≤ A := by
    rw [hA]
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hUle : ctxU t tau x₁ x₂ lam ≤ ctxO t tau x₁ x₂ ⊔ A := by
    rw [ctxU]
    exact sup_le le_sup_left (hzple.trans le_sup_right)
  have h2dvd : 2 ^ 10 ∣ Nat.card ↥(ctxO t tau x₁ x₂ ⊔ A) := by
    have h := Subgroup.card_dvd_of_le hUle
    rwa [p0_card_U hc] at h
  have h3dvd : 3 ∣ Nat.card ↥(ctxO t tau x₁ x₂ ⊔ A) := by
    have hmem : rho ∈ ctxO t tau x₁ x₂ ⊔ A :=
      Subgroup.mem_sup_right (by rw [hA]; exact Subgroup.subset_closure (by simp))
    have h3 : orderOf (⟨rho, hmem⟩ : ↥(ctxO t tau x₁ x₂ ⊔ A)) = 3 := by
      rw [Subgroup.orderOf_mk, hc.ord_rho]
    have h := orderOf_dvd_natCard (⟨rho, hmem⟩ : ↥(ctxO t tau x₁ x₂ ⊔ A))
    rwa [h3] at h
  have hprod : 2 ^ 10 * 3 ∣ Nat.card ↥(ctxO t tau x₁ x₂ ⊔ A) :=
    (by decide : Nat.Coprime (2 ^ 10) 3).mul_dvd_of_dvd_of_dvd h2dvd h3dvd
  have hge : 3 * 2 ^ 10 ≤ Nat.card ↥(ctxO t tau x₁ x₂ ⊔ A) := by
    have hpos : 0 < Nat.card ↥(ctxO t tau x₁ x₂ ⊔ A) :=
      Nat.card_pos_iff.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩
    have h := Nat.le_of_dvd hpos hprod
    rwa [Nat.mul_comm] at h
  have hcardle : Nat.card ↥(ctxO t tau x₁ x₂ ⊔ A) ≤ Nat.card ↥(ctxM t tau x₁ x₂) := by
    have hpos : 0 < Nat.card ↥(ctxM t tau x₁ x₂) :=
      Nat.card_pos_iff.mpr ⟨⟨1, one_mem _⟩, inferInstance⟩
    exact Nat.le_of_dvd hpos (Subgroup.card_dvd_of_le hle)
  have hcard : Nat.card ↥(ctxO t tau x₁ x₂ ⊔ A) = 3 * 2 ^ 10 :=
    le_antisymm (by rw [← hc.card_M]; exact hcardle) hge
  have hEq : ctxO t tau x₁ x₂ ⊔ A = ctxM t tau x₁ x₂ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hc.card_M, hcard])
  rw [← hEq, hA]

theorem p0_gens_mem_O (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    t ∈ ctxO t tau x₁ x₂ ∧ tau ∈ ctxO t tau x₁ x₂ ∧ x₁ ∈ ctxO t tau x₁ x₂ ∧
      x₂ ∈ ctxO t tau x₁ x₂ := by
  obtain ⟨htM, htauM, hx₁M, hx₂M, _, _⟩ :=
    p0_gens_mem_M hc.toCtx8a.toCtx8.toCtx10.toCtx4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hc.O_eq_C]; exact ⟨htM, t_mem_centralizer_fourGrp hc⟩
  · rw [hc.O_eq_C]; exact ⟨htauM, tau_mem_centralizer_fourGrp hc⟩
  · rw [hc.O_eq_C]; exact ⟨hx₁M, x₁_mem_centralizer_fourGrp hc⟩
  · rw [hc.O_eq_C]; exact ⟨hx₂M, x₂_mem_centralizer_fourGrp hc⟩

theorem p0_S_le_U (hc : Ctx8b t L S x₁ x₂ lam rho tau) : S ≤ ctxU t tau x₁ x₂ lam := by
  obtain ⟨htO, htauO, hx₁O, hx₂O⟩ := p0_gens_mem_O hc
  rw [hc.S_eq, hc.l43]
  refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left htO)) ?_
  rw [m12Grp]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx | hx
  · rw [hx]; exact Subgroup.mem_sup_left hx₁O
  · rw [hx]; exact Subgroup.mem_sup_left hx₂O
  · rw [hx]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  · rw [hx]; exact Subgroup.mem_sup_left htauO

theorem p0_U_sylow (hc : Ctx8b t L S x₁ x₂ lam rho tau) :
    IsSylowIn 2 (ctxU t tau x₁ x₂ lam) (ctxM t tau x₁ x₂) := by
  have hlamM : lam ∈ ctxM t tau x₁ x₂ :=
    (p0_gens_mem_M hc.toCtx8a.toCtx8.toCtx10.toCtx4).2.2.2.2.2
  have hle : ctxU t tau x₁ x₂ lam ≤ ctxM t tau x₁ x₂ := by
    rw [ctxU]
    exact sup_le (p0_O_le_M t tau x₁ x₂) (Subgroup.zpowers_le.mpr hlamM)
  refine ⟨hle, IsPGroup.of_card (p0_card_U hc), ?_⟩
  have hcardU : Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 ^ 10 := p0_card_U hc
  have hrel : (ctxU t tau x₁ x₂ lam).relIndex (ctxM t tau x₁ x₂) * 2 ^ 10 = 3 * 2 ^ 10 := by
    have h := Subgroup.relIndex_mul_card (ctxU t tau x₁ x₂ lam) (ctxM t tau x₁ x₂)
    rw [inf_eq_left.mpr hle, hcardU, hc.card_M] at h
    exact h
  have hrel3 : (ctxU t tau x₁ x₂ lam).relIndex (ctxM t tau x₁ x₂) = 3 := by
    exact Nat.mul_right_cancel (by norm_num : 0 < (2 : ℕ) ^ 10) hrel
  rw [hrel3]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
