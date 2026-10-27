module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbI18a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem conj_fix_of_centralizes {Ξ Y : Subgroup G}
    (hYc : ∀ a ∈ Y, ∀ x ∈ Ξ, x * a = a * x) {m a : G} (hm : m ∈ Ξ) (ha : a ∈ Y) :
    m * a * m⁻¹ = a := by
  have hcomm : m * a = a * m := hYc a ha m hm
  rw [hcomm]; group

private def commTauSub (Ξ Y : Subgroup G) (tau : G)
    (hYc : ∀ a ∈ Y, ∀ x ∈ Ξ, x * a = a * x) (hYleΞ : Y ≤ Ξ)
    (hcommY : ∀ m ∈ Ξ, m * tau * m⁻¹ * tau⁻¹ ∈ Y) : Subgroup G where
  carrier := {y | ∃ m ∈ Ξ, m * tau * m⁻¹ * tau⁻¹ = y}
  mul_mem' := by
    rintro a b ⟨m1, hm1, ha⟩ ⟨m2, hm2, hb⟩
    refine ⟨m1 * m2, Ξ.mul_mem hm1 hm2, ?_⟩
    have haY : a ∈ Y := ha ▸ hcommY m1 hm1
    have hbY : b ∈ Y := hb ▸ hcommY m2 hm2
    have hfix : m1 * (m2 * tau * m2⁻¹ * tau⁻¹) * m1⁻¹
        = m2 * tau * m2⁻¹ * tau⁻¹ :=
      conj_fix_of_centralizes hYc hm1 (hcommY m2 hm2)
    have key : (m1 * m2) * tau * (m1 * m2)⁻¹ * tau⁻¹
        = (m2 * tau * m2⁻¹ * tau⁻¹) * (m1 * tau * m1⁻¹ * tau⁻¹) := by
      rw [show (m1 * m2) * tau * (m1 * m2)⁻¹ * tau⁻¹
          = m1 * (m2 * tau * m2⁻¹ * tau⁻¹) * m1⁻¹
            * (m1 * tau * m1⁻¹ * tau⁻¹) by group, hfix]
    have hab : b * a = a * b := hYc a haY b (hYleΞ hbY)
    calc (m1 * m2) * tau * (m1 * m2)⁻¹ * tau⁻¹
        = (m2 * tau * m2⁻¹ * tau⁻¹) * (m1 * tau * m1⁻¹ * tau⁻¹) := key
      _ = b * a := by rw [← hb, ← ha]
      _ = a * b := hab
  one_mem' := ⟨1, Ξ.one_mem, by group⟩
  inv_mem' := by
    rintro a ⟨m, hm, ha⟩
    refine ⟨m⁻¹, Ξ.inv_mem hm, ?_⟩
    have hfixinv : m * (m⁻¹ * tau * (m⁻¹)⁻¹ * tau⁻¹) * m⁻¹
        = m⁻¹ * tau * (m⁻¹)⁻¹ * tau⁻¹ :=
      conj_fix_of_centralizes hYc hm (hcommY m⁻¹ (Ξ.inv_mem hm))
    have key : m * (m⁻¹ * tau * (m⁻¹)⁻¹ * tau⁻¹) * m⁻¹ = a⁻¹ := by
      rw [← ha]; group
    rw [hfixinv] at key
    exact key

private theorem commTauSub_le_Y {Ξ Y : Subgroup G} {tau : G}
    (hYc : ∀ a ∈ Y, ∀ x ∈ Ξ, x * a = a * x) (hYleΞ : Y ≤ Ξ)
    (hcommY : ∀ m ∈ Ξ, m * tau * m⁻¹ * tau⁻¹ ∈ Y) :
    commTauSub Ξ Y tau hYc hYleΞ hcommY ≤ Y := by
  rintro y ⟨m, hm, hy⟩
  rw [← hy]
  exact hcommY m hm

theorem l18_comm_tau_surj (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {y : G}
    (hy : y ∈ ctxYq t tau x₁ x₂ rho) :
    ∃ m ∈ ctxXi t tau x₁ x₂ rho, m * tau * m⁻¹ * tau⁻¹ = y := by
  have hc13 : Ctx13 t L S x₁ x₂ lam rho tau om := hc.toCtx13
  let Ξ : Subgroup G := ctxXi t tau x₁ x₂ rho
  let Y : Subgroup G := ctxYq t tau x₁ x₂ rho
  have hYc : ∀ a ∈ Y, ∀ x ∈ Ξ, x * a = a * x := by
    intro a ha x hx
    have hxC : x ∈ ctxCY t tau x₁ x₂ rho := l18_Xi_le_C hc hx
    have hcent : x ∈ centralizer ((ctxYq t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp hxC).2
    have hcomm : a * x = x * a := Subgroup.mem_centralizer_iff.mp hcent a ha
    exact hcomm.symm
  have hYleΞ : Y ≤ Ξ := (ctxYq_le_ctxQ).trans (l18_Q_le_Xi hc13)
  have hcommY : ∀ m ∈ Ξ, m * tau * m⁻¹ * tau⁻¹ ∈ Y :=
    fun m hm => l18_comm_tau_mem_Y hc hm
  let I : Subgroup G := commTauSub Ξ Y tau hYc hYleΞ hcommY
  have hI_le_Y : I ≤ Y := commTauSub_le_Y hYc hYleΞ hcommY
  have hV_le_Y : fourGrp x₁ x₂ ≤ Y := l17_V_le_Y hc13
  have hx₁Q : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hx₂Q : x₂ ∈ ctxQ t tau x₁ x₂ rho :=
    hc.base_le_Q (Subgroup.subset_closure (by simp))
  have hV_le_I : fourGrp x₁ x₂ ≤ I := by
    rw [fourGrp, Subgroup.closure_le]
    rintro g (hg : g ∈ ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G))
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · refine ⟨x₁, l18_Q_le_Xi hc13 hx₁Q, ?_⟩
      have h := hc.tau_inv_Q x₁ hx₁Q
      have h' : tau * x₁⁻¹ * tau⁻¹ = x₁ := by
        calc tau * x₁⁻¹ * tau⁻¹ = (tau * x₁ * tau⁻¹)⁻¹ := by group
          _ = x₁ := by rw [h]; simp
      show x₁ * tau * x₁⁻¹ * tau⁻¹ = x₁ ^ 2
      rw [show x₁ * tau * x₁⁻¹ * tau⁻¹ = x₁ * (tau * x₁⁻¹ * tau⁻¹) by group,
        h', pow_two]
    · have hxQ : x₁ * x₂ ∈ ctxQ t tau x₁ x₂ rho := mul_mem hx₁Q hx₂Q
      refine ⟨x₁ * x₂, l18_Q_le_Xi hc13 hxQ, ?_⟩
      have h := hc.tau_inv_Q (x₁ * x₂) hxQ
      have h' : tau * (x₁ * x₂)⁻¹ * tau⁻¹ = x₁ * x₂ := by
        calc tau * (x₁ * x₂)⁻¹ * tau⁻¹ = (tau * (x₁ * x₂) * tau⁻¹)⁻¹ := by group
          _ = x₁ * x₂ := by rw [h]; simp
      show (x₁ * x₂) * tau * (x₁ * x₂)⁻¹ * tau⁻¹ = (x₁ * x₂) ^ 2
      rw [show (x₁ * x₂) * tau * (x₁ * x₂)⁻¹ * tau⁻¹
          = (x₁ * x₂) * (tau * (x₁ * x₂)⁻¹ * tau⁻¹) by group, h', pow_two]
  have hI_rho : ∀ x ∈ I, rho * x * rho⁻¹ ∈ I := by
    rintro x ⟨m, hm, hx⟩
    have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc13).2.2.2.2
    have hm' : rho * m * rho⁻¹ ∈ Ξ := (l18_Xi_normal hc13).2 rho hρK m hm
    refine ⟨rho * m * rho⁻¹, hm', ?_⟩
    have hcomm : Commute tau rho := hc.tau_rho
    have h2 : rho⁻¹ * tau * rho = tau := by
      rw [hcomm.symm.inv_left.eq]; group
    have h2inv : rho⁻¹ * tau⁻¹ * rho = tau⁻¹ := by
      rw [hcomm.symm.inv_left.inv_right.eq]; group
    rw [← hx]
    calc (rho * m * rho⁻¹) * tau * (rho * m * rho⁻¹)⁻¹ * tau⁻¹
        = rho * m * (rho⁻¹ * tau * rho) * m⁻¹ * (rho⁻¹ * tau⁻¹ * rho) * rho⁻¹ := by
          group
      _ = rho * m * tau * m⁻¹ * tau⁻¹ * rho⁻¹ := by rw [h2, h2inv]
      _ = rho * (m * tau * m⁻¹ * tau⁻¹) * rho⁻¹ := by group
  have hV_rho : ∀ x ∈ fourGrp x₁ x₂, rho * x * rho⁻¹ ∈ fourGrp x₁ x₂ := by
    intro x hx
    have hρM : rho ∈ ctxM t tau x₁ x₂ := by
      rw [hc.M_eq]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    exact hc.normal_V.2 rho hρM x hx
  have hfix : ∀ x ∈ I, rho * x * rho⁻¹ = x → x = 1 := by
    intro x hx hxfix
    have hxY : x ∈ Y := hI_le_Y hx
    have hxP : x ∈ ctxP t tau x₁ x₂ rho := (l17_Q_le_P hc13) ((ctxYq_le_ctxQ) hxY)
    have hcomm : rho * x = x * rho := by
      calc rho * x = (rho * x * rho⁻¹) * rho := by group
        _ = x * rho := by rw [hxfix]
    exact l17_CP_rho hc13 x hxP hcomm.symm
  have hQ : Nat.card (fourGrp x₁ x₂) % 3 = 1 := by
    rw [l17_card_V hc13]
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc13.ord_rho]; exact pow_orderOf_eq_one rho
  have hmod : (fourGrp x₁ x₂).relIndex I % 3 = 1 :=
    relIndex_mod_three hV_le_I hρ3 hI_rho hV_rho hfix hQ
  have hVY : (fourGrp x₁ x₂).relIndex Y = 4 := by
    have h := Subgroup.relIndex_mul_card (fourGrp x₁ x₂) Y
    rw [inf_of_le_left hV_le_Y, l17_card_V hc13, l17_card_Y hc13] at h
    omega
  have hdvd : (fourGrp x₁ x₂).relIndex I ∣ 4 :=
    ⟨I.relIndex Y, by
      rw [Subgroup.relIndex_mul_relIndex (fourGrp x₁ x₂) I Y hV_le_I hI_le_Y, hVY]⟩
  have hcardI : Nat.card I = 4 * (fourGrp x₁ x₂).relIndex I := by
    have h := Subgroup.relIndex_mul_card (fourGrp x₁ x₂) I
    rw [inf_of_le_left hV_le_I, l17_card_V hc13] at h
    omega
  have hrel : (fourGrp x₁ x₂).relIndex I = 1 ∨ (fourGrp x₁ x₂).relIndex I = 4 := by
    have hle : (fourGrp x₁ x₂).relIndex I ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : (fourGrp x₁ x₂).relIndex I <;> simp_all
  have hne : I ≠ fourGrp x₁ x₂ := by
    intro hIV
    obtain ⟨m, hm, hmV⟩ := l18_exists_comm_tau_not_mem_V hc
    have hmI : m * tau * m⁻¹ * tau⁻¹ ∈ I := ⟨m, hm, rfl⟩
    exact hmV (hIV ▸ hmI)
  have hcases : I = fourGrp x₁ x₂ ∨ I = Y := by
    rcases hrel with h1 | h4
    · left
      have hcard : Nat.card I = 4 := by rw [hcardI, h1]
      exact (Subgroup.eq_of_le_of_card_ge hV_le_I (by rw [hcard, l17_card_V hc13])).symm
    · right
      have hcard : Nat.card I = 16 := by rw [hcardI, h4]
      apply Subgroup.eq_of_le_of_card_ge hI_le_Y
      rw [l17_card_Y hc13, hcard]
  have hIY : I = Y := hcases.resolve_left hne
  have hyI : y ∈ I := by rw [hIY]; exact hy
  obtain ⟨m, hm, hmy⟩ := hyI
  exact ⟨m, hm, hmy⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
