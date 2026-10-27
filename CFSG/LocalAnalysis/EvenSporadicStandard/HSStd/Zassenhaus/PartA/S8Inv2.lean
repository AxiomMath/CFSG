module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8F0

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section Elem

variable {G : Type*} [Group G]

theorem zpow_sq_one {x : G} (hx : x * x = 1) (n : ℤ) : x ^ n = 1 ∨ x ^ n = x := by
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul]
    have : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    rw [this, one_zpow]
  · right
    rw [zpow_add, zpow_mul]
    have : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    rw [this, one_zpow, one_mul, zpow_one]

end Elem

section Inv

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem F0_elem_cases (hb : PAB G L t E W z) (a : PA7 L t E z) (hd : a.dcase = DCase.d8) {f : G}
    (hf : f ∈ a.F₀) (hft : (f * t) * (f * t) = 1) : f = 1 ∨ f = a.ub := by
  obtain ⟨ho, hu1Cen, hu1J, htu1, hF0, hnot, -⟩ := a.d8_props hd
  have hsq : a.u₁ * a.u₁ = 1 := u1_sq a hd
  have hui : a.u₁⁻¹ = a.u₁ := inv_eq_of_mul_eq_one_right hsq
  have hu1ub : a.u₁ * a.ub = a.ub * a.u₁ := mem_Cen.1 hu1Cen
  have htt := hb.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hub2 := PA5.ub_sq a.toPA6.toPA5
  have hubne := PA5.ub_ne_one a.toPA6.toPA5
  have htub := PA5.t_ub a.toPA6.toPA5 hb
  have hu1t : a.u₁ * t * a.u₁ = t * a.ub := by
    have := congrArg Subtype.val (u1_conj_t hb a hd)
    simpa [tG, u1G, ubG, hui] using this
  have hsqt : (a.u₁ * t) * (a.u₁ * t) = a.ub := by
    calc (a.u₁ * t) * (a.u₁ * t) = (a.u₁ * t * a.u₁) * t := by simp only [mul_assoc]
      _ = (t * a.ub) * t := by rw [hu1t]
      _ = a.ub := by rw [mul_assoc, ← htub, ← mul_assoc, htt, one_mul]
  rw [hF0] at hf
  have hcomm : ∀ n ∈ zpowers a.ub, ∀ m ∈ zpowers a.u₁, n * m = m * n := by
    intro n hn m hm
    obtain ⟨i, rfl⟩ := hn
    obtain ⟨j, rfl⟩ := hm
    exact ((Commute.zpow_zpow (show Commute a.ub a.u₁ from hu1ub.symm) i j).eq)
  obtain ⟨n, hn, m, hm, rfl⟩ := exists_mul_of_mem_sup hcomm hf
  obtain ⟨i, rfl⟩ := hn
  obtain ⟨j, rfl⟩ := hm
  beta_reduce at hft ⊢
  rcases zpow_sq_one hub2 i with h1 | h1 <;> rcases zpow_sq_one hsq j with h2 | h2
  · left; rw [h1, h2, one_mul]
  · exfalso
    rw [h1, h2, one_mul] at hft
    exact hubne (hsqt.symm.trans hft)
  · right; rw [h1, h2, mul_one]
  · exfalso
    rw [h1, h2] at hft
    have e : (a.ub * a.u₁ * t) * (a.ub * a.u₁ * t) = (a.ub * a.ub) * ((a.u₁ * t) * (a.u₁ * t)) := by
      have c1 : a.u₁ * t * a.ub = a.ub * (a.u₁ * t) := by
        calc a.u₁ * t * a.ub = a.u₁ * (t * a.ub) := by rw [mul_assoc]
          _ = a.u₁ * (a.ub * t) := by rw [htub]
          _ = (a.u₁ * a.ub) * t := by rw [mul_assoc]
          _ = (a.ub * a.u₁) * t := by rw [hu1ub]
          _ = a.ub * (a.u₁ * t) := by rw [mul_assoc]
      calc (a.ub * a.u₁ * t) * (a.ub * a.u₁ * t)
          = a.ub * ((a.u₁ * t) * a.ub) * (a.u₁ * t) := by simp only [mul_assoc]
        _ = a.ub * (a.ub * (a.u₁ * t)) * (a.u₁ * t) := by rw [c1]
        _ = (a.ub * a.ub) * ((a.u₁ * t) * (a.u₁ * t)) := by simp only [mul_assoc]
    rw [e, hub2, one_mul, hsqt] at hft
    exact hubne hft

end Inv

section Inv2

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}
  (hb : PAB G L t E W z) (a : PA7 L t E z) {K : Subgroup ↥(Cen a.ub)} (hK : IsComponent K)
  (hcj : cj (tG hb a.toPA6.toPA5) K = K)
  (hall : ∀ K' : Subgroup ↥(Cen a.ub), IsComponent K' → K' = K)

include hb a hK hcj hall

theorem inv_layer : layer ↥(Cen a.ub) = K := by
  rw [layer_eq_of_orbit hb a.toPA6.toPA5 hK (fun K' h => Or.inl (hall K' h)), hcj, sup_idem]

theorem inv_E : GorensteinWalter.componentLayerOf (Cen a.ub) = K.map (Cen a.ub).subtype := by
  rw [componentLayerOf_eq, inv_layer hb a hK hcj hall]

theorem inv_cent_F0 (g : ↥(Cen a.ub)) (hg : ∀ k ∈ K, g * k = k * g) : (g : G) ∈ a.F₀ := by
  have hE : ∀ x ∈ GorensteinWalter.componentLayerOf (Cen a.ub), (g : G) * x = x * (g : G) := by
    intro x hx
    rw [inv_E hb a hK hcj hall] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact congrArg Subtype.val (hg k hk)
  exact PA7.cpe_le_F0 hb a g.2 (fun x hx => hE x (a.E₁_le hx))
    (a.CPE ⟨g.2, Subgroup.mem_centralizer_iff.2 fun x hx => (hE x hx).symm⟩)

end Inv2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
