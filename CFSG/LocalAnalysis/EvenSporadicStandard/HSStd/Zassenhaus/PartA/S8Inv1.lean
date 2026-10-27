module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S8Cpe

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section U1c

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem derivedIn_conj {A : Subgroup G} {x j : G} (hx : x ∈ A) (hj : j ∈ derivedIn A) :
    x * j * x⁻¹ ∈ derivedIn A := by
  obtain ⟨c, hc, rfl⟩ := hj
  have := Subgroup.Normal.conj_mem (inferInstance : (commutator ↥A).Normal) c hc ⟨x, hx⟩
  exact ⟨_, this, rfl⟩

theorem PA7.u1_comm_c (hb : PAB G L t E W z) (a : PA7 L t E z) (hd : a.dcase = DCase.d8) {c : G}
    (hct : c * t = t * c) (hcub : c * a.ub = a.ub * c) :
    a.u₁ * c * a.u₁⁻¹ * c⁻¹ = 1 ∨ a.u₁ * c * a.u₁⁻¹ * c⁻¹ = a.ub := by
  obtain ⟨ho, hu1Cen, hu1J, htu1, -⟩ := a.d8_props hd
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
  obtain ⟨v, hv, x, hx, rfl⟩ := PA5.cent_decomp hb a.toPA6.toPA5 hct hcub
  set c := v * x with hcdef
  have hJc : ∀ j ∈ derivedIn a.Abar, c⁻¹ * j * c ∈ derivedIn a.Abar := by
    intro j hj
    have hjA := derivedIn_le _ hj
    have hjv : j * v = v * j :=
      commute_Vsub (PA5.Abar_comm_t hb a.toPA6.toPA5 hjA) (PA5.Abar_comm_ub hb a.toPA6.toPA5 hjA)
        v hv
    have e : c⁻¹ * j * c = x⁻¹ * j * (x⁻¹)⁻¹ := by
      rw [inv_inv, hcdef, mul_inv_rev]
      calc x⁻¹ * v⁻¹ * j * (v * x) = x⁻¹ * (v⁻¹ * (j * v) * x) := by simp only [mul_assoc]
        _ = x⁻¹ * (v⁻¹ * (v * j) * x) := by rw [hjv]
        _ = x⁻¹ * j * x := by group
    rw [e]
    exact derivedIn_conj (a.Abar.inv_mem hx) hj
  have hwJ : ∀ j ∈ derivedIn a.Abar,
      (a.u₁ * c * a.u₁⁻¹ * c⁻¹) * j = j * (a.u₁ * c * a.u₁⁻¹ * c⁻¹) := by
    intro j hj
    have hj' := hJc j hj
    have h1 : j * a.u₁ = a.u₁ * j := Subgroup.mem_centralizer_iff.1 hu1J j hj
    have h2 : (c⁻¹ * j * c) * a.u₁ = a.u₁ * (c⁻¹ * j * c) :=
      Subgroup.mem_centralizer_iff.1 hu1J _ hj'
    rw [hui]
    calc a.u₁ * c * a.u₁ * c⁻¹ * j
        = a.u₁ * c * (a.u₁ * (c⁻¹ * j * c)) * c⁻¹ := by group
      _ = a.u₁ * c * ((c⁻¹ * j * c) * a.u₁) * c⁻¹ := by rw [h2]
      _ = a.u₁ * j * c * a.u₁ * c⁻¹ := by group
      _ = (a.u₁ * j) * c * a.u₁ * c⁻¹ := by rfl
      _ = (j * a.u₁) * c * a.u₁ * c⁻¹ := by rw [h1]
      _ = j * (a.u₁ * c * a.u₁ * c⁻¹) := by group
  have hCub : ∀ y : G, y * a.ub = a.ub * y → y⁻¹ * a.ub = a.ub * y⁻¹ := fun y h => by
    have := congrArg (fun q => y⁻¹ * q * y⁻¹) h
    simpa [mul_assoc] using this.symm
  have hwt : (a.u₁ * c * a.u₁⁻¹ * c⁻¹) * t = t * (a.u₁ * c * a.u₁⁻¹ * c⁻¹) := by
    have e : t * (a.u₁ * c * a.u₁⁻¹ * c⁻¹) * t⁻¹ = a.u₁ * c * a.u₁⁻¹ * c⁻¹ := by
      have e1 : t * (a.u₁ * c * a.u₁⁻¹ * c⁻¹) * t⁻¹ =
          (t * a.u₁ * t⁻¹) * (t * c * t⁻¹) * (t * a.u₁ * t⁻¹)⁻¹ * (t * c * t⁻¹)⁻¹ := by group
      rw [e1, htu1, show t * c * t⁻¹ = c by rw [← hct]; group]
      have hX : Commute a.ub (a.u₁ * c * a.u₁⁻¹) := by
        have h1 : Commute a.ub a.u₁ := hu1ub.symm
        have h2 : Commute a.ub c := hcub.symm
        exact (h1.mul_right h2).mul_right h1.inv_right
      calc a.ub * a.u₁ * c * (a.ub * a.u₁)⁻¹ * c⁻¹
          = (a.ub * (a.u₁ * c * a.u₁⁻¹) * a.ub⁻¹) * c⁻¹ := by group
        _ = (a.u₁ * c * a.u₁⁻¹) * c⁻¹ := by rw [hX.mul_inv_cancel]
    exact (mul_inv_eq_iff_eq_mul.1 e).symm
  have hV := PA5.cent_t_J hb a.toPA6.toPA5 hwt hwJ
  rw [mem_Vsub_iff htt hub2 htub] at hV
  have hinv : a.u₁ * (a.u₁ * c * a.u₁⁻¹ * c⁻¹) * a.u₁ = (a.u₁ * c * a.u₁⁻¹ * c⁻¹)⁻¹ := by
    rw [hui]
    have h3 : a.u₁ * (a.u₁ * c * a.u₁ * c⁻¹) * a.u₁ = c * a.u₁ * c⁻¹ * a.u₁ := by
      calc a.u₁ * (a.u₁ * c * a.u₁ * c⁻¹) * a.u₁ = (a.u₁ * a.u₁) * c * a.u₁ * c⁻¹ * a.u₁ := by
            simp only [mul_assoc]
        _ = c * a.u₁ * c⁻¹ * a.u₁ := by rw [hsq, one_mul]
    rw [h3]
    have h4 : (a.u₁ * c * a.u₁ * c⁻¹)⁻¹ = c * a.u₁⁻¹ * c⁻¹ * a.u₁⁻¹ := by group
    rw [h4, hui]
  rcases hV with h | h | h | h
  · exact Or.inl h
  · exfalso
    rw [h, hu1t, hti] at hinv
    exact hubne (mul_left_cancel (by rw [mul_one]; exact hinv))
  · exact Or.inr h
  · exfalso
    rw [h] at hinv
    have h1 : a.u₁ * (t * a.ub) * a.u₁ = t := by
      calc a.u₁ * (t * a.ub) * a.u₁ = a.u₁ * t * (a.ub * a.u₁) := by simp only [mul_assoc]
        _ = a.u₁ * t * (a.u₁ * a.ub) := by rw [hu1ub]
        _ = (a.u₁ * t * a.u₁) * a.ub := by simp only [mul_assoc]
        _ = t * a.ub * a.ub := by rw [hu1t]
        _ = t := by rw [mul_assoc, hub2, mul_one]
    have h2 : (t * a.ub)⁻¹ = t * a.ub := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hub2, hti]; exact htub.symm
    rw [h1, h2] at hinv
    exact hubne (mul_left_cancel (by rw [mul_one]; exact hinv.symm))

end U1c

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
