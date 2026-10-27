module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e6a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13e_x_AN_mod_N (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) {x : G} (hxL : x ∈ q13L t tau x₁ x₂ rho om)
    (hxV : ∀ v ∈ fourGrp x₁ x₂, x * v = v * x) :
    ∀ a ∈ q13AN t tau x₁ x₂ rho, x * a * x⁻¹ * a⁻¹ ∈ ctxN tau x₁ x₂ := by
  intro a ha
  have haP : a ∈ q13P t tau x₁ x₂ rho om := q13e_AN_le_P h ha
  have ha2V : a * a ∈ fourGrp x₁ x₂ := by
    have h2 := ((q13e_mem_AN h hD).mp ha).2
    simpa [pow_two] using h2
  have hcP : x * a * x⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    q13d_P_normal_L h hD.A_cent x hxL a haP
  have hmem : x * a * x⁻¹ * a⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
    mul_mem hcP (inv_mem haP)
  have hc2 : (x * a * x⁻¹) * (x * a * x⁻¹) = a * a := by
    calc (x * a * x⁻¹) * (x * a * x⁻¹)
        = x * (a * a) * x⁻¹ := by group
      _ = (a * a) * x * x⁻¹ := by rw [hxV (a * a) ha2V]
      _ = a * a := by group
  have hsq : (x * a * x⁻¹ * a⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    have hcomm : (x * a * x⁻¹) * a⁻¹ = a⁻¹ * (x * a * x⁻¹) :=
      q13d_P_comm h hD.A_cent _ hcP _ (inv_mem haP)
    calc (x * a * x⁻¹ * a⁻¹) * (x * a * x⁻¹ * a⁻¹)
        = (x * a * x⁻¹) * (a⁻¹ * (x * a * x⁻¹)) * a⁻¹ := by group
      _ = (x * a * x⁻¹) * ((x * a * x⁻¹) * a⁻¹) * a⁻¹ := by rw [← hcomm]
      _ = (x * a * x⁻¹) * (x * a * x⁻¹) * (a⁻¹ * a⁻¹) := by group
      _ = (a * a) * (a⁻¹ * a⁻¹) := by rw [hc2]
      _ = 1 := by group
  exact q13d_P_sq_eq_one_mem_N h hD.A_cent _ hmem hsq

theorem q13e_comm_x_B (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) {x : G}
    (hxL : x ∈ q13L t tau x₁ x₂ rho om) (hxV : ∀ v ∈ fourGrp x₁ x₂, x * v = v * x)
    (hx2 : x * x ∈ q13P t tau x₁ x₂ rho om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om, x * b * x⁻¹ * b⁻¹ ∈ q13P t tau x₁ x₂ rho om := by
  intro b hb
  have hbL : b ∈ q13L t tau x₁ x₂ rho om := (Subgroup.mem_inf.mp hb).1
  have hb'B : x * b * x⁻¹ ∈ q13B t tau x₁ x₂ rho om := hD.B_normal.2 x hxL b hb
  have hw : ⁅t, b⁆ ∈ q13AN t tau x₁ x₂ rho := q13e_kap_mem_AN h hB hC hD b hb
  have hwP : ⁅t, b⁆ ∈ q13P t tau x₁ x₂ rho om := q13e_kap_mem_P h hD b hbL
  have hb'P : ⁅t, x * b * x⁻¹⁆ ∈ q13P t tau x₁ x₂ rho om :=
    q13e_kap_mem_P h hD (x * b * x⁻¹) (mul_mem (mul_mem hxL hbL) (inv_mem hxL))
  have hb'N : ⁅t, x * b * x⁻¹⁆ * (⁅t, b⁆)⁻¹ ∈ ctxN tau x₁ x₂ := by
    have h1 := q13e_kap_conj h hD x hxL b hb
    have h2 := mul_mem h1 (q13e_x_AN_mod_N h hD hxL hxV (⁅t, b⁆) hw)
    have heq : (⁅t, x * b * x⁻¹⁆ * (x * ⁅t, b⁆ * x⁻¹)⁻¹) *
        (x * ⁅t, b⁆ * x⁻¹ * (⁅t, b⁆)⁻¹) = ⁅t, x * b * x⁻¹⁆ * (⁅t, b⁆)⁻¹ := by
      group
    rwa [heq] at h2
  have hbinvN : ⁅t, b⁻¹⁆ * ⁅t, b⁆ ∈ ctxN tau x₁ x₂ := by
    have h1 := q13e_kap_mul_B h hD b hb b⁻¹ (inv_mem hb)
    have hk1 : ⁅t, b * b⁻¹⁆ = 1 := by rw [mul_inv_cancel, commutatorElement_one_right]
    rw [hk1, one_mul] at h1
    have h1' : ⁅t, b⁆ * ⁅t, b⁻¹⁆ ∈ ctxN tau x₁ x₂ := by simpa using inv_mem h1
    have hcomm : ⁅t, b⁆ * ⁅t, b⁻¹⁆ = ⁅t, b⁻¹⁆ * ⁅t, b⁆ :=
      q13d_P_comm h hD.A_cent _ hwP _ (q13e_kap_mem_P h hD b⁻¹ (inv_mem hbL))
    rwa [hcomm] at h1'
  have hprod : ⁅t, b⁻¹⁆ * ⁅t, x * b * x⁻¹⁆ ∈ ctxN tau x₁ x₂ := by
    have h1 := mul_mem hbinvN hb'N
    have hcomm : ⁅t, b⁆ * ⁅t, x * b * x⁻¹⁆ = ⁅t, x * b * x⁻¹⁆ * ⁅t, b⁆ :=
      q13d_P_comm h hD.A_cent _ hwP _ hb'P
    have heq : (⁅t, b⁻¹⁆ * ⁅t, b⁆) * (⁅t, x * b * x⁻¹⁆ * (⁅t, b⁆)⁻¹) =
        ⁅t, b⁻¹⁆ * ⁅t, x * b * x⁻¹⁆ := by
      rw [show (⁅t, b⁻¹⁆ * ⁅t, b⁆) * (⁅t, x * b * x⁻¹⁆ * (⁅t, b⁆)⁻¹) =
          ⁅t, b⁻¹⁆ * (⁅t, b⁆ * ⁅t, x * b * x⁻¹⁆) * (⁅t, b⁆)⁻¹ by group, hcomm]
      group
    rwa [heq] at h1
  set e : G := b⁻¹ * (x * b * x⁻¹) with he
  have heB : e ∈ q13B t tau x₁ x₂ rho om := by
    rw [he]
    exact mul_mem (inv_mem hb) hb'B
  have heN : ⁅t, e⁆ ∈ ctxN tau x₁ x₂ := by
    have h1 := q13e_kap_mul_B h hD b⁻¹ (inv_mem hb) (x * b * x⁻¹) hb'B
    have h2 := mul_mem h1 hprod
    have heq : (⁅t, b⁻¹ * (x * b * x⁻¹)⁆ *
          (⁅t, b⁻¹⁆ * ⁅t, x * b * x⁻¹⁆)⁻¹) *
          (⁅t, b⁻¹⁆ * ⁅t, x * b * x⁻¹⁆) = ⁅t, e⁆ := by
      rw [he]
      group
    rwa [heq] at h2
  have heE0 : e ∈ q13E0 t tau x₁ x₂ rho om := (q13e_kap_N_iff h hB hD e heB).1 heN
  have hbe : b * e = x * b * x⁻¹ := by rw [he]; group
  rcases (q13d_mem_E0 h hD.A_cent).1 heE0 with heP | ⟨p, hp, hep⟩
  · have heq : x * b * x⁻¹ * b⁻¹ = b * e * b⁻¹ := by
      rw [← hbe]
    rw [heq]
    exact q13d_P_normal_L h hD.A_cent b hbL e heP
  · exfalso
    have hgL : x * b ∈ q13L t tau x₁ x₂ rho om := mul_mem hxL hbL
    have hx2' : p * (x * x) ∈ q13P t tau x₁ x₂ rho om := mul_mem hp hx2
    have hbp : b * (p * (x * x)) * b⁻¹ ∈ q13P t tau x₁ x₂ rho om :=
      q13d_P_normal_L h hD.A_cent b hbL _ hx2'
    have hbb : b * b ∈ q13P t tau x₁ x₂ rho om := q13e_B_sq_mem_P h hB hC hD b hb
    have hPf : ⁅t, b⁆ * (b * (p * (x * x)) * b⁻¹) * (b * b) ∈
        q13P t tau x₁ x₂ rho om := mul_mem (mul_mem hwP hbp) hbb
    have hbt : b * t = t * ⁅t, b⁆ * b := by
      have h1 := q13e_conj_t h b
      rw [← h1]
      group
    have hgg : (x * b) * (x * b) =
        t * (⁅t, b⁆ * (b * (p * (x * x)) * b⁻¹) * (b * b)) := by
      calc (x * b) * (x * b)
          = (x * b * x⁻¹) * (x * x) * b := by group
        _ = (b * e) * (x * x) * b := by rw [← hbe]
        _ = b * (t * p) * (x * x) * b := by rw [hep]
        _ = b * t * (p * (x * x)) * b := by group
        _ = t * ⁅t, b⁆ * b * (p * (x * x)) * b := by rw [hbt]
        _ = t * (⁅t, b⁆ * (b * (p * (x * x)) * b⁻¹) * (b * b)) := by group
    exact q13e_no_sq h hD (x * b) hgL
      (⁅t, b⁆ * (b * (p * (x * x)) * b⁻¹) * (b * b)) hPf hgg

theorem q13e_comm_x₁₂_B (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ b ∈ q13B t tau x₁ x₂ rho om,
      x₁ * b * x₁⁻¹ * b⁻¹ ∈ q13P t tau x₁ x₂ rho om ∧
      x₂ * b * x₂⁻¹ * b⁻¹ ∈ q13P t tau x₁ x₂ rho om := by
  intro b hb
  obtain ⟨hx₁L, hx₂L⟩ := q13e_x_mem_L h hD
  have hx₁V : ∀ v ∈ fourGrp x₁ x₂, x₁ * v = v * x₁ := fun v hv => (q13e_x_cent_V h v hv).1
  have hx₂V : ∀ v ∈ fourGrp x₁ x₂, x₂ * v = v * x₂ := fun v hv => (q13e_x_cent_V h v hv).2
  obtain ⟨hx₁sqV, hx₂sqV⟩ := q13e_x_sq_mem_V h
  have hx₁2 : x₁ * x₁ ∈ q13P t tau x₁ x₂ rho om := by
    have hm : x₁ ^ 2 ∈ q13A t tau x₁ x₂ rho := q13a_V_le_A h hx₁sqV
    rw [pow_two] at hm
    exact q13d_A_le_P h hm
  have hx₂2 : x₂ * x₂ ∈ q13P t tau x₁ x₂ rho om := by
    have hm : x₂ ^ 2 ∈ q13A t tau x₁ x₂ rho := q13a_V_le_A h hx₂sqV
    rw [pow_two] at hm
    exact q13d_A_le_P h hm
  exact ⟨q13e_comm_x_B h hB hC hD hx₁L hx₁V hx₁2 b hb,
    q13e_comm_x_B h hB hC hD hx₂L hx₂V hx₂2 b hb⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
