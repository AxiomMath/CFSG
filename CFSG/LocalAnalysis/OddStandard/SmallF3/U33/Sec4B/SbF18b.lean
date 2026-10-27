module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbF18a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma l18_sq_of_conj {a m : G} (ha2 : a * a = 1) (ht2 : t * t = 1)
    (hconj : a * t * a⁻¹ = t * tau) :
    (t * (m * a)) * (t * (m * a)) = (t * m * t⁻¹) * tau * (a * m * a⁻¹) := by
  have h1 : a * t = (t * tau) * a := by
    have h := congrArg (fun z => z * a) hconj
    simpa [mul_assoc] using h
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  calc (t * (m * a)) * (t * (m * a)) = (t * m) * (a * t) * (m * a) := by group
    _ = (t * m) * ((t * tau) * a) * (m * a) := by rw [h1]
    _ = (t * m * t⁻¹) * tau * (a * m * a⁻¹) := by rw [ht_inv, ha_inv]; group

private lemma l18_F3_om_contra (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮)
    (hXi : tau ∈ ctxXi t tau x₁ x₂ rho) (hom_t : om * t * om⁻¹ = t * tau)
    (htau_not : tau ∉ zpowers t) : False := by
  have htau_cl : tau ∈ closure ({t, om} : Set G) := by
    have h : tau = t⁻¹ * om * t * om⁻¹ := by
      calc tau = t⁻¹ * (t * tau) := by group
        _ = t⁻¹ * (om * t * om⁻¹) := by rw [hom_t]
        _ = t⁻¹ * om * t * om⁻¹ := by group
    rw [h]
    exact mul_mem (mul_mem (mul_mem (inv_mem (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp)))
      (inv_mem (Subgroup.subset_closure (by simp)))
  have hbot : tau ∈ (⊥ : Subgroup G) := by
    have hmem := Subgroup.mem_inf.mpr ⟨hXi, htau_cl⟩
    rwa [l18_Xi_cap_tom hc] at hmem
  have h1 : tau = 1 := Subgroup.mem_bot.mp hbot
  exact htau_not (by rw [h1]; exact Subgroup.one_mem _)

theorem l18_F3 (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {e : G}
    (he : e ∈ ctxCY t tau x₁ x₂ rho) (h2 : (t * e) * (t * e) = 1) :
    ∃ x ∈ ctxCY t tau x₁ x₂ rho, t * e = x * t * x⁻¹ := by
  obtain ⟨m, hm, a, ha, rfl⟩ := (l18_mem_C hc).mp he
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc.toCtx13
  obtain ⟨htK, htauK, homK, hlamK, hrhoK⟩ := l17_mem_K hc.toCtx13
  have ht2' : t * t = 1 := by rwa [pow_two] at ht2
  have hτ2' : tau * tau = 1 := by rwa [pow_two] at htau2
  have hom2' : om * om = 1 := by rwa [pow_two] at hom2
  have hcomm : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 ht_tau hom_t
  have hlist := (mem_closure_pair_of_invol (a := tau) (b := om) hτ2' hom2' hcomm.symm).mp ha
  have haa : a * a = 1 := by
    rcases hlist with rfl | rfl | rfl | rfl
    · simp
    · exact hτ2'
    · exact hom2'
    · calc (tau * om) * (tau * om) = tau * (om * tau) * om := by group
        _ = tau * (tau * om) * om := by rw [hcomm]
        _ = (tau * tau) * (om * om) := by group
        _ = 1 := by rw [hτ2', hom2', one_mul]
  have haK : a ∈ ctxK t tau x₁ x₂ rho := by
    rcases hlist with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact htauK
    · exact homK
    · exact (ctxK t tau x₁ x₂ rho).mul_mem htauK homK
  have hτ_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right hτ2'
  rcases hlist with h1 | hτ | hom | htom
  ·
    subst a
    have h2m : (t * m) * (t * m) = 1 := by simpa using h2
    obtain ⟨p, hp, hpe⟩ := l18_fl_t hc hm h2m
    exact ⟨p, l18_Xi_le_C hc hp, by simpa using hpe⟩
  ·
    subst a
    have hm'' : tau * m * tau⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
      (l18_Xi_normal hc.toCtx13).2 tau htauK m hm
    have hgx : (t * tau) * (tau * m * tau⁻¹) = t * (m * tau) := by
      calc (t * tau) * (tau * m * tau⁻¹)
          = t * (tau * tau) * m * tau := by rw [hτ_inv]; group
        _ = t * m * tau := by rw [hτ2']; group
        _ = t * (m * tau) := by group
    have hx2 : ((t * tau) * (tau * m * tau⁻¹)) * ((t * tau) * (tau * m * tau⁻¹)) = 1 := by
      rw [hgx]; exact h2
    obtain ⟨p, hp, hpe⟩ := l18_fl_ttau hc hm'' hx2
    have hconj : p * (t * tau) * p⁻¹ = (p * om) * t * (p * om)⁻¹ := by
      rw [hom_t.symm]; group
    refine ⟨p * om, ?_, ?_⟩
    · have homC : om ∈ ctxCY t tau x₁ x₂ rho :=
        l18_QA_le_C hc.toCtx13 (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
      exact (ctxCY t tau x₁ x₂ rho).mul_mem (l18_Xi_le_C hc hp) homC
    · calc t * (m * tau) = (t * tau) * (tau * m * tau⁻¹) := hgx.symm
        _ = p * (t * tau) * p⁻¹ := hpe
        _ = (p * om) * t * (p * om)⁻¹ := hconj
  ·
    subst a
    exfalso
    have hsq := l18_sq_of_conj (a := om) (m := m) hom2' ht2' hom_t
    have hzero : (t * m * t⁻¹) * tau * (om * m * om⁻¹) = 1 := by rw [← hsq]; exact h2
    have hprod : (t * m * t⁻¹)⁻¹ * (om * m * om⁻¹)⁻¹ = tau := by
      have h1' : tau = (t * m * t⁻¹)⁻¹ *
          ((t * m * t⁻¹) * tau * (om * m * om⁻¹)) * (om * m * om⁻¹)⁻¹ := by group
      rw [hzero, mul_one] at h1'
      exact h1'.symm
    have htm : t * m * t⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
      (l18_Xi_normal hc.toCtx13).2 t htK m hm
    have homm : om * m * om⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
      (l18_Xi_normal hc.toCtx13).2 om homK m hm
    have hXi0 : (t * m * t⁻¹)⁻¹ * (om * m * om⁻¹)⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
      (ctxXi t tau x₁ x₂ rho).mul_mem
        ((ctxXi t tau x₁ x₂ rho).inv_mem htm) ((ctxXi t tau x₁ x₂ rho).inv_mem homm)
    have hXi : tau ∈ ctxXi t tau x₁ x₂ rho := by
      rw [hprod] at hXi0
      exact hXi0
    exact l18_F3_om_contra hc hXi hom_t htau_not
  ·
    subst a
    exfalso
    have hconj : (tau * om) * t * (tau * om)⁻¹ = t * tau := by
      calc (tau * om) * t * (tau * om)⁻¹
          = tau * (om * t * om⁻¹) * tau⁻¹ := by group
        _ = tau * (t * tau) * tau⁻¹ := by rw [hom_t]
        _ = (tau * t) * (tau * tau) := by rw [hτ_inv]; group
        _ = (t * tau) * 1 := by rw [← ht_tau, hτ2']
        _ = t * tau := by rw [mul_one]
    have hsq := l18_sq_of_conj (a := tau * om) (m := m) haa ht2' hconj
    have hzero : (t * m * t⁻¹) * tau * ((tau * om) * m * (tau * om)⁻¹) = 1 := by
      rw [← hsq]; exact h2
    have hprod : (t * m * t⁻¹)⁻¹ * ((tau * om) * m * (tau * om)⁻¹)⁻¹ = tau := by
      have h1' : tau = (t * m * t⁻¹)⁻¹ *
          ((t * m * t⁻¹) * tau * ((tau * om) * m * (tau * om)⁻¹)) *
          ((tau * om) * m * (tau * om)⁻¹)⁻¹ := by group
      rw [hzero, mul_one] at h1'
      exact h1'.symm
    have htm : t * m * t⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
      (l18_Xi_normal hc.toCtx13).2 t htK m hm
    have homm : (tau * om) * m * (tau * om)⁻¹ ∈ ctxXi t tau x₁ x₂ rho :=
      (l18_Xi_normal hc.toCtx13).2 (tau * om)
        ((ctxK t tau x₁ x₂ rho).mul_mem htauK homK) m hm
    have hXi0 : (t * m * t⁻¹)⁻¹ * ((tau * om) * m * (tau * om)⁻¹)⁻¹ ∈
        ctxXi t tau x₁ x₂ rho :=
      (ctxXi t tau x₁ x₂ rho).mul_mem
        ((ctxXi t tau x₁ x₂ rho).inv_mem htm) ((ctxXi t tau x₁ x₂ rho).inv_mem homm)
    have hXi : tau ∈ ctxXi t tau x₁ x₂ rho := by
      rw [hprod] at hXi0
      exact hXi0
    exact l18_F3_om_contra hc hXi hom_t htau_not

theorem l18_F2 (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) (g : G) {e : G}
    (he : e ∈ ctxCY t tau x₁ x₂ rho) : g * t * g⁻¹ ≠ lam * e := by
  intro hge
  obtain ⟨p, hpXi, a, haCl, rfl⟩ := (l18_mem_C hc).mp he
  obtain ⟨ht2, ht1, hom2, htau2, htau_not, ht_tau, hom_t⟩ := ctx13_relations hc.toCtx13
  have hom_tau : om * tau = tau * om := om_tau_comm ht2 hom2 htau2 ht_tau hom_t
  have htau_om : tau * om = om * tau := hom_tau.symm
  have htau2' : tau * tau = 1 := by rw [← pow_two]; exact htau2
  have hom2' : om * om = 1 := by rw [← pow_two]; exact hom2
  have ht2' : t * t = 1 := by rw [← pow_two]; exact ht2
  have ha_cases := (mem_closure_pair_of_invol htau2' hom2' htau_om).mp haCl
  obtain ⟨htK, htauK, homK, hlamK, hrhoK⟩ := l17_mem_K hc.toCtx13
  have haK : a ∈ ctxK t tau x₁ x₂ rho := by
    rcases ha_cases with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact htauK
    · exact homK
    · exact (ctxK t tau x₁ x₂ rho).mul_mem htauK homK
  have haInvK : a⁻¹ ∈ ctxK t tau x₁ x₂ rho := (ctxK t tau x₁ x₂ rho).inv_mem haK
  have hxXi : a⁻¹ * p * a ∈ ctxXi t tau x₁ x₂ rho := by
    have := (l18_Xi_normal hc.toCtx13).2 a⁻¹ haInvK p hpXi
    simpa using this
  have hg0x : (lam * a) * (a⁻¹ * p * a) = g * t * g⁻¹ := by
    calc (lam * a) * (a⁻¹ * p * a) = lam * p * a := by group
      _ = lam * (p * a) := by group
      _ = g * t * g⁻¹ := hge.symm
  have hu2 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2']; group
  have hxsq : ((lam * a) * (a⁻¹ * p * a)) * ((lam * a) * (a⁻¹ * p * a)) = 1 := by
    rw [hg0x]; exact hu2
  obtain ⟨p', hp'Xi, hp'eq⟩ := l18_fl_lam hc haCl hxXi hxsq
  have h1 : p' * (lam * a) * p'⁻¹ = g * t * g⁻¹ := by rw [← hp'eq, hg0x]
  have hconj : (p'⁻¹ * g) * t * (p'⁻¹ * g)⁻¹ = lam * a := by
    calc (p'⁻¹ * g) * t * (p'⁻¹ * g)⁻¹ = p'⁻¹ * (g * t * g⁻¹) * p' := by group
      _ = p'⁻¹ * (p' * (lam * a) * p'⁻¹) * p' := by rw [← h1]
      _ = lam * a := by group
  obtain ⟨B, hclB, hBe, hB32⟩ := l17_E32 hc.toCtx13
  have hlamB : lam ∈ closure ({tau, om, lam} : Set G) := Subgroup.subset_closure (by simp)
  have haB : a ∈ closure ({tau, om, lam} : Set G) :=
    Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      tauto) haCl
  have hlam_a_B : lam * a ∈ B := B.mul_mem (hclB hlamB) (hclB haB)
  have hBcent : B ≤ centralizer ({lam * a} : Set G) := by
    intro x hx
    haveI : IsMulCommutative ↥B := hBe.1
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥B) (⟨lam * a, hlam_a_B⟩ : ↥B)))
  have hAc : B ≤ centralizer ({(p'⁻¹ * g) * t * (p'⁻¹ * g)⁻¹} : Set G) := by
    rw [hconj]
    exact hBcent
  have hbound : Nat.card B ≤ 16 :=
    c17_card_elemAbelian_conj_le (hc := hc.toCtx13.toCtx11.toCtx10) (g := p'⁻¹ * g) hAc hBe
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
