module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d6e1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d4b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d5c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d4a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private theorem q13d_t_mem_L (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t ∈ q13L t tau x₁ x₂ rho om := by
  rw [q13L]
  exact Subgroup.le_normalizer (q13d_t_mem_E0 h)

private theorem q13d_om_mem_L (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om ∈ q13L t tau x₁ x₂ rho om := by
  rw [q13L]
  exact Subgroup.le_normalizer (q13d_om_mem_E0 h)

private theorem q13d_t_conj_om (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * om * t⁻¹ = om * tau := by
  have hominv : om⁻¹ = om := inv_eq_of_mul_eq_one_right h.om_sq
  have h1 : om * t * om = t * tau := by
    have := h.t_om
    rwa [hominv] at this
  have h2 : t * om = om * t * tau := by
    calc t * om = (om * om) * t * om := by rw [h.om_sq, one_mul]
      _ = om * (om * t * om) := by group
      _ = om * (t * tau) := by rw [h1]
      _ = om * t * tau := by group
  have ht2 : t * t = 1 := q13a_t_mul_self h
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rw [htinv]
  calc t * om * t = (om * t * tau) * t := by rw [h2]
    _ = om * (t * tau * t) := by group
    _ = om * ((tau * t) * t) := by rw [(q13a_t_comm h).2.2]
    _ = om * (tau * (t * t)) := by rw [mul_assoc]
    _ = om * tau := by rw [ht2, mul_one]

private theorem q13d_t_gam_pow_mem (h : Q13Om t L S x₁ x₂ lam rho tau om) {n : ℕ}
    (hn : n < 4) :
    t * (t * om) ^ n ∈ ({t, t * tau, om, om * tau} : Set G) := by
  interval_cases n
  · rw [pow_zero, mul_one]
    simp
  · rw [pow_one]
    have h1 : t * (t * om) = om := by rw [← mul_assoc, q13a_t_mul_self h, one_mul]
    rw [h1]
    simp
  · rw [q13d_gam_sq h]
    simp
  · have h3 : (t * om) ^ 3 = tau * (t * om) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_one, q13d_gam_sq h]
    rw [h3]
    have h4 : t * (tau * (t * om)) = om * tau := by
      calc t * (tau * (t * om)) = (t * tau) * (t * om) := by group
        _ = (tau * t) * (t * om) := by rw [(q13a_t_comm h).2.2]
        _ = tau * (t * (t * om)) := by group
        _ = tau * ((t * t) * om) := by group
        _ = tau * om := by rw [q13a_t_mul_self h, one_mul]
        _ = om * tau := (q13a_om_comm h).1.symm
    rw [h4]
    simp

private theorem q13d_t_ne_ttau (h : Q13Om t L S x₁ x₂ lam rho tau om) : t ≠ t * tau := by
  intro heq
  refine q13b_tau_ne_one h ?_
  calc tau = t⁻¹ * (t * tau) := by group
    _ = t⁻¹ * t := by rw [← heq]
    _ = 1 := by group

private theorem q13d_t_ne_om (h : Q13Om t L S x₁ x₂ lam rho tau om) : t ≠ om := by
  intro heq
  apply h.om_not_mem
  rw [← heq]
  exact Subgroup.subset_closure (by simp)

private theorem q13d_t_ne_omtau (h : Q13Om t L S x₁ x₂ lam rho tau om) : t ≠ om * tau := by
  intro heq
  apply h.om_not_mem
  have hom : om = t * tau := by
    calc om = (om * tau) * tau := by rw [mul_assoc, q13a_tau_mul_self h, mul_one]
      _ = t * tau := by rw [← heq]
  rw [hom]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

private theorem q13d_ttau_ne_om (h : Q13Om t L S x₁ x₂ lam rho tau om) : t * tau ≠ om := by
  intro heq
  apply h.om_not_mem
  rw [← heq]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))

private theorem q13d_ttau_ne_omtau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * tau ≠ om * tau := by
  intro heq
  apply q13d_t_ne_om h
  calc t = t * tau * tau := by rw [mul_assoc, q13a_tau_mul_self h, mul_one]
    _ = om * tau * tau := by rw [heq]
    _ = om := by rw [mul_assoc, q13a_tau_mul_self h, mul_one]

private theorem q13d_om_ne_omtau (h : Q13Om t L S x₁ x₂ lam rho tau om) : om ≠ om * tau := by
  intro heq
  refine q13b_tau_ne_one h ?_
  calc tau = om⁻¹ * (om * tau) := by group
    _ = om⁻¹ * om := by rw [← heq]
    _ = 1 := by group

private theorem q13d_ncard_B (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ({t, t * tau, om, om * tau} : Set G).ncard = 4 := by
  have h1 : t ∉ ({t * tau, om, om * tau} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨q13d_t_ne_ttau h, q13d_t_ne_om h, q13d_t_ne_omtau h⟩
  have h2 : t * tau ∉ ({om, om * tau} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨q13d_ttau_ne_om h, q13d_ttau_ne_omtau h⟩
  have h3 : om ∉ ({om * tau} : Set G) := by
    simpa using q13d_om_ne_omtau h
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_insert_of_notMem h3, Set.ncard_singleton]

private theorem q13d_ncard_s (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ({t, t * tau} : Set G).ncard = 2 :=
  Set.ncard_pair (q13d_t_ne_ttau h)

private theorem q13d_t_mem_fix (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t ∈ conjIn (q13L t tau x₁ x₂ rho om) t ∩ {u : G | rho * u * rho⁻¹ = u} := by
  refine ⟨⟨1, Subgroup.one_mem _, by group⟩, ?_⟩
  show rho * t * rho⁻¹ = t
  rw [← (q13a_t_comm h).2.1]
  group

private theorem q13d_ttau_mem_fix (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * tau ∈ conjIn (q13L t tau x₁ x₂ rho om) t ∩ {u : G | rho * u * rho⁻¹ = u} := by
  refine ⟨⟨om, q13d_om_mem_L h, h.t_om⟩, ?_⟩
  show rho * (t * tau) * rho⁻¹ = t * tau
  have ht : rho * t * rho⁻¹ = t := by
    rw [← (q13a_t_comm h).2.1]
    group
  have hta : rho * tau * rho⁻¹ = tau := by
    rw [h.c11.tau_rho.symm]
    group
  calc rho * (t * tau) * rho⁻¹ = (rho * t * rho⁻¹) * (rho * tau * rho⁻¹) := by group
    _ = t * tau := by rw [ht, hta]

private theorem q13d_om_mem_T_iff (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om ∈ conjIn (q13L t tau x₁ x₂ rho om) t ↔
      om * tau ∈ conjIn (q13L t tau x₁ x₂ rho om) t := by
  have htL : t ∈ q13L t tau x₁ x₂ rho om := q13d_t_mem_L h
  constructor
  · rintro ⟨k, hk, hkconj⟩
    refine ⟨t * k, Subgroup.mul_mem _ htL hk, ?_⟩
    calc (t * k) * t * (t * k)⁻¹ = t * (k * t * k⁻¹) * t⁻¹ := by group
      _ = t * om * t⁻¹ := by rw [hkconj]
      _ = om * tau := q13d_t_conj_om h
  · rintro ⟨k, hk, hkconj⟩
    refine ⟨t⁻¹ * k, Subgroup.mul_mem _ (Subgroup.inv_mem _ htL) hk, ?_⟩
    calc (t⁻¹ * k) * t * (t⁻¹ * k)⁻¹ = t⁻¹ * (k * t * k⁻¹) * t := by group
      _ = t⁻¹ * (om * tau) * t := by rw [hkconj]
      _ = om := by rw [← q13d_t_conj_om h]; group

private theorem q13d_om_mem_fix_iff (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om ∈ conjIn (q13L t tau x₁ x₂ rho om) t ∩ {u : G | rho * u * rho⁻¹ = u} ↔
      om * tau ∈ conjIn (q13L t tau x₁ x₂ rho om) t ∩
        {u : G | rho * u * rho⁻¹ = u} := by
  have homfix : rho * om * rho⁻¹ = om := by
    rw [← (q13a_om_comm h).2.1]
    group
  have htaufix : rho * tau * rho⁻¹ = tau := by
    rw [h.c11.tau_rho.symm]
    group
  have homtaufix : rho * (om * tau) * rho⁻¹ = om * tau := by
    calc rho * (om * tau) * rho⁻¹ = (rho * om * rho⁻¹) * (rho * tau * rho⁻¹) := by group
      _ = om * tau := by rw [homfix, htaufix]
  constructor
  · intro hmem
    obtain ⟨hT, _⟩ := hmem
    exact ⟨(q13d_om_mem_T_iff h).mp hT, homtaufix⟩
  · intro hmem
    obtain ⟨hT, _⟩ := hmem
    exact ⟨(q13d_om_mem_T_iff h).mpr hT, homfix⟩

private theorem q13d_fix_subset_B (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    conjIn (q13L t tau x₁ x₂ rho om) t ∩ {u : G | rho * u * rho⁻¹ = u} ⊆
      ({t, t * tau, om, om * tau} : Set G) := by
  classical
  rintro u ⟨huT, hufix⟩
  obtain ⟨k, hkL, hku⟩ := huT
  have hmem : k * t * k⁻¹ ∈ t • (q13P t tau x₁ x₂ rho om : Set G) :=
    q13d_tL h hII k hkL
  rw [Set.mem_smul_set] at hmem
  obtain ⟨p, hpP, hpeq⟩ := hmem
  have hpeq' : k * t * k⁻¹ = t * p := by rw [← hpeq, smul_eq_mul]
  have hpc : rho * p * rho⁻¹ = p := by
    have h1 : rho * (t * p) * rho⁻¹ = t * p := by
      rw [← hpeq', hku]
      exact hufix
    have h2 : rho * (t * p) * rho⁻¹ = t * (rho * p * rho⁻¹) := by
      calc rho * (t * p) * rho⁻¹ = (rho * t) * p * rho⁻¹ := by group
        _ = (t * rho) * p * rho⁻¹ := by rw [(q13a_t_comm h).2.1]
        _ = t * (rho * p * rho⁻¹) := by group
    rw [h2] at h1
    exact mul_left_cancel h1
  have hpcent : p ∈ Subgroup.centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc p * rho = (rho * p * rho⁻¹) * rho := by rw [hpc]
      _ = rho * p := by group
  have hpCP : p ∈ q13P t tau x₁ x₂ rho om ⊓ Subgroup.centralizer ({rho} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hpP, hpcent⟩
  rw [q13d_CP_rho h hII] at hpCP
  have hpImg : p ∈ (Finset.range (orderOf (t * om))).image
      (fun n : ℕ => (t * om) ^ n) :=
    (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf
      (x := t * om) (isOfFinOrder_of_finite (t * om))).mp hpCP
  obtain ⟨n, hn, hpn⟩ := Finset.mem_image.mp hpImg
  have hn4 : n < 4 := by
    rw [Finset.mem_range, q13d_orderOf_gam h] at hn
    exact hn
  have hu : u = t * (t * om) ^ n := by
    rw [← hku, hpeq', hpn]
  rw [hu]
  exact q13d_t_gam_pow_mem h hn4

theorem q13d_ncard_fix_tL (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ((conjIn (q13L t tau x₁ x₂ rho om) t) ∩ {u : G | rho * u * rho⁻¹ = u}).ncard = 2 ∨
      ((conjIn (q13L t tau x₁ x₂ rho om) t) ∩ {u : G | rho * u * rho⁻¹ = u}).ncard = 4 := by
  classical
  set T : Set G := conjIn (q13L t tau x₁ x₂ rho om) t with hTdef
  set F : Set G := T ∩ {u : G | rho * u * rho⁻¹ = u} with hFdef
  have hsub : F ⊆ ({t, t * tau, om, om * tau} : Set G) := by
    rw [hFdef, hTdef]
    exact q13d_fix_subset_B h hII
  have htF : t ∈ F := by
    rw [hFdef, hTdef]
    exact q13d_t_mem_fix h
  have httauF : t * tau ∈ F := by
    rw [hFdef, hTdef]
    exact q13d_ttau_mem_fix h
  have homtau_iff : om ∈ F ↔ om * tau ∈ F := by
    rw [hFdef, hTdef]
    exact q13d_om_mem_fix_iff h
  by_cases hom : om ∈ F
  · right
    have homtau : om * tau ∈ F := homtau_iff.mp hom
    have hFB : F = ({t, t * tau, om, om * tau} : Set G) := by
      apply Set.Subset.antisymm hsub
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact htF
      · exact httauF
      · exact hom
      · exact homtau
    rw [hFB, q13d_ncard_B h]
  · left
    have homtau_nF : om * tau ∉ F := fun hc => hom (homtau_iff.mpr hc)
    have hFs : F = ({t, t * tau} : Set G) := by
      apply Set.Subset.antisymm
      · intro u hu
        have huB : u ∈ ({t, t * tau, om, om * tau} : Set G) := hsub hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huB ⊢
        rcases huB with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd hu hom
        · exact absurd hu homtau_nF
      · intro u hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
        rcases hu with rfl | rfl
        · exact htF
        · exact httauF
    rw [hFs, q13d_ncard_s h]

theorem q13d_not_three_dvd_ncard_tL (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ¬ 3 ∣ (conjIn (q13L t tau x₁ x₂ rho om) t).ncard := by
  intro h3
  have hTinv : ∀ u ∈ conjIn (q13L t tau x₁ x₂ rho om) t,
      rho * u * rho⁻¹ ∈ conjIn (q13L t tau x₁ x₂ rho om) t := by
    rintro u ⟨k, hk, rfl⟩
    exact ⟨rho * k, Subgroup.mul_mem _ (q13d_rho_norm h) hk, by group⟩
  have hmod := q13d_ncard_modEq_fixed (hr := q13a_rho_cube h) hTinv
  have hfix := q13d_ncard_fix_tL h hII
  have hFdvd : 3 ∣ ((conjIn (q13L t tau x₁ x₂ rho om) t) ∩
      {u : G | rho * u * rho⁻¹ = u}).ncard := by
    have h0 : (conjIn (q13L t tau x₁ x₂ rho om) t).ncard ≡ 0 [MOD 3] :=
      Nat.modEq_zero_iff_dvd.mpr h3
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h0)
  rcases hfix with h2 | h4
  · rw [h2] at hFdvd
    norm_num at hFdvd
  · rw [h4] at hFdvd
    norm_num at hFdvd

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
